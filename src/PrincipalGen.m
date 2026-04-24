(* ::Package:: *)

(* ::Title:: *)
(* Principal-generator construction (Phase 5, revised per TragerPlan §17) *)

(* ::Text:: *)
(* Given a divisor D = (h, A) of degree 0, find an AF element v with     *)
(* (v) = D. Two-step reduction (Trager 1984 Ch 6 §1 "Principal Divisors"  *)
(* combined with the Ch 2 §3 normalize-at-infinity step):                 *)
(*                                                                         *)
(* Step A. Build the 2n × n matrix M whose rows are the w_j-coordinates of*)
(*         {w_i · h : i = 0..n-1} ∪ {w_i · A : i = 0..n-1} — a generating *)
(* set for I_D over K[z]. Clear column denominators into L[j], apply     *)
(* hermiteNormalFormOverKz, take the top n × n block, divide columns     *)
(* back by L[j]. The result is a K[z]-basis of I_D.                     *)
(*                                                                         *)
(* Step B. Apply normalizeAtInfinity to kill Q-linear dependencies of   *)
(* leading-at-infinity coefficients.                                      *)
(*                                                                         *)
(* Step C. Scan for a row whose AF element is integral at infinity       *)
(* (noPoleAtInfinityRowQ). In genus 0, exactly one such row exists up to *)
(* a K[z]-unit (a nonzero rational number); it is the principal          *)
(* generator v of D.                                                       *)
(*                                                                         *)
(* The legacy single-phase "polynomial HNF + scan" flow from the first   *)
(* port of this file is superseded; see trager_status.md §2.8 for the   *)
(* history. See TragerPlan.md §17 for the specification of the revised  *)
(* algorithm.                                                             *)

(* ::Section:: *)
(* i-th basis element as AF                                                 *)

ClearAll[afBasisElement];
afBasisElement[i_Integer, basis_?basisDescriptorQ] :=
  afMake[UnitVector[basis["n"], i + 1], basis];

(* ::Section:: *)
(* Column-denominator clearing                                              *)
(*                                                                           *)
(* Given a matrix with K(z)-entries, return {scaled matrix, L} where      *)
(* scaled[[all, j]] = M[[all, j]] · L[[j]] has polynomial entries, and    *)
(* L[[j]] is PolynomialLCM of the denominators in column j.                *)

ClearAll[clearColumnDenominators];
clearColumnDenominators[M_List, z_Symbol] := Module[
  {nrows, ncols, cols, dens, lcms, scaled},
  nrows = Length[M];
  ncols = Length[First[M]];
  cols  = Table[M[[All, j]], {j, ncols}];
  lcms  = Table[
    Module[{ds = Denominator[Together[#]] & /@ cols[[j]]},
      PolynomialLCM @@ ds
    ],
    {j, ncols}
  ];
  scaled = Table[
    Table[Expand[M[[i, j]] * lcms[[j]]], {j, ncols}],
    {i, nrows}
  ];
  <|"scaled" -> scaled, "denominators" -> lcms|>
];

(* ::Section:: *)
(* findPrincipalGenerator                                                   *)

(* findPrincipalGenerator returns an AF element satisfying div(v) == D, or    *)
(* a Failure. Optional Verify -> fn is called on each candidate row; the     *)
(* first row for which fn returns True is returned. fn may also return       *)
(* $Unknown, in which case the row is treated as a tentative pass — reported *)
(* with a tentative flag to the caller (currently we return it but prefer   *)
(* rows with confirmed True).                                                 *)
(*                                                                           *)
(* Default Verify -> None is backward-compatible: any integral-at-infinity  *)
(* row is returned. This is correct in genus 0 (L(−D) is 1-dim), but in     *)
(* higher genus a verification function is required to rule out spurious    *)
(* integral-at-infinity rows whose divisor is NOT D.                         *)

ClearAll[findPrincipalGenerator];
Options[findPrincipalGenerator] = {Verify -> None};
findPrincipalGenerator[div_?divisorQ, basis_?basisDescriptorQ,
                       y_Symbol, OptionsPattern[]] := Catch[Module[
  {h, A, n, z, wTimesH, wTimesA, matrix, cleared, hnf, topN, ext,
   restored, normalized, finalM, candidateRows, verifyFn,
   verifiedRow, tentativeRow, chosenRow, vCand, vResult, i},

  h = div["h"];
  A = div["A"];
  n = basis["n"];
  z = basis["x"];
  verifyFn = OptionValue[Verify];

  (* 2n generators of I_D viewed as AF elements. *)
  wTimesH = Table[afTimes[afBasisElement[i, basis], h, basis], {i, 0, n - 1}];
  wTimesA = Table[afMake[A * UnitVector[n, i + 1], basis], {i, 0, n - 1}];

  matrix = Join[
    #["Coeffs"] & /@ wTimesH,
    #["Coeffs"] & /@ wTimesA
  ];

  (* Step A.1 — Clear column denominators. *)
  cleared = clearColumnDenominators[matrix, z];

  (* Detect the algebraic extension required for K[z]-arithmetic.          *)
  (* Residues and their derived divisors may carry Root[]/AlgebraicNumber *)
  (* generators; working over ℚ(ext) instead of ℚ lets the HNF see that   *)
  (* polynomials like x³-1 split further after the residues' splitting    *)
  (* field is adjoined. Scanning the divisor's own coordinates suffices — *)
  (* any generator needed downstream appears there after Phase-4 Qlist    *)
  (* construction.                                                          *)
  ext = detectExtensionGenerators[{h["Coeffs"], A}];

  (* Step A.2 — Polynomial K[z]-Hermite Normal Form. *)
  hnf = hermiteNormalFormOverKz[cleared["scaled"], z, ext];

  (* Step A.3 — Top n × n block. *)
  topN = Take[hnf, n];

  (* Step A.4 — Divide each column j by L[j] to return to K(z). *)
  restored = Table[
    Table[
      Together[topN[[i, j]] / cleared["denominators"][[j]]],
      {j, n}
    ],
    {i, n}
  ];

  (* Step B — normalizeAtInfinity on the n × n matrix of K(z) entries. *)
  normalized = normalizeAtInfinity[restored, basis];
  finalM     = normalized["matrix"];

  (* Step C — collect candidate rows (integral at infinity, nonzero). *)
  candidateRows = Select[finalM,
    !AllTrue[#, zeroQ] && noPoleAtInfinityRowQ[#, basis] &
  ];

  If[candidateRows === {},
    Throw[incompleteFailure["NonPrincipalDivisor",
      "Divisor"   -> div,
      "Reason"    -> "no integral-at-infinity row after HNF + normalizeAtInfinity",
      "Matrix"    -> finalM,
      "ScaledKs"  -> normalized["ks"],
      "Iterations" -> normalized["iterations"],
      "SuggestedFix" -> "if genus > 0, torsionIfCan will retry with k·D for k ≥ 2"]]
  ];

  (* If no verification requested, return first candidate as before. *)
  If[verifyFn === None,
    Throw[afMake[First[candidateRows], basis]]
  ];

  (* With verification: scan rows, prefer a confirmed True over $Unknown.    *)
  verifiedRow  = None;
  tentativeRow = None;
  Do[
    vCand   = afMake[candidateRows[[i]], basis];
    vResult = verifyFn[vCand];
    Which[
      vResult === True,
        verifiedRow = vCand; Break[],
      vResult === $Unknown && tentativeRow === None,
        tentativeRow = vCand,
      True, Null (* False or other — skip *)
    ],
    {i, Length[candidateRows]}
  ];

  Which[
    verifiedRow =!= None,  verifiedRow,
    tentativeRow =!= None, tentativeRow,
    True,
      incompleteFailure["NonPrincipalDivisor",
        "Divisor"   -> div,
        "Reason"    -> "no integral-at-infinity row passed the verifier; \
divisor is likely not principal at this torsion level",
        "CandidateCount" -> Length[candidateRows],
        "SuggestedFix"   -> "retry with a larger k in torsionIfCan, or accept \
NonElementary if the bound is exhausted"]
  ]
]];
