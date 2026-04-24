(* ::Package:: *)

(* ::Title:: *)
(* Phase 4 -- computeResidues via the Rothstein-Trager double resultant *)

(* ::Text:: *)
(* See TragerPlan.md Section 6.                                              *)
(*                                                                           *)
(* Given the simple-pole remainder from Hermite reduction (AF element with  *)
(* K(z) coefficients, represented with a common K[z] denominator B), compute*)
(*                                                                           *)
(*   R(Z) = resultant_x(resultant_y(Z * B_full' - G_poly, y^n - g, y), B_full)*)
(*                                                                           *)
(* factor-by-factor, with G_poly the polynomial-in-(z, y) form of the        *)
(* remainder times B_full = B * d[n-1]. The scaling by d[n-1] clears the    *)
(* d_i denominators of the integral basis at the cost of introducing zero-  *)
(* residue places at the branch points (roots of d[n-1]); those show up as  *)
(* a Z^k factor in R which we strip.                                         *)

(* ::Section:: *)
(* computeResidues[remainder, B, basis, y, ZVar]                             *)
(*                                                                           *)
(* - remainder : AF element (phase-3 output)                                 *)
(* - B         : square-free polynomial in basis["x"] (phase-3 "D")          *)
(* - basis     : basis descriptor                                            *)
(* - y         : algebraic generator symbol                                  *)
(* - ZVar      : symbol to use for the residue variable in R(Z)              *)

ClearAll[computeResidues];

computeResidues[remainder_?afElementQ, B_, basis_?basisDescriptorQ,
                y_Symbol, ZVar_Symbol] := Module[
  {n, g, d, z, dmax, Gpoly, Bfull, Bprime, innerRes, factList,
   RZ, RCoeffs, Zstrip, Rstripped, RprimitiveLC, Rnormalized,
   rootList, distinctRes, basisInfo},

  n = basis["n"]; g = basis["g"]; d = basis["d"]; z = basis["x"];
  dmax = Last[d];                          (* d[n-1] *)

  (* Build Gpoly ∈ Q[z, y] of y-degree < n and Bfull ∈ Q[z] so that          *)
  (*   remainder = Gpoly / Bfull   (as differential form integrand)          *)
  Gpoly  = Expand[afToStandard[remainder, basis, y] * B * dmax];
  Bfull  = Expand[B * dmax];
  Bprime = D[Bfull, z];

  (* Rothstein-Trager double resultant, factored over Q for efficiency.     *)
  factList = Rest[FactorList[Bfull]];     (* {{irreducible_i, mult_i}, ...} *)
  innerRes = Resultant[ZVar * Bprime - Gpoly, y^n - g, y];

  RZ = Times @@ (Resultant[innerRes, #[[1]]^#[[2]], z] & /@ factList);
  RZ = Expand[RZ];

  (* Strip Z^k factor corresponding to zero-residue places.                 *)
  RCoeffs = CoefficientList[RZ, ZVar];
  Zstrip  = Length[TakeWhile[RCoeffs, # === 0 &]];
  Rstripped = If[Zstrip > 0, PolynomialQuotient[RZ, ZVar^Zstrip, ZVar], RZ];

  (* Normalize by dividing out the gcd of integer coefficients to keep the  *)
  (* display tidy -- the roots are unchanged.                                *)
  If[rationalPolynomialQ[Rstripped, ZVar],
    RprimitiveLC = GCD @@ Rationalize[CoefficientList[Rstripped, ZVar]];
    Rnormalized = If[RprimitiveLC =!= 0, Expand[Rstripped / RprimitiveLC], Rstripped],
    Rnormalized = Rstripped
  ];

  (* Extract distinct roots as Root objects (or rationals when they split). *)
  (* Solve returns {} when Rnormalized is a non-zero constant (all residues  *)
  (* were stripped as zero-residue places); ZVar /. {} evaluates to ZVar,   *)
  (* which breaks DeleteDuplicates. Guard explicitly.                        *)
  Module[{solveResult = Solve[Rnormalized == 0, ZVar]},
    rootList = If[solveResult === {}, {}, ZVar /. solveResult];
  ];
  distinctRes = DeleteDuplicates[rootList];

  basisInfo = residueQBasis[distinctRes];

  (* Multiplicities: for each distinct residue, find the smallest k with   *)
  (* k-th derivative of R at r nonzero — equivalently, the multiplicity   *)
  (* of r as a root of R. Used to weight the contribution of branch places *)
  (* (where ramification index appears as a multiplicity of the RT root). *)
  Module[{multiplicities},
    multiplicities = Table[
      Module[{p = Rnormalized, k = 0, val},
        val = Simplify[p /. ZVar -> r];
        While[TrueQ[val === 0] || TrueQ[zeroQ[val]],
          p = D[p, ZVar];
          k++;
          If[k > Exponent[Rnormalized, ZVar], Break[]];
          val = Simplify[p /. ZVar -> r];
        ];
        If[k === 0, 1, k]  (* defensive: every residue is a root with mult ≥ 1 *)
      ],
      {r, distinctRes}
    ];

    <|
      "R"              -> Rnormalized,
      "Rraw"           -> RZ,
      "Zstrip"         -> Zstrip,
      "residues"       -> distinctRes,
      "multiplicities" -> multiplicities,
      "qBasis"         -> basisInfo["qBasis"],
      "basisCoeffs"    -> basisInfo["basisCoeffs"]
    |>
  ]
];

(* ::Section:: *)
(* residueQBasis                                                             *)
(*                                                                           *)
(* Compute a Z-basis of the Q-vector-subspace spanned by the residues.       *)
(* Each residue is expressed as an integer-coefficient vector against the   *)
(* basis.                                                                    *)
(*                                                                           *)
(* Strategy: pick basis elements from the RESIDUES THEMSELVES (greedily in  *)
(* list order: first non-zero residue, then each subsequent residue that    *)
(* is linearly independent of the previously-picked ones). Express every   *)
(* residue as a Q-combination of the picked residues; clear column          *)
(* denominators by scaling basis elements. When residues are already        *)
(* Z-linearly related (Galois orbit with zero trace, or symmetric +/-      *)
(* pairs), the resulting coefficient matrix is naturally small-integer.    *)
(*                                                                           *)
(* This avoids the alternative "row-reduce the power basis of the number  *)
(* field" strategy which is correct but yields numerically inflated        *)
(* coefficients on Galois-orbit residue sets (e.g. the three cube roots   *)
(* of Z^3 = 1/81 produced basisCoeffs with entries in the hundreds).      *)

ClearAll[residueQBasis];
residueQBasis[residues_List] := Module[
  {allRat, nf, algEntries, gen, dim, vectors, basisIndices, basisVectors,
   coeffs, denomLCMs, scaledCoeffs, scaledBasis},

  (* Empty residue list: return trivial basis.                               *)
  If[residues === {},
    Return[<|"qBasis" -> {}, "basisCoeffs" -> {}|>]
  ];

  (* Trivial case: residues all rational -- span is Q. Scale the basis so   *)
  (* coefficients become integers.                                           *)
  allRat = AllTrue[residues, Element[#, Rationals] &];
  If[allRat,
    Module[{denomLCM, scaledResidues},
      denomLCM = LCM @@ (Denominator /@ residues);
      scaledResidues = residues * denomLCM;
      Return[<|
        "qBasis"      -> {1/denomLCM},
        "basisCoeffs" -> ({#} & /@ scaledResidues)
      |>]
    ]
  ];

  (* Reduce to a common number field via ToNumberField.                     *)
  (* ToNumberField expresses each input either as AlgebraicNumber[gen, c]   *)
  (* or -- for rational inputs -- as the bare rational. We unify by padding *)
  (* rationals with zeros in the power-basis representation.                 *)
  nf = Quiet @ Check[ToNumberField[residues], $Failed];
  If[nf === $Failed,
    Return[<|
      "qBasis" -> residues,
      "basisCoeffs" -> IdentityMatrix[Length[residues]]
    |>]
  ];
  algEntries = Cases[nf, AlgebraicNumber[_, _]];
  If[algEntries === {},
    Return[<|"qBasis" -> {1}, "basisCoeffs" -> ({#} & /@ residues)|>]
  ];
  gen = First[algEntries][[1]];
  dim = Length[First[algEntries][[2]]];
  vectors = nf /. {
    AlgebraicNumber[_, c_] :> c,
    r_ /; Element[r, Rationals] :> PadRight[{r}, dim]
  };

  (* Pick basis residues greedily: iterate in list order, add each residue *)
  (* whose inclusion increases the rank of the accumulated basis.         *)
  basisIndices = {};
  basisVectors = {};
  Module[{currentRank = 0, newRank, testMat},
    Do[
      If[AllTrue[vectors[[i]], zeroQ], Continue[]];
      testMat = Append[basisVectors, vectors[[i]]];
      newRank = MatrixRank[testMat];
      If[newRank > currentRank,
        AppendTo[basisIndices, i];
        AppendTo[basisVectors, vectors[[i]]];
        currentRank = newRank
      ],
      {i, Length[vectors]}
    ]
  ];

  If[basisIndices === {},
    Return[<|
      "qBasis"      -> {},
      "basisCoeffs" -> ConstantArray[0, {Length[residues], 0}]
    |>]
  ];

  (* Express each residue as a Q-linear combination of the picked basis    *)
  (* residues. Transpose[basisVectors] has columns = basis-residue vectors *)
  (* in the number-field power basis; LinearSolve returns the coefficient *)
  (* vector c with basisVectors^T . c = vectors[[j]].                     *)
  coeffs = Quiet @ Check[
    Table[
      LinearSolve[Transpose[basisVectors], vectors[[j]]],
      {j, Length[vectors]}
    ],
    $Failed
  ];
  If[coeffs === $Failed,
    Return[<|
      "qBasis"      -> residues,
      "basisCoeffs" -> IdentityMatrix[Length[residues]]
    |>]
  ];

  (* Clear column denominators: scale each basis residue down by the LCM    *)
  (* of denominators in its column, so the coefficient matrix is integer.   *)
  denomLCMs = Table[
    LCM @@ (Denominator /@ coeffs[[All, i]]),
    {i, Length[basisIndices]}
  ];
  scaledCoeffs = Table[
    coeffs[[j, i]] * denomLCMs[[i]],
    {j, Length[coeffs]}, {i, Length[basisIndices]}
  ];
  scaledBasis = Table[
    residues[[basisIndices[[i]]]] / denomLCMs[[i]],
    {i, Length[basisIndices]}
  ];

  <|"qBasis" -> scaledBasis, "basisCoeffs" -> scaledCoeffs|>
];

(* Elementary row reduction returning the reduced rows and pivot columns.   *)
(* Pivots are identified by the first non-zero entry in each non-zero row.  *)

ClearAll[reduceRowsOverQ];
reduceRowsOverQ[vectors_List] := Module[{rr, pivots},
  rr = RowReduce[vectors];
  pivots = SelectFirst[
              Range[Length[#]],
              Function[i, #[[i]] =!= 0],
              Missing[]
            ] & /@ rr;
  pivots = Select[pivots, !MissingQ[#] &];
  {rr, pivots}
];

(* Express a target row as a Q-linear combination of the basis rows by     *)
(* reading the pivot-column entries directly -- because basis rows are row-*)
(* reduced, the target's pivot-column entries ARE its basis coefficients.  *)
ClearAll[solveRowCoeffs];
solveRowCoeffs[target_List, basisRows_List, pivotCols_List] :=
  target[[#]] & /@ pivotCols;
