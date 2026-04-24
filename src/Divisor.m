(* ::Package:: *)

(* ::Title:: *)
(* Divisor representation and arithmetic *)

(* ::Text:: *)
(* Trager 1984 Ch 5 §3 ("Constructing Divisors").                            *)
(*                                                                           *)
(* A divisor D on the curve y^n = g(x) is represented LOCALLY-PRINCIPALLY  *)
(*     D ~ (h, A)    h : AF element, A : polynomial in x                   *)
(* with the invariant                                                        *)
(*                                                                           *)
(*   ord_P(h) = ord_P(D)   at every place P lying over a root of A         *)
(*   ord_P(D) = 0          at every place P not over a root of A.           *)
(*                                                                           *)
(* h may have additional zeros/poles at places not over A; those are        *)
(* irrelevant to the abstract divisor D.                                    *)
(*                                                                           *)
(* In our Phase-5 application every residue divisor has support over roots  *)
(* of the SAME polynomial A (the square-free Hermite remainder denominator),*)
(* so divisor addition collapses to the simple case A1 = A2.                *)

(* ::Section:: *)
(* Constructors *)

ClearAll[makeDivisor];
makeDivisor[h_?afElementQ, A_] := <|
  "Type" -> "Divisor",
  "h"    -> h,
  "A"    -> Together[A]
|>;

(* ::Section:: *)
(* Residue divisor from Phase-4 data                                        *)
(*                                                                           *)
(* Given the simple-pole remainder G(x, y)/D(x) from Hermite and a residue  *)
(* alpha associated to one of the roots of D, the residue divisor (Trager  *)
(* 1984 Ch 5 §3) is represented locally as                                  *)
(*                                                                           *)
(*   h := G - alpha * D'                                                   *)
(*   A := D                                                                 *)
(*                                                                           *)
(* At a place (beta, y_beta) over a root beta of D where the residue of f  *)
(* equals alpha, we have G(beta, y_beta) = alpha D'(beta), so h vanishes   *)
(* there (to order = 1 for simple residues, higher order for a cluster).   *)
(* At other places over roots of D (same beta, different y_beta value), h  *)
(* does not vanish, so ord_P(h) = 0 there.                                  *)

(* Simplify an AF element h modulo an ideal polynomial A.                   *)
(*   1. Let d = lcm of denominators of h's integral-basis coefficients.   *)
(*   2. Each numerator n_i = c_i · d is in K[x].                          *)
(*   3. Replace n_i with Rem(n_i, A·d, x) — polynomial remainder.         *)
(*   4. Reassemble h_simplified = (Σ n_i · w_i) / d.                      *)
(* Rationale: the locally-principal model (h, A) only constrains h at     *)
(* places over roots of A. h may carry spurious divisor contributions at  *)
(* OTHER places (zeros/poles of the denominator of h, zeros of h itself   *)
(* off supp(A), etc.). These contaminations propagate into I_D = h·O +    *)
(* A·O and are the direct cause of "spurious" pole-free-at-infinity       *)
(* elements that are not the principal generator. Reducing h's numerators *)
(* modulo (A·d) kills this contamination while preserving the behavior of *)
(* h at every place over a root of A (where the (h,A) invariant matters). *)

(* Scale h by the "coprime-to-A" part of its common denominator, so that  *)
(* h's denominator divides some power of A. This ensures the K[z]-module  *)
(* K[z]·h + K[z]·A has no spurious "poles" at places not over supp(A),    *)
(* which is otherwise introduced when divisor arithmetic (multiplication, *)
(* inversion) produces AF elements whose coefficient denominators have    *)
(* factors coprime to A.                                                   *)
(*                                                                           *)
(* Iteratively factor out the part of the common denominator that is       *)
(* coprime to A: while gcd(den(h), A) ≠ den(h), accumulate the gcd into a  *)
(* multiplier d, then divide once more.                                     *)
(*                                                                           *)
(* Mathematical justification: multiplying h by a polynomial c coprime to *)
(* A is a unit at every place over every root of A, so it preserves the    *)
(* orders that define the divisor in the locally-principal (h, A) model.  *)
(* At places NOT over roots of A, where the abstract divisor has order 0,  *)
(* h·c may have a nonzero order but the K[z]-module K[z]·(h·c) + K[z]·A   *)
(* becomes the correct ideal sheaf because c has cleared any denominators *)
(* that were creating spurious poles.                                      *)

ClearAll[simplifyHDenominator];
simplifyHDenominator[h_?afElementQ, A_, basis_?basisDescriptorQ] := Module[
  {x, coeffs, dens, d, dCoprime, gPoly, remaining, newCoeffs},
  x      = basis["x"];
  coeffs = h["Coeffs"];
  dens   = Denominator[Together[#]] & /@ coeffs;
  d      = PolynomialLCM @@ dens;
  (* Iteratively remove the A-supported part of d.                            *)
  (* PolynomialGCD needs Extension -> Automatic because h coefficients may   *)
  (* carry algebraic numbers from Phase-4 residues (Trager Ch 5 §3); without *)
  (* it the gcd over ℚ misses the shared factors that only appear over ℚ(α). *)
  (* PolynomialQuotient/Remainder already handle algebraic-number            *)
  (* coefficients natively (no Extension option needed / accepted).           *)
  remaining = d;
  gPoly = PolynomialGCD[remaining, A, Extension -> Automatic];
  While[Exponent[gPoly, x] > 0,
    remaining = PolynomialQuotient[remaining, gPoly, x];
    gPoly     = PolynomialGCD[remaining, A, Extension -> Automatic];
  ];
  dCoprime = remaining;
  If[Exponent[dCoprime, x] <= 0,
    h,
    (* Multiply each AF coefficient by dCoprime. *)
    newCoeffs = Table[Together[coeffs[[i]] * dCoprime], {i, Length[coeffs]}];
    afMake[newCoeffs, basis]
  ]
];

ClearAll[simplifyHModA];
simplifyHModA[h_?afElementQ, A_, basis_?basisDescriptorQ] := Module[
  {x, coeffs, dens, d, nums, reduced, newCoeffs, r, simplifiedAF},
  x      = basis["x"];
  coeffs = h["Coeffs"];
  dens   = Denominator[Together[#]] & /@ coeffs;
  d      = PolynomialLCM @@ dens;
  nums   = Table[
    Expand[coeffs[[i]] * d],
    {i, Length[coeffs]}
  ];
  r = Expand[A * d];
  (* PolynomialRemainder already handles algebraic-number coefficients       *)
  (* natively when ℚ(α) is the coefficient field — no Extension option is    *)
  (* needed (nor accepted by PolynomialRemainder).                            *)
  reduced = Table[
    PolynomialRemainder[Expand[nums[[i]]], r, x],
    {i, Length[nums]}
  ];
  newCoeffs = Table[Together[reduced[[i]] / d], {i, Length[reduced]}];
  afMake[newCoeffs, basis]
];

(* "Lucky integer" reduction (Trager 1984 Ch 5 §3).                         *)
(*                                                                           *)
(* Given an AF element h with "correct" divisor behavior at places over     *)
(* roots of D1 (the support polynomial) but possible stray zeros/poles     *)
(* over roots of DD \ D1, find an integer j such that h + j·D1 has no      *)
(* stray DD-support. Adding a multiple of D1 preserves h's behavior on     *)
(* supp(D1) (since D1 vanishes there) while generically killing zeros     *)
(* elsewhere.                                                                *)
(*                                                                           *)
(* Success criterion: extract all DD-factors from Norm(h + j·D1) by iterated*)
(* GCD; the accumulated product N1 should have degree exactly malpha in x. *)
(* malpha is the residue multiplicity (1 for simple residues).             *)

ClearAll[reduceH];
Options[reduceH] = {MaxJ -> 32};
reduceH[h_?afElementQ, D1_, DD_, malpha_Integer,
        basis_?basisDescriptorQ, y_Symbol,
        OptionsPattern[]] := Catch[Module[
  {j, hAdj, coeffs, normVal, N0, Ncur, N1, gPoly, x, maxJ, allZero},

  x     = basis["x"];
  maxJ  = OptionValue[MaxJ];

  (* Empty h: divisor is trivial; nothing to reduce. *)
  allZero = AllTrue[h["Coeffs"], TrueQ[Together[#] === 0] &];
  If[allZero, Throw[h]];

  Do[
    hAdj = If[j === 0,
      h,
      (coeffs = h["Coeffs"];
       coeffs[[1]] = Together[coeffs[[1]] + j * D1];
       afMake[coeffs, basis])
    ];
    normVal = afNorm[hAdj, basis];
    N0      = Numerator[Together[normVal]];
    Ncur    = N0;
    N1      = 1;
    (* Iteratively strip DD-factors from Ncur, accumulating into N1.         *)
    (* PolynomialGCD needs Extension -> Automatic: when α is algebraic the   *)
    (* norm carries α-dependent coefficients and the gcd over ℚ would miss   *)
    (* the shared factor with DD.                                             *)
    gPoly = PolynomialGCD[Ncur, DD, Extension -> Automatic];
    While[Exponent[gPoly, x] > 0,
      N1    = Expand[N1 * gPoly];
      Ncur  = PolynomialQuotient[Ncur, gPoly, x];
      gPoly = PolynomialGCD[Ncur, DD, Extension -> Automatic];
    ];
    If[Exponent[N1, x] === malpha, Throw[hAdj]],
    {j, 0, maxJ}
  ];

  Throw[incompleteFailure["ReduceLuckyIntegerMaxIter",
    "MaxJ"       -> maxJ,
    "h"          -> h,
    "D1"         -> D1,
    "DD"         -> DD,
    "malpha"     -> malpha,
    "Reason"     -> "no integer j in [0, MaxJ] produced Norm(h + j·D1) \
with the expected DD-part degree = malpha. Either malpha is wrong, the \
divisor is not locally principal in this form, or the search bound is \
too small."]]
]];

(* Residue divisor construction with branch / non-branch separation         *)
(* (Trager 1984 Ch 5 §3 + §4 "Dealing with Branch Places").                 *)
(*                                                                           *)
(*   h1 = G − α·D'                    (raw locally-principal generator)     *)
(*   N  = numer(Norm(h1))                                                    *)
(*   D1 = gcd(N, Dpoly)                (actual x-projection of supp(h1) ∩    *)
(*                                      supp(Dpoly))                         *)
(*   D3 = gcd(D1, Disc)                (branch part: supp(D1) ∩ branch locus)*)
(*   D2 = D1/D3                        (non-branch part)                     *)
(*                                                                           *)
(* For the non-branch component: apply `simplify` then `reduce` to h1.     *)
(* For the branch component: apply `simplify`, raise to n-th power         *)
(* (ramification index = n at each branch place for a simple radical       *)
(* y^n = g), `simplify` again, then `reduce`.                              *)
(*                                                                           *)
(* The returned divisor keeps A = Dpoly (the original full denominator)     *)
(* rather than D1 so that pairs of residue divisors (for α and −α, etc.)   *)
(* share a common A and can be combined via divisorAdd/Subtract. The       *)
(* representation is mathematically equivalent: at places over roots of   *)
(* Dpoly \ D1, h (= h2·h3) has order 0 by construction of D1 as the       *)
(* x-projection of supp(Norm(h1)) ∩ supp(Dpoly).                          *)

ClearAll[residueDivisor];
Options[residueDivisor] = {Multiplicity -> 1};
residueDivisor[GtildeAF_?afElementQ, Dpoly_, alpha_,
               basis_?basisDescriptorQ, y_Symbol,
               OptionsPattern[]] := Module[
  {x, n, g, Dprime, DprimeAF, alphaAF, h1,
   normVal, N0, D1, Disc, D3, D2, h2, h3,
   h3start, hCombined, malpha},

  x      = basis["x"];
  n      = basis["n"];
  g      = basis["g"];
  malpha = OptionValue[Multiplicity];

  Dprime   = D[Dpoly, x];
  DprimeAF = afFromStandard[Dprime, basis, y];
  alphaAF  = afFromStandard[alpha, basis, y];

  (* h1 = G − α·D' as an AF element (Trager Ch 5 §3). *)
  h1 = afMinus[
    GtildeAF,
    afTimes[alphaAF, DprimeAF, basis],
    basis
  ];

  (* Compute the actual x-projection of supp(h1) intersected with supp(Dpoly). *)
  normVal = afNorm[h1, basis];
  N0      = Numerator[Together[normVal]];
  (* Extension -> Automatic: when the residue α is algebraic (e.g. a root of *)
  (* an irreducible factor of R(Z) of degree ≥ 2, as on a genus-1 curve with *)
  (* multiple Galois orbits of residues) the norm N0 carries α-dependent     *)
  (* coefficients. GCD over ℚ then fails to see the shared factor — D1 = 1 — *)
  (* and the residue divisor silently collapses to the trivial one (h = 1).  *)
  (* Enabling the extension lets Mathematica lift to ℚ(α)[x] automatically.  *)
  D1      = PolynomialGCD[N0, Dpoly, Extension -> Automatic];

  (* Degenerate: h1's norm has no support over Dpoly (residue does not     *)
  (* actually occur here). Return a trivial divisor.                       *)
  If[Exponent[D1, x] <= 0,
    Return[makeDivisor[afFromStandard[1, basis, y], Dpoly]]
  ];

  (* Branch locus for y^n = g(x): the squarefree part of g (roots of g are*)
  (* branch points). FactorList returns {{c, 1}, {p_i, e_i}, ...}; Rest   *)
  (* drops the leading constant, First /@ extracts the irreducible factor,*)
  (* and the product over those factors is the squarefree part.          *)
  Disc = Times @@ (First /@ Rest[FactorList[g]]);
  D3   = PolynomialGCD[D1, Disc, Extension -> Automatic];
  D2 = If[Exponent[D3, x] > 0,
         PolynomialQuotient[D1, D3, x],
         D1];

  (* Non-branch component: simplify + reduce on D2. *)
  h2 = If[Exponent[D2, x] > 0,
    Module[{h},
      h = simplifyHModA[h1, D2, basis];
      reduceH[h, D2, Dpoly, malpha, basis, y]
    ],
    afFromStandard[1, basis, y]
  ];
  If[tragerFailureQ[h2], Return[h2]];

  (* Branch component: simplify, raise to n-th power, simplify, reduce.    *)
  h3 = If[Exponent[D3, x] > 0,
    Module[{h},
      h3start = simplifyHModA[h1, D3, basis];
      h = h3start;
      Do[h = afTimes[h, h3start, basis], {n - 1}];
      h = simplifyHModA[h, D3, basis];
      reduceH[h, D3, Dpoly, malpha, basis, y]
    ],
    afFromStandard[1, basis, y]
  ];
  If[tragerFailureQ[h3], Return[h3]];

  hCombined = afTimes[h2, h3, basis];

  (* Clear any denominator factor coprime to A so that h's denom lies     *)
  (* entirely in supp(A). Otherwise the K[z]-module K[z]·h + K[z]·A      *)
  (* would contain AF elements with spurious poles at places outside      *)
  (* supp(A), and findPrincipalGenerator would return a wrong generator. *)
  hCombined = simplifyHDenominator[hCombined, Dpoly, basis];

  (* Final canonicalization mod Dpoly's denominator lcm, so the chosen    *)
  (* representative in each K[z]-coset is the small-degree one.           *)
  hCombined = simplifyHModA[hCombined, Dpoly, basis];

  makeDivisor[hCombined, Dpoly]
];

(* ::Section:: *)
(* Arithmetic                                                                *)

(* All of the following assume that the divisors share the same A, which is *)
(* the situation for Phase-5 residue divisors. A more general gcd-aware    *)
(* merge is deferred (not needed for the simple-radical scope).             *)

(* divisorAdd: correct O-ideal multiplication.                              *)
(*                                                                           *)
(* The locally-principal representation of D is (h, A): ord_P(h) = ord_P(D) *)
(* at every P over a root of A. For the ADDITION D_1 + D_2, the correct    *)
(* K[z]-module representation is (h_1·h_2, A_1·A_2), NOT (h_1·h_2, A_1)    *)
(* even when A_1 = A_2.                                                    *)
(*                                                                           *)
(* Reason: the K[z]-module I_D = (h, A)·O has ord_P(elt) ≥ min(ord(h),    *)
(* ord(A)) at each place P. For D principal with simple support, this gives *)
(* the correct ideal. But for k·D (e.g. squaring to build 2·D), with h_new *)
(* = h² and A_new = A, the min at positive-support places becomes min(2,1) *)
(* = 1 rather than the required 2. Candidates from HNF on this too-large  *)
(* module then carry spurious zeros that the verifier correctly rejects.  *)
(* Using A_new = A_1·A_2 ensures ord(A^k) = k at supp places, so the min *)
(* agrees with ord(k·D) for simple-multiplicity support.                   *)
(*                                                                           *)
(* The A-side accumulates multiplicatively when summing divisors: A_new = *)
(* A_1·A_2 (since the support of D_1 + D_2 is contained in V(A_1·A_2)).    *)

(* stripContent: divide a polynomial by the integer GCD of its coefficients.*)
(* The root set is unchanged, so using `A/content` in place of `A` doesn't *)
(* alter the K[z]-module (h, A)·O or the PolynomialRemainder semantics of *)
(* simplifyHModA — but it keeps intermediate integer magnitudes bounded.   *)
(* Crucial for torsion-order searches, where A^k otherwise grows as        *)
(* (content(A))^k, producing 200+ digit coefficients by k = 4.             *)

ClearAll[stripIntegerContent];
stripIntegerContent[p_] := Module[{ftl, content},
  ftl = Quiet @ FactorTermsList[Expand[p]];
  content = ftl[[1]];
  If[TrueQ[content === 0] || TrueQ[content === 1] || !NumberQ[content],
    p,
    Expand[p / content]
  ]
];

ClearAll[divisorAdd];
divisorAdd[d1_?divisorQ, d2_?divisorQ, basis_?basisDescriptorQ] := Module[
  {ANew, hProd},
  ANew = stripIntegerContent[d1["A"] * d2["A"]];
  hProd = afTimes[d1["h"], d2["h"], basis];
  hProd = simplifyHDenominator[hProd, ANew, basis];
  hProd = simplifyHModA[hProd, ANew, basis];
  makeDivisor[hProd, ANew]
];

ClearAll[divisorNegate];
divisorNegate[d_?divisorQ, basis_?basisDescriptorQ] := Module[{hInv},
  hInv = afInverse[d["h"], basis];
  hInv = simplifyHDenominator[hInv, d["A"], basis];
  hInv = simplifyHModA[hInv, d["A"], basis];
  makeDivisor[hInv, d["A"]]
];

ClearAll[divisorSubtract];
divisorSubtract[d1_?divisorQ, d2_?divisorQ, basis_?basisDescriptorQ] :=
  divisorAdd[d1, divisorNegate[d2, basis], basis];

ClearAll[divisorScale];
divisorScale[k_Integer, d_?divisorQ, basis_?basisDescriptorQ] := Module[
  {h = d["h"], A, hResult, AResult},
  Which[
    k === 0,
      (* Zero divisor: h=1, A=1 so invariants are trivial. *)
      makeDivisor[afFromStandard[1, basis, Symbol["y"]], 1],
    k > 0,
      A = d["A"];
      hResult = h;
      AResult = A;
      Do[
        hResult = afTimes[hResult, h, basis];
        AResult = stripIntegerContent[AResult * A],
        {k - 1}
      ];
      (* Canonicalise hResult modulo AResult to keep degrees bounded.       *)
      hResult = simplifyHDenominator[hResult, AResult, basis];
      hResult = simplifyHModA[hResult, AResult, basis];
      makeDivisor[hResult, AResult],
    k < 0,
      divisorScale[-k, divisorNegate[d, basis], basis]
  ]
];

(* ::Section:: *)
(* Zero / principal checks at the representation level                      *)
(*                                                                           *)
(* These are necessarily conservative: a divisor (h, A) represents the zero *)
(* divisor iff h is a unit at every place over every root of A. We cannot  *)
(* always decide this efficiently, so we return True / False / Indet.      *)

ClearAll[divisorIsTriviallyZeroQ];
divisorIsTriviallyZeroQ[d_?divisorQ] :=
  (* Shortcut: A=1 means support is empty, divisor is zero. *)
  TrueQ[Together[d["A"] - 1] === 0];
