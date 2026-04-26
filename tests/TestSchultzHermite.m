(* ::Package:: *)

(* ::Title:: *)
(* Tests for the Schultz §4.3 infinity-aware Hermite reduction (§S.3). *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

(* Round-trip helper, identical in spirit to TestHermite.m: any decomposition *)
(*   ω = d(algPart) + remainder                                                *)
(* must hold in the AF ring.                                                    *)

schultzRoundTripOK[integrand_, basis_?basisDescriptorQ, y_Symbol,
                   r_Association] := Module[
  {dAlg, sum, origAF, diff},
  dAlg = afD[r["algPart"], basis];
  sum = afPlus[dAlg, r["remainder"], basis];
  origAF = rationalizeToAF[integrand, basis, y];
  diff = afMinus[sum, origAF, basis];
  AllTrue[diff["Coeffs"], TrueQ[Together[#] === 0] &]
];

(* Compare two AF coefficient lists modulo Together. *)
afCoeffsEqualQ[a_List, b_List] :=
  Length[a] === Length[b] &&
  AllTrue[Range[Length[a]],
    TrueQ[Together[a[[#]] - b[[#]]] === 0] &
  ];

tsection["integralBasisDerivativeMatrix: shape and diagonal entries"];

Module[{basis, M},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  M = integralBasisDerivativeMatrix[basis];
  tassertEqual["M is 2×2", {2, 2}, Dimensions[M]];
  tassertEqual["M[1,1] = 0 (η_0 = 1 has trivial derivative)",
    0, Together[M[[1, 1]]]];
  (* M[2,2] = (2-1)·g'·d_{n-1} − n·g·(d_{n-1}/d_1)·d_1' *)
  (*        = g' (since d_0 = d_1 = 1 here)              *)
  tassertEqual["M[2,2] = g' = 2x", 2 x, Together[M[[2, 2]]]];
  tassertEqual["M[1,2] = 0 (off-diagonal zero for diagonal basis)",
    0, Together[M[[1, 2]]]];
  tassertEqual["M[2,1] = 0 (off-diagonal zero for diagonal basis)",
    0, Together[M[[2, 1]]]];
];

Module[{basis, M},
  basis = buildIntegralBasis[3, x, x];
  M = integralBasisDerivativeMatrix[basis];
  (* For y^3 = x: d_0 = 1, d_1 = 1, d_2 = 1. E = 3·x·1 = 3x. *)
  (* M[i, i] = (i-1)·g'·d_{n-1} − n·g·(d_{n-1}/d_{i-1})·d_{i-1}'  *)
  (* M[1,1] = 0·1·1 − 3·x·1·0 = 0                                *)
  (* M[2,2] = 1·1·1 − 3·x·1·0 = 1                                *)
  (* M[3,3] = 2·1·1 − 3·x·1·0 = 2                                *)
  tassertEqual["M[1,1] = 0 for y^3=x", 0, Together[M[[1, 1]]]];
  tassertEqual["M[2,2] = 1 for y^3=x", 1, Together[M[[2, 2]]]];
  tassertEqual["M[3,3] = 2 for y^3=x", 2, Together[M[[3, 3]]]];
];

tsection["schultzInfinityNeedsReductionQ / schultzInfinityBudget"];

Module[{basis, deltas},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  deltas = basis["deltas"];
  (* For y^2 = x^2+1, m=2, n=2, gcd=2. δ_0 = 0, δ_1 = max(0, 1-0) = 1. *)
  tassertEqual["deltas for y^2 = x^2+1 are {0, 1}", {0, 1}, deltas];
  (* Acoeffs = {0, 1} (i.e. integrand y), b = 1: deg(a_1)+δ_1 = 0+1 = 1 ≥ 0. *)
  tassert["needs reduction at infinity for ∫ y dx",
    schultzInfinityNeedsReductionQ[{0, 1}, 1, deltas, x]];
  (* Acoeffs = {1, 0} (integrand 1), b = 1: deg(a_0)+δ_0 = 0+0 ≥ 0. *)
  tassert["needs reduction at infinity for ∫ 1 dx",
    schultzInfinityNeedsReductionQ[{1, 0}, 1, deltas, x]];
  (* Acoeffs = {0, 1}, b = x^2+1: deg(a_1)+δ_1 = 0+1 = 1 < 2 ⇒ no reduction. *)
  tassert["no reduction needed for y/(x^2+1) integrand",
    !schultzInfinityNeedsReductionQ[{0, 1}, x^2 + 1, deltas, x]];
];

Module[{basis, deltas, N0},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  deltas = basis["deltas"];
  N0 = schultzInfinityBudget[{0, 1}, 1, deltas, x];
  (* N = max_i(deg(a_i) + δ_i + 1 − deg(b)). For ∫ y dx: max(-∞+0+1, 0+1+1, 0)*)
  (* = 2.                                                                      *)
  tassertEqual["budget N for ∫ y dx is 2", 2, N0];
];

tsection["schultzHermiteReduce: agreement with hermiteReduce on finite-only inputs"];

(* For inputs whose denominator does NOT have the integrand-at-infinity issue *)
(* (i.e. deg(a_i) + δ_i < deg(b) holds at termination), schultzHermiteReduce  *)
(* should agree with hermiteReduce term-for-term: same algPart, same          *)
(* remainder. The acceptance is identity of AF coefficients after Together.   *)

Module[{basis, rH, rS},
  basis = buildIntegralBasis[2, 1 + x^2, x];
  rH = hermiteReduce[1/(x^2*y), basis, y];
  rS = schultzHermiteReduce[1/(x^2*y), basis, y];
  tassert["round-trip (Schultz) for 1/(x^2 y)",
    schultzRoundTripOK[1/(x^2*y), basis, y, rS]];
  tassert["algPart matches hermiteReduce (1/(x^2 y))",
    afCoeffsEqualQ[rH["algPart"]["Coeffs"], rS["algPart"]["Coeffs"]]];
  tassert["remainder matches hermiteReduce (1/(x^2 y))",
    afCoeffsEqualQ[rH["remainder"]["Coeffs"], rS["remainder"]["Coeffs"]]];
];

Module[{basis, rH, rS},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  rH = hermiteReduce[1/(x*y), basis, y];
  rS = schultzHermiteReduce[1/(x*y), basis, y];
  tassert["round-trip (Schultz) for 1/(x y)",
    schultzRoundTripOK[1/(x*y), basis, y, rS]];
  tassert["algPart matches (1/(x y))",
    afCoeffsEqualQ[rH["algPart"]["Coeffs"], rS["algPart"]["Coeffs"]]];
  tassert["remainder matches (1/(x y))",
    afCoeffsEqualQ[rH["remainder"]["Coeffs"], rS["remainder"]["Coeffs"]]];
];

Module[{basis, rH, rS},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  rH = hermiteReduce[1/(x^3*y), basis, y];
  rS = schultzHermiteReduce[1/(x^3*y), basis, y];
  tassert["round-trip (Schultz) for 1/(x^3 y)",
    schultzRoundTripOK[1/(x^3*y), basis, y, rS]];
  tassert["algPart matches (1/(x^3 y))",
    afCoeffsEqualQ[rH["algPart"]["Coeffs"], rS["algPart"]["Coeffs"]]];
  tassert["remainder matches (1/(x^3 y))",
    afCoeffsEqualQ[rH["remainder"]["Coeffs"], rS["remainder"]["Coeffs"]]];
];

Module[{basis, rH, rS},
  basis = buildIntegralBasis[3, x, x];
  rH = hermiteReduce[1/(x^2*y^2), basis, y];
  rS = schultzHermiteReduce[1/(x^2*y^2), basis, y];
  tassert["round-trip (Schultz, n=3) for 1/(x^2 y^2)",
    schultzRoundTripOK[1/(x^2*y^2), basis, y, rS]];
  tassert["algPart matches (n=3, 1/(x^2 y^2))",
    afCoeffsEqualQ[rH["algPart"]["Coeffs"], rS["algPart"]["Coeffs"]]];
  tassert["remainder matches (n=3, 1/(x^2 y^2))",
    afCoeffsEqualQ[rH["remainder"]["Coeffs"], rS["remainder"]["Coeffs"]]];
];

Module[{basis, rH, rS},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  rH = hermiteReduce[1/(x^2*(x - 1)^2*y), basis, y];
  rS = schultzHermiteReduce[1/(x^2*(x - 1)^2*y), basis, y];
  tassert["round-trip (Schultz, two double poles)",
    schultzRoundTripOK[1/(x^2*(x - 1)^2*y), basis, y, rS]];
  tassert["algPart matches (two double poles)",
    afCoeffsEqualQ[rH["algPart"]["Coeffs"], rS["algPart"]["Coeffs"]]];
  tassert["remainder matches (two double poles)",
    afCoeffsEqualQ[rH["remainder"]["Coeffs"], rS["remainder"]["Coeffs"]]];
];

tsection["schultzHermiteReduce: D and Dinf flags"];

Module[{basis, rS, fac},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  rS = schultzHermiteReduce[1/(x^3*y), basis, y];
  fac = Rest[FactorSquareFreeList[rS["D"]]];
  tassert["D is squarefree after Schultz Hermite",
    AllTrue[fac, Last[#] == 1 &]];
  tassert["Dinf association exists",
    AssociationQ[rS["Dinf"]] && KeyExistsQ[rS["Dinf"], "solvable"]];
];

Module[{basis, rS},
  (* Integrand with finite-only poles AND no pole-at-infinity issue:        *)
  (* y/(x^2+1) on y^2 = x^2+1 has a_1 = y → coeffs {0, 1}, and after       *)
  (* common-denominator extraction b = x^2+1, deg(a_1)+δ_1 = 0+1 = 1 < 2.  *)
  (* So Dinf.solvable = True with no reduction needed.                      *)
  basis = buildIntegralBasis[2, x^2 + 1, x];
  rS = schultzHermiteReduce[y/(x^2 + 1), basis, y];
  tassert["round-trip for y/(x^2+1)",
    schultzRoundTripOK[y/(x^2 + 1), basis, y, rS]];
  tassert["Dinf.solvable = True (no infinity reduction needed)",
    rS["Dinf"]["solvable"] === True];
];

tsection["schultzHermiteReduce: deltas wired through into Dinf"];

Module[{basis, rS},
  basis = buildIntegralBasis[3, x, x];
  rS = schultzHermiteReduce[1/(x^2*y^2), basis, y];
  tassertEqual["Dinf.deltas matches basis[\"deltas\"]",
    basis["deltas"], rS["Dinf"]["deltas"]];
];

(* ::Section:: *)
(* Pole-at-infinity reduction (Sch §4.3 eq. 4.7-4.9, Lemma 4.4 part 2)         *)
(*                                                                              *)
(* These tests exercise schultzSolveInfinityLinearSystem on inputs that the    *)
(* finite-only Hermite cannot remove. The expected algPart for each input is  *)
(* hand-derived from the Schultz paper § 4.3 procedure, then cross-checked    *)
(* against the calculus answer.                                                 *)

tsection["schultzHermiteReduce: ∫ √(x²+2x) dx (Sch §1 introductory example)"];

Module[{basis, rS, expectedF2, ydx},
  (* y² = x² + 2x. Sch §1 gives the integral as (1/2)(x+1)y - (1/2)log(...).  *)
  (* The algebraic part is F = (x+1)·y/2, i.e. f₂ = (x+1)/2 in the η-basis.   *)
  basis = buildIntegralBasis[2, x^2 + 2*x, x];
  rS = schultzHermiteReduce[y, basis, y];
  tassert["round-trip on ∫y dx, y²=x²+2x",
    schultzRoundTripOK[y, basis, y, rS]];
  expectedF2 = (x + 1)/2;
  tassertEqual["algPart η₁-coefficient = 0 (no constant part)",
    0, Together[rS["algPart"]["Coeffs"][[1]]]];
  tassertEqual["algPart η₂-coefficient = (x+1)/2",
    expectedF2, Together[rS["algPart"]["Coeffs"][[2]]]];
  tassert["Dinf.solvable = True (infinity reduction succeeded)",
    rS["Dinf"]["solvable"] === True];
];

tsection["schultzHermiteReduce: ∫ x²/√(x³+1) dx (elementary, f₂ = 2/3)"];

Module[{basis, rS},
  (* y² = x³+1. d(2y/3)/dx = (1/3)·g'/y = (3x²)/(3y) = x²/y. So this integral *)
  (* equals (2/3)·y. The infinity solver should produce f₂ = 2/3, f₁ = 0,    *)
  (* g_i = 0, leaving zero remainder.                                         *)
  basis = buildIntegralBasis[2, x^3 + 1, x];
  rS = schultzHermiteReduce[x^2/y, basis, y];
  tassert["round-trip on ∫x²/y dx, y²=x³+1",
    schultzRoundTripOK[x^2/y, basis, y, rS]];
  tassertEqual["algPart η₁-coefficient = 0",
    0, Together[rS["algPart"]["Coeffs"][[1]]]];
  tassertEqual["algPart η₂-coefficient = 2/3",
    2/3, Together[rS["algPart"]["Coeffs"][[2]]]];
  tassertEqual["remainder is zero (η₁)",
    0, Together[rS["remainder"]["Coeffs"][[1]]]];
  tassertEqual["remainder is zero (η₂)",
    0, Together[rS["remainder"]["Coeffs"][[2]]]];
];

tsection["schultzHermiteReduce: post-reduction Lemma 4.4 invariant"];

Module[{basis, rS, remA, remD, deltas, n, ok},
  (* Sch Lemma 4.4(2): after the reduction, the remainder satisfies            *)
  (* deg(a_i) + δ_i < deg(b) for every i. Verify on ∫√(x²+2x) dx.              *)
  basis = buildIntegralBasis[2, x^2 + 2*x, x];
  rS = schultzHermiteReduce[y, basis, y];
  remA = rS["remainderA"]; remD = rS["D"];
  deltas = basis["deltas"]; n = basis["n"];
  ok = AllTrue[Range[n], Function[i,
    Module[{ai = remA[[i]], degAi},
      degAi = If[zeroQ[ai], -Infinity, Exponent[ai, x]];
      degAi + deltas[[i]] < Exponent[remD, x]
    ]
  ]];
  tassert["after reduction, deg(a_i) + δ_i < deg(b) for every i",
    ok];
];

(* ::Section:: *)
(* Cross-check against shiftAwayFromInfinity + hermiteReduce                    *)
(*                                                                              *)
(* The classical Trager pipeline removes infinity poles via Möbius shift then  *)
(* runs finite Hermite. The Schultz pipeline removes them directly. Both       *)
(* should produce the same algebraic part (up to the choice of representative *)
(* for the integration constant) and an equivalent remainder.                  *)

tsection["schultzHermiteReduce vs calculus answer (∫y dx, y²=x²+2x)"];

Module[{basis, schultz, schultzAlgY, dSchultz, expected},
  (* Cross-check: the AF-derivative of algPart is computed via afD (which     *)
  (* uses y² = g internally), so we evaluate it without going through         *)
  (* Mathematica's D operator on a Sqrt expression. Convert algPart and dF    *)
  (* to standard (x, y) form, then substitute y → √g for numerical equality. *)
  basis = buildIntegralBasis[2, x^2 + 2*x, x];
  schultz = schultzHermiteReduce[y, basis, y];
  (* (x+1)y/2 differentiated via afD then converted to (x, y):                *)
  schultzAlgY = afToStandard[afD[schultz["algPart"], basis], basis, y];
  dSchultz = schultzAlgY /. y -> Sqrt[x^2 + 2*x];
  (* d/dx[(x+1)y/2] = (1/2)·y + (x+1)/2·y' with y' = (x+1)/y, giving         *)
  (* (y² + (x+1)²)/(2y) = (2x²+4x+1)/(2y).                                    *)
  expected = (2 x^2 + 4 x + 1)/(2 Sqrt[x^2 + 2 x]);
  tassertEqual["d/dx[(x+1)y/2] = (2x²+4x+1)/(2y) (via afD)",
    Together[expected], Together[dSchultz]];
];

tSummary[];
