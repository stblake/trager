(* ::Package:: *)

(* ::Title:: *)
(* Tests for the Schultz double-ideal divisor representation (§S.2). *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

tsection["SchultzDivisor: data structure and trivial divisor"];

Module[{basis, d},
  basis = buildIntegralBasis[2, x^3 + 1, x];
  d = schultzDivisorTrivial[basis];
  tassert["trivial divisor is a SchultzDivisor", schultzDivisorQ[d]];
  tassertEqual["trivial aFin is 2×2 identity",
    IdentityMatrix[2], d["aFin"]];
  tassertEqual["trivial aInf is 2×2 identity",
    IdentityMatrix[2], d["aInf"]];
  tassertEqual["trivial divisor has degree 0", 0, schultzDivisorDegree[d]];
];

tsection["SchultzDivisor: finite-polynomial constructor"];

Module[{basis, d},
  basis = buildIntegralBasis[2, x^3 + 1, x];
  d = schultzDivisorFromFinitePoly[x, basis];
  tassert["is a SchultzDivisor", schultzDivisorQ[d]];
  (* Finite part is x * I_2, already HNF. *)
  tassertEqual["aFin[1,1] = x", x, d["aFin"][[1, 1]]];
  tassertEqual["aFin[2,2] = x", x, d["aFin"][[2, 2]]];
  tassertEqual["aFin[1,2] = 0", 0, d["aFin"][[1, 2]]];
  tassertEqual["aFin[2,1] = 0", 0, d["aFin"][[2, 1]]];
  (* Infinite part on {w_0, x^{-2} w_1} basis: b-matrix for div(x · O^∞)   *)
  (* evaluated at infinity gives x * I_2 in the w-basis. After the         *)
  (* change-of-basis to {x^{-δ_j} w_j} with δ = {0, 2}, x * ψ_j gives     *)
  (* x * x^{-δ_j} w_j, so aInf[j,j] = x (untouched diagonal since we       *)
  (* pass A * I_n directly). After HNF normalization the diagonal becomes *)
  (* monomial x (k_j = 1 each).                                            *)
  tassertEqual["aInf diagonal entries are both x (monomial form)",
    {x, x}, {d["aInf"][[1, 1]], d["aInf"][[2, 2]]}];
  (* Divisor of x is a zero at finite place x=0 (valuation +1 over each   *)
  (* place over x=0) and poles at infinite places. Over y^2 = x^3+1 there *)
  (* is ONE finite place over x=0 (ramification 1, since g(0) = 1 ≠ 0)   *)
  (* so ord_{x=0}(x) = 1 there; at each of the two infinite places         *)
  (* (ramification 1 since gcd(2,3) = 1, so actually ONE infinite place   *)
  (* of ramification 2) we have ord_∞(x) = -2. Net: deg = 2·1 − 2 = 0    *)
  (* for div(x); but this is div(x · O^∞) as a fractional ideal of O^∞,   *)
  (* whose finite "degree" is 2 (from deg det aFin = 2·1) and similarly   *)
  (* for the infinite side. Net should be 0 as this ideal corresponds to *)
  (* the principal divisor of x.                                           *)
  tassertEqual["degree of div(x · O^∞)-as-Schultz-divisor is 0", 0,
    schultzDivisorDegree[d]];
];

tsection["SchultzDivisor: principal divisor of a rational function"];

Module[{basis, fAF, d, y},
  y = SymbolName`y;   (* placeholder; we'll use y directly below *)
];

Module[{basis, fAF, d},
  basis = buildIntegralBasis[2, x^3 + 1, x];
  (* f = x (pure rational function) as an AF element:                     *)
  (* Coeffs[1] = x, Coeffs[2] = 0 on the basis {w_0, w_1} = {1, y}.       *)
  fAF = afMake[{x, 0}, basis];
  d = schultzPrincipalDivisor[fAF, basis, y];
  tassert["principal divisor of x is a SchultzDivisor", schultzDivisorQ[d]];
  tassertEqual["principal divisor of x has degree 0", 0,
    schultzDivisorDegree[d]];
];

Module[{basis, fAF, gAF, productDiv, productAF},
  basis = buildIntegralBasis[2, x^3 + 1, x];
  fAF = afMake[{x + 1, 0}, basis];
  gAF = afMake[{1/(x - 2), 0}, basis];
  (* div(f * g) should equal div(f) + div(g) (equivalently, multiply      *)
  (* ideals), and the composite principal divisor has degree 0.           *)
  productAF = afTimes[fAF, gAF, basis];
  productDiv = schultzPrincipalDivisor[productAF, basis, y];
  tassertEqual["div(f * g) for rational f, g has degree 0",
    0, schultzDivisorDegree[productDiv]];
];

tsection["SchultzDivisor: round-trip div(f) · div(1/f) ~ trivial"];

Module[{basis, fAF, invAF, productAF},
  basis = buildIntegralBasis[2, x^3 + 1, x];
  fAF = afMake[{x + 1, 0}, basis];
  invAF = afInverse[fAF, basis];
  productAF = afTimes[fAF, invAF, basis];
  (* f * (1/f) = 1, so div(f * 1/f) = 0 (trivial divisor).                *)
  tassertEqual["f · (1/f)[1] (constant part) is 1",
    1, Together[productAF["Coeffs"][[1]]]];
  tassertEqual["f · (1/f)[y] (y-part) is 0",
    0, Together[productAF["Coeffs"][[2]]]];
];

tsection["SchultzDivisor: finite HNF"];

Module[{M, H},
  (* Identity matrix is already HNF. *)
  M = IdentityMatrix[3];
  H = schultzHNFFinite[M, x];
  tassertEqual["HNF of I_3 over k[x] is I_3", IdentityMatrix[3], H];
];

Module[{M, H},
  (* A diagonal polynomial matrix is already HNF (rows are lined up). *)
  M = DiagonalMatrix[{x, x^2, x^3}];
  H = schultzHNFFinite[M, x];
  tassertEqual["HNF of diag(x, x^2, x^3) is itself",
    DiagonalMatrix[{x, x^2, x^3}], H];
];

tsection["SchultzDivisor: infinity HNF"];

Module[{M, H},
  (* Identity is already HNF at infinity (diagonal x^0 entries). *)
  M = IdentityMatrix[3];
  H = schultzHNFInfinity[M, x];
  tassertEqual["HNF of I_3 over k[[1/x]] is I_3", IdentityMatrix[3], H];
];

Module[{M, H},
  (* Diagonal with monomials of various degrees — already HNF. *)
  M = {{x, 0}, {0, 1/x}};
  H = schultzHNFInfinity[M, x];
  tassertEqual["HNF of {{x,0},{0,1/x}} is itself", {{x, 0}, {0, 1/x}}, H];
];

Module[{M, H},
  (* Exact Sch §6.2 divisor δ(+18)/δ(−18) infinity matrix.                *)
  (* The paper gives it already in HNF: diag(x, 1/x), above-diag (x+1).  *)
  (* All nonzero terms of (x+1) have degree > -1 = k_2, so canonical.    *)
  M = {{x, x + 1}, {0, 1/x}};
  H = schultzHNFInfinity[M, x];
  tassertEqual["HNF of Sch §6.2 δ(+18)/δ(−18) infinity matrix is itself",
    {{x, x + 1}, {0, 1/x}}, H];
];

Module[{M, H, expected},
  (* Non-canonical above-diagonal: entry has a low-degree part that       *)
  (* should be removed. E.g. diagonal 1 = x^0, above-diag 1 + 1/x:        *)
  (* k_2 = 0, so we keep only monomials of degree > 0. The 1 and 1/x      *)
  (* terms both have degree ≤ 0 and should be eliminated.                  *)
  M = {{1, 1 + 1/x}, {0, 1}};
  H = schultzHNFInfinity[M, x];
  (* After reduction, above-diag entry should be 0.                        *)
  expected = {{1, 0}, {0, 1}};
  tassertEqual["infinity-HNF cancels sub-pivot monomials above diagonal",
    expected, H];
];

tsection["SchultzDivisor: schultzHNFFinite on non-trivial reductions"];

Module[{M, H},
  (* Lower-triangular entry needs to be eliminated against the diagonal pivot.*)
  M = {{1, 0}, {x + 1, x^2 + 1}};
  H = schultzHNFFinite[M, x];
  (* Row 2 - (x+1)·Row 1 should give (0, x²+1).                                *)
  tassertEqual["HNF eliminates lower-triangular polynomial entry",
    {{1, 0}, {0, x^2 + 1}}, H];
];

Module[{M, H, det},
  (* Above-diagonal reduction modulo the diagonal pivot.                       *)
  M = {{x^2 + 1, x^3}, {0, x}};
  H = schultzHNFFinite[M, x];
  (* x^3 mod x = 0, so the (1,2) entry should reduce to 0.                    *)
  det = Together[Det[H]];
  tassertEqual["HNF determinant equals input determinant (matrix invariant)",
    Together[Det[M]], det];
  tassertEqual["above-diagonal reduces mod diagonal: (1,2) entry → 0",
    0, Together[H[[1, 2]]]];
];

tsection["SchultzDivisor: principal divisor of a non-rational function"];

Module[{basis, fAF, divDiv, deg},
  (* f = 1 + y on y² = x³+1 — non-trivial (y-bearing) principal divisor.      *)
  (* div(f) must have degree 0. The multiplication matrix is non-diagonal,    *)
  (* so this exercises the matrix→HNF path that constant-f tests skip.        *)
  basis = buildIntegralBasis[2, x^3 + 1, x];
  fAF = afMake[{1, 1}, basis];
  divDiv = schultzPrincipalDivisor[fAF, basis, y];
  deg = schultzDivisorDegree[divDiv];
  tassertEqual["deg(div(1 + y)) = 0", 0, deg];
];

Module[{basis, fAF, gAF, prodDiv, prodInv},
  (* div(f * (1/f)) for f = x + y on y² = x²+1.                                *)
  basis = buildIntegralBasis[2, x^2 + 1, x];
  fAF = afMake[{x, 1}, basis];
  gAF = afInverse[fAF, basis];
  prodDiv = schultzDivisorMultiplyPrincipal[fAF, gAF, basis, y];
  tassertEqual["deg(div(f · 1/f)) = 0",
    0, schultzDivisorDegree[prodDiv]];
  prodInv = schultzPrincipalDivisor[afTimes[fAF, gAF, basis], basis, y];
  tassertEqual["aFin matches direct construction",
    prodInv["aFin"], prodDiv["aFin"]];
];

tsection["SchultzDivisor: Sch §6.2 D_2 matrix (y² = x(x+5)(x-4)(x-3))"];

Module[{basis, gPoly, finiteRows, infinityRows, aFinHNF, aInfHNF},
  (* The paper (page 23) gives the explicit divisor matrix for D_2 on this    *)
  (* curve as (((x(x+5)(x-4)(x-3), 0), (0, 1)), ((1, 0), (0, 1))). The HNF    *)
  (* of the same matrix should be itself (already canonical).                  *)
  gPoly = x*(x + 5)*(x - 4)*(x - 3);
  basis = buildIntegralBasis[2, gPoly, x];
  finiteRows = {{Expand[gPoly], 0}, {0, 1}};
  infinityRows = {{1, 0}, {0, 1}};
  aFinHNF = schultzHNFFinite[finiteRows, x];
  aInfHNF = schultzHNFInfinity[infinityRows, x];
  tassertEqual["HNF of Sch §6.2 D_2 finite matrix is itself",
    finiteRows, Map[Together, aFinHNF, {2}]];
  tassertEqual["HNF of Sch §6.2 D_2 infinity matrix is itself",
    infinityRows, aInfHNF];
];

tsection["SchultzDivisor: Sch §6.2 residue divisor δ(+18)/δ(-18)"];

Module[{basis, finiteRows, infinityRows, aInfHNF},
  (* The paper (page 24) gives the explicit residue-divisor matrix:           *)
  (*   δ(+18)/δ(-18) = (((1, 0), (0, 1)), ((x, x+1), (0, 1/x)))                *)
  (* The infinity matrix is in HNF: monomial diagonal (x and 1/x), off-      *)
  (* diagonal entry (x+1) with all monomials of degree > k_2 = -1 (so x and   *)
  (* the constant 1 are both ≥ degree 0 > -1).                                 *)
  basis = buildIntegralBasis[2, x*(x + 5)*(x - 4)*(x - 3), x];
  infinityRows = {{x, x + 1}, {0, 1/x}};
  aInfHNF = schultzHNFInfinity[infinityRows, x];
  tassertEqual["Sch §6.2 residue infinity matrix is canonical",
    infinityRows, aInfHNF];
  (* Determinant invariant: det = x · (1/x) = 1. So the divisor has finDeg − *)
  (* infDeg contribution 0 from the infinity side.                            *)
  tassertEqual["det of infinity matrix is 1",
    1, Together[Det[aInfHNF]]];
];

tsection["SchultzDivisor: schultzDivisorPrincipalQ on trivial divisor"];

Module[{basis, triv, result},
  basis = buildIntegralBasis[2, x^3 + 1, x];
  triv = schultzDivisorTrivial[basis];
  result = schultzDivisorPrincipalQ[triv];
  tassertEqual["trivial divisor is recognized as principal",
    True, First[result]];
  tassert["principal generator candidate is an AF element",
    afElementQ[Last[result]]];
];

tsection["SchultzDivisor: schultzDivisorPrincipalQ on non-degree-0 divisor"];

Module[{basis, A, divA, result},
  (* schultzDivisorFromFinitePoly[A, basis] is NOT div(A) — it represents the *)
  (* fractional ideal A·O^∞ paired with A·O_∞. As a Schultz-pair its degree  *)
  (* is 0 (the finite and infinity parts cancel), but its INTERPRETATION as a *)
  (* divisor is *not* the principal divisor div(A). schultzDivisorPrincipalQ  *)
  (* uses a heuristic that looks only at the aInf diagonal exponents — which *)
  (* for this construction always have k_j = deg(A) > 0, failing the          *)
  (* heuristic. This documents a known limitation; the proper fix requires    *)
  (* simultaneous HNF of (aFin, aInf) to extract the d_i exponents of Sch     *)
  (* Lemma 4.1, and is deferred to S.6 (where it is actually needed).          *)
  basis = buildIntegralBasis[2, x^3 + 1, x];
  A = x;
  divA = schultzDivisorFromFinitePoly[A, basis];
  tassertEqual["degree of A · I_n divisor is 0 (consistency check)",
    0, schultzDivisorDegree[divA]];
  result = schultzDivisorPrincipalQ[divA];
  (* The heuristic returns False — documenting this rather than asserting    *)
  (* the (correct) principal nature of div(x). When S.6 lands the test       *)
  (* should flip to True with the correct generator returned.                 *)
  tassertEqual["[KNOWN LIMITATION] heuristic does not detect div(A·I) as principal",
    False, First[result]];
];

tsection["SchultzDivisor: valInfinity helper"];

tassertEqual["valInfinity(0) = Infinity", Infinity, valInfinity[0, x]];
tassertEqual["valInfinity(x) = −1", -1, valInfinity[x, x]];
tassertEqual["valInfinity(1/x) = 1", 1, valInfinity[1/x, x]];
tassertEqual["valInfinity(x^2 + 1) = −2", -2, valInfinity[x^2 + 1, x]];
tassertEqual["valInfinity((x+1)/(x^2+1)) = 1",
  1, valInfinity[(x + 1)/(x^2 + 1), x]];
tassertEqual["valInfinity(5) = 0 (constant)", 0, valInfinity[5, x]];

tSummary[];
