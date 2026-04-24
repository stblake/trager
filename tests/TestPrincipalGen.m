(* ::Package:: *)

(* ::Title:: *)
(* Tests for PrincipalGen.m and Normalize.m *)

(* ::Text:: *)
(* These tests exercise the individual helpers (polynomial HNF, rational  *)
(* degree, pole-at-infinity checks) that support findPrincipalGenerator. *)
(*                                                                           *)
(* NOTE on the main algorithm: findPrincipalGenerator itself is known to   *)
(* produce elements that pass the pole-free-at-infinity check but do not  *)
(* always satisfy (v) = D for the original divisor. See trager_status.md  *)
(* for the current gap and TragerPlan.md §13 for the port plan. The tests *)
(* below verify the LOCAL helpers are correct; the GLOBAL correctness of  *)
(* findPrincipalGenerator is tested indirectly via IntegrateTrager (where *)
(* tier-1 cases currently surface as ImplementationIncomplete).            *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

tsection["rationalDegInZ: degree of rational functions"];

tassert["deg(0) = -Infinity",
  rationalDegInZ[0, x] === -Infinity];
tassert["deg(1) = 0",
  rationalDegInZ[1, x] === 0];
tassert["deg(x) = 1",
  rationalDegInZ[x, x] === 1];
tassert["deg(1/x) = -1",
  rationalDegInZ[1/x, x] === -1];
tassert["deg(x^2+1) = 2",
  rationalDegInZ[x^2 + 1, x] === 2];
tassert["deg((x+1)/(x^2+1)) = -1",
  rationalDegInZ[(x + 1)/(x^2 + 1), x] === -1];

tsection["polyOrderAtZero and zAdicOrderAtZero"];

tassert["polyOrderAtZero[x, x] = 1",
  polyOrderAtZero[x, x] === 1];
tassert["polyOrderAtZero[x^3 + x^2, x] = 2",
  polyOrderAtZero[x^3 + x^2, x] === 2];
tassert["polyOrderAtZero[1+x, x] = 0",
  polyOrderAtZero[1 + x, x] === 0];
tassert["zAdicOrderAtZero[1/x, x] = -1",
  zAdicOrderAtZero[1/x, x] === -1];
tassert["zAdicOrderAtZero[x^2/(x+1), x] = 2",
  zAdicOrderAtZero[x^2/(x + 1), x] === 2];

tsection["noPoleAtInfinityRowQ: AF element pole-at-infinity check"];

Module[{basis},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  (* AF {1, 0} = 1: constant, pole-free at infinity. *)
  tassert["AF {1, 0} pole-free at infinity",
    noPoleAtInfinityRowQ[{1, 0}, basis]];
  (* AF {0, 1} = y: at infinity y ~ x, pole. *)
  tassert["AF {0, 1} (y) has pole at infinity",
    !noPoleAtInfinityRowQ[{0, 1}, basis]];
  (* AF {1/x, 0} = 1/x: zero at infinity. *)
  tassert["AF {1/x, 0} pole-free at infinity (zero there)",
    noPoleAtInfinityRowQ[{1/x, 0}, basis]];
  (* AF {1/x, 1/x} = (1+y)/x: pole-free at infinity per worked example.   *)
  tassert["AF {1/x, 1/x} = (1+y)/x pole-free at infinity",
    noPoleAtInfinityRowQ[{1/x, 1/x}, basis]];
  (* AF {x, 0} = x has pole at infinity. *)
  tassert["AF {x, 0} has pole at infinity",
    !noPoleAtInfinityRowQ[{x, 0}, basis]];
];

tsection["polynomialHNFOverKz: row reduction preserves K(z) span"];

Module[{mat, reduced, nonzero},
  mat = {{x, 1}, {x^2, x}};
  reduced = polynomialHNFOverKz[mat, x];
  nonzero = Select[reduced, !AllTrue[#, PossibleZeroQ] &];
  tassert["polynomialHNFOverKz produces at least one nonzero row",
    Length[nonzero] >= 1];
  (* The second row {x^2, x} = x * {x, 1} is a K(x)-multiple of the first,*)
  (* so the K(x)-span has dim 1 and reduction should give one nonzero row.*)
  tassert["polynomialHNFOverKz on rank-1 matrix gives 1 nonzero row",
    Length[nonzero] === 1];
];

Module[{mat, reduced},
  mat = {{1, x}, {x, 1}};
  reduced = polynomialHNFOverKz[mat, x];
  tassert["polynomialHNFOverKz produces a list of rows",
    ListQ[reduced] && Length[reduced] === 2];
];

tsection["polynomialExtendedGCDExt: extended GCD over algebraic extensions"];

(* Pure ℚ path: should agree with the built-in PolynomialExtendedGCD *)
Module[{r},
  r = polynomialExtendedGCDExt[x^3 - 1, x^2 - 1, x, {}];
  tassert["EGCD(x^3-1, x^2-1) over Q: g = x - 1",
    PossibleZeroQ[r[[1]] - (x - 1)]];
  tassert["EGCD(x^3-1, x^2-1) over Q: Bezout identity",
    PossibleZeroQ[Expand[r[[2]] (x^3 - 1) + r[[3]] (x^2 - 1) - r[[1]]]]];
];

(* Q(Sqrt[2]) path: x^2 - 2 and x - Sqrt[2] share factor x - Sqrt[2]    *)
(* over Q(√2) -- Mathematica's built-in cannot detect this without the *)
(* Extension option that PolynomialExtendedGCD does NOT accept.        *)
Module[{alpha, r},
  alpha = Sqrt[2];
  r = polynomialExtendedGCDExt[x^2 - 2, x - alpha, x, {alpha}];
  tassert["EGCD(x^2-2, x-√2) over Q(√2): g is monic in x - √2",
    PossibleZeroQ[Simplify[r[[1]] - (x - alpha)]]];
  tassert["EGCD(x^2-2, x-√2) over Q(√2): Bezout identity",
    PossibleZeroQ[Simplify[
      r[[2]] (x^2 - 2) + r[[3]] (x - alpha) - r[[1]]]]];
];

(* Q(ω) path: splitting x^3-1 over a primitive cube root of unity.     *)
(* ω satisfies ω^2 + ω + 1 = 0; then x^3 - 1 = (x-1)(x-ω)(x-ω^2). The *)
(* EGCD of x^3-1 and x^2+x+1 over Q(ω) is monic (x-ω)(x-ω^2) = x^2+x+1.*)
Module[{w, r},
  w = Root[#^2 + # + 1 &, 1];
  r = polynomialExtendedGCDExt[x^3 - 1, x^2 + x + 1, x, {w}];
  tassert["EGCD(x^3-1, x^2+x+1) over Q(ω): g = x^2 + x + 1",
    PossibleZeroQ[Simplify[r[[1]] - (x^2 + x + 1)]]];
  tassert["EGCD over Q(ω): Bezout identity",
    PossibleZeroQ[Simplify[
      r[[2]] (x^3 - 1) + r[[3]] (x^2 + x + 1) - r[[1]]]]];
];

(* Q(∛2) path: x^3 - 2 factors as (x - α)(x^2 + αx + α^2). EGCD of    *)
(* these two is the quadratic cofactor.                                *)
Module[{alpha, cofactor, r},
  alpha    = Root[#^3 - 2 &, 1];
  cofactor = x^2 + alpha x + alpha^2;
  r = polynomialExtendedGCDExt[x^3 - 2, cofactor, x, {alpha}];
  tassert["EGCD(x^3-2, x^2+αx+α^2) over Q(∛2): g = x^2 + αx + α^2",
    PossibleZeroQ[RootReduce[r[[1]] - cofactor]]];
  tassert["EGCD over Q(∛2): Bezout identity",
    PossibleZeroQ[RootReduce[Expand[
      r[[2]] (x^3 - 2) + r[[3]] cofactor - r[[1]]]]]];
];

(* Coprime case in Q(ω): x - 1 and x - ω share nothing; g = 1.         *)
Module[{w, r},
  w = Root[#^2 + # + 1 &, 1];
  r = polynomialExtendedGCDExt[x - 1, x - w, x, {w}];
  tassert["EGCD(x-1, x-ω) over Q(ω): coprime, g = 1",
    PossibleZeroQ[Simplify[r[[1]] - 1]]];
  tassert["EGCD(x-1, x-ω) over Q(ω): Bezout identity",
    PossibleZeroQ[Simplify[
      r[[2]] (x - 1) + r[[3]] (x - w) - r[[1]]]]];
];

tsection["hermiteNormalFormOverKz with algebraic extension"];

(* HNF of a 2x2 matrix over Q(ω). The K(x)-rank is 2; the HNF should   *)
(* be upper-triangular with pivot (x-1) on row 1 and a Q(ω)-monic     *)
(* polynomial on row 2.                                                *)
Module[{w, mat, hnf, top},
  w = Root[#^2 + # + 1 &, 1];
  mat = {{x - 1, w x}, {x^2 - 1, w}};
  hnf = hermiteNormalFormOverKz[mat, x, {w}];
  tassert["HNF over Q(ω): produces n rows",
    ListQ[hnf] && Length[hnf] === 2];
  tassert["HNF over Q(ω): below-pivot entry is zero",
    PossibleZeroQ[Simplify[hnf[[2, 1]]]]];
];

tsection["findPrincipalGenerator: returns either AF element or Failure"];

Module[{basis, Gtilde, Dpoly, div, result},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  Gtilde = afFromStandard[-y, basis, y];
  Dpoly  = x (1 + x^2);
  div    = residueDivisor[Gtilde, Dpoly, 1, basis, y];
  result = findPrincipalGenerator[div, basis, y];
  tassert["findPrincipalGenerator returns AF element or Failure",
    afElementQ[result] || MatchQ[result, _Failure]];
];

tSummary[];
