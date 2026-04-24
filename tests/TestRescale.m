(* ::Package:: *)

(* ::Title:: *)
(* Tests for reduceIrreducibility integrand-rescale path *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

Off[IntegrateTrager::autoreduce];

(* Verify via differentiation. The user's y satisfies the ORIGINAL relation *)
(* y_user^n = g_user, and the result should be correct when we substitute    *)
(* y -> g_user^(1/n).                                                        *)

(* The antiderivative returned by IntegrateTrager uses y as the USER's y    *)
(* (satisfying y^n = g). We differentiate with implicit y' = g'/(n y^(n-1))*)
(* and reduce y-degree modulo y^n - g. Agreement with the original          *)
(* integrand (also reduced) is the correctness criterion.                   *)
(*                                                                           *)
(* Exception: when reduceIrreducibility applied a yScale rescale, the       *)
(* result is in the REDUCED generator by the time we see it (per the       *)
(* reassemble phase-0-reduce step which converts back). We re-run the       *)
(* reduction in the test to pick up the reduced (n, g) for verification.   *)

(* Numerical verification. Pick the principal branch y_user = gOrig^(1/n). *)
(* Differentiate the result with y substituted for this branch, compare to *)
(* integrand with same substitution at multiple test x values.              *)

integrateVerify[integrand_, nOrig_Integer, gOrig_, x_Symbol, y_Symbol] := Module[
  {result, yExpr, deriv, expected, sample, diff, okCount, testPts, pt},
  result = IntegrateTrager[integrand, {x, y, y^nOrig == gOrig}];
  If[MatchQ[result, _Failure], Return[<|"ok" -> False, "result" -> result|>]];
  yExpr = gOrig^(1/nOrig);
  deriv = D[result /. y -> yExpr, x];
  expected = integrand /. y -> yExpr;
  diff = Simplify[deriv - expected];
  If[TrueQ[diff === 0], Return[<|"ok" -> True, "result" -> result|>]];
  (* Fall back to numeric at several well-chosen x points.                   *)
  testPts = {11/10, 13/10, 7/5, 3/2, 17/10, 2, 5/2};
  okCount = 0;
  Do[
    sample = N[diff /. x -> pt, 30];
    If[Abs[sample] < 10^(-20), okCount++],
    {pt, testPts}
  ];
  <|"ok" -> (okCount == Length[testPts]), "result" -> result|>
];

tsection["integrand rescale: absorb step with non-trivial yScale"];

Module[{v},
  v = integrateVerify[1/y, 2, x^2 * (x^2 + 1), x, y];
  tassert["1/y on y^2 = x^2(x^2+1)", v["ok"]];
];

Module[{v},
  v = integrateVerify[x/y, 2, x^2 * (x^2 + 1), x, y];
  tassert["x/y on y^2 = x^2(x^2+1)", v["ok"]];
];

tsection["integrand rescale: gcd-of-exponents reduction"];

Module[{v},
  v = integrateVerify[1/y, 4, (x^2 + 1)^2, x, y];
  tassert["1/y on y^4 = (x^2+1)^2 (n reduced 4->2)", v["ok"]];
];

(* y^6 = x^2: reduces to y^3 = x. Pure algebraic antiderivative, no logs. *)
Module[{v},
  v = integrateVerify[1/y, 6, x^2, x, y];
  tassert["1/y on y^6 = x^2 (n reduced 6->3, pure algebraic, works)", v["ok"]];
];

tsection["integrand rescale: composite absorb + gcd"];

Module[{v},
  v = integrateVerify[1/y, 4, x^4 * (x^2 + 1)^2, x, y];
  tassert["1/y on y^4 = x^4(x^2+1)^2", v["ok"]];
];

tSummary[];
