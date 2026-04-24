(* ::Package:: *)

(* ::Title:: *)
(* Tests for the surface-syntax wrapper IntegrateTrager[f, x] *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

Off[IntegrateTrager::autoreduce];

surfaceVerify[integrand_, x_Symbol] := Module[{result, diff},
  result = IntegrateTrager[integrand, x];
  If[MatchQ[result, _Failure], Return[<|"ok" -> False, "result" -> result|>]];
  diff = Simplify[D[result, x] - integrand];
  <|"ok" -> TrueQ[diff === 0], "result" -> result|>
];

tsection["surface syntax: single radical Sqrt[...]"];

Module[{v},
  v = surfaceVerify[1/Sqrt[x^2 + 1], x];
  tassert["1/Sqrt[x^2+1]", v["ok"]];
];

Module[{v},
  v = surfaceVerify[x/Sqrt[x^2 + 1], x];
  tassert["x/Sqrt[x^2+1] (pure algebraic)", v["ok"]];
];

Module[{v},
  v = surfaceVerify[1/Sqrt[1 - x^2], x];
  tassert["1/Sqrt[1-x^2] (ArcSin family)", v["ok"]];
];

Module[{v},
  v = surfaceVerify[1/Sqrt[x^2 - 1], x];
  tassert["1/Sqrt[x^2-1] (ArcCosh family)", v["ok"]];
];

Module[{v},
  v = surfaceVerify[1/(x * Sqrt[x^2 + 1]), x];
  tassert["1/(x Sqrt[x^2+1])", v["ok"]];
];

tsection["surface syntax: higher-order radicals"];

Module[{v},
  v = surfaceVerify[1/x^(1/3), x];
  tassert["1/x^(1/3)", v["ok"]];
];

tsection["surface syntax: failure tags"];

tassertFailure["multiple distinct radicals", "NotSimpleRadical",
  IntegrateTrager[1/(Sqrt[x^2 + 1] + Sqrt[x]), x]];

tassertFailure["non-algebraic integrand", "BadInput",
  IntegrateTrager[Exp[x]/Sqrt[x], x]];

tassertFailure["no radicals at all", "NotSimpleRadical",
  IntegrateTrager[1/x, x]];

tsection["surface syntax: non-elementary genus > 0 still reported"];

tassertFailure["1/Sqrt[x^3+1] (elliptic, genus 1)", "NonElementary",
  IntegrateTrager[1/Sqrt[x^3 + 1], x]];

tSummary[];
