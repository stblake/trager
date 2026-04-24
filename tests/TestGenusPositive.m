(* ::Package:: *)

(* ::Title:: *)
(* Tests for genus > 0 support ("MaxGenus" option + NonElementary verification) *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

Off[IntegrateTrager::autoreduce];

(* Helper: integrate permissively and check via differentiation. *)
integrateAndVerify[integrand_, n_, g_, x_Symbol, y_Symbol] := Module[
  {result, yRoot, fSub, diff},
  result = IntegrateTrager[integrand, {x, y, y^n == g}, "MaxGenus" -> Infinity];
  If[MatchQ[result, _Failure], Return[result]];
  yRoot = g^(1/n);
  fSub  = integrand /. y -> yRoot;
  diff  = Simplify[D[result /. y -> yRoot, x] - fSub];
  <|"result" -> result, "ok" -> TrueQ[diff === 0]|>
];

tsection["\"MaxGenus\" option: explicit gate still fires"];

tassertFailure["MaxGenus->0 rejects genus-1",
  "PositiveGenus",
  IntegrateTrager[1/y, {x, y, y^2 == x^3 + 1}, "MaxGenus" -> 0]];

tassertFailure["MaxGenus->0 rejects genus-2",
  "PositiveGenus",
  IntegrateTrager[1/y, {x, y, y^2 == x^5 - x}, "MaxGenus" -> 0]];

tsection["genus 1 (elliptic): classically non-elementary integrands"];

tassertFailure["1/Sqrt[x^3+1] -> NonElementary",
  "NonElementary",
  IntegrateTrager[1/y, {x, y, y^2 == x^3 + 1}, "MaxGenus" -> Infinity]];

tassertFailure["x/Sqrt[x^3+1] -> NonElementary",
  "NonElementary",
  IntegrateTrager[x/y, {x, y, y^2 == x^3 + 1}, "MaxGenus" -> Infinity]];

tassertFailure["1/Sqrt[x^4+1] -> NonElementary",
  "NonElementary",
  IntegrateTrager[1/y, {x, y, y^2 == x^4 + 1}, "MaxGenus" -> Infinity]];

tsection["genus 1: integrands that HAPPEN to be elementary"];

Module[{v},
  (* x^2/Sqrt[x^3+1]: antiderivative (2/3) Sqrt[x^3+1] *)
  v = integrateAndVerify[x^2/y, 2, x^3 + 1, x, y];
  tassert["x^2/Sqrt[x^3+1] is elementary (d/dx(2y/3) = x^2/y)", v["ok"]];
  tassertEqual["result is 2y/3", 2 y/3, v["result"]];
];

Module[{v},
  (* x^3/Sqrt[x^4+1]: d/dx Sqrt[x^4+1]/2 = x^3/Sqrt[x^4+1] *)
  v = integrateAndVerify[x^3/y, 2, x^4 + 1, x, y];
  tassert["x^3/Sqrt[x^4+1] is elementary", v["ok"]];
];

tsection["genus 3 (quartic Fermat-like): elementary via torsion"];

Module[{v},
  (* 1/(x^4+1)^(1/4) on y^4 = x^4+1: genus 3, elementary with torsion k=4. *)
  (* Classical result: (1/4) Log[(y+x)/(y-x)] + (1/2) ArcTan[x/y]         *)
  v = integrateAndVerify[1/y, 4, x^4 + 1, x, y];
  tassert["1/y on y^4 = x^4+1 is elementary (torsion k=4)", v["ok"]];
];

tsection["genus 2 (hyperelliptic): non-elementary baseline"];

tassertFailure["1/Sqrt[x^5-x] (genus 2) -> NonElementary",
  "NonElementary",
  IntegrateTrager[1/y, {x, y, y^2 == x^5 - x}, "MaxGenus" -> Infinity]];

tsection["diagnostic: verified flag set on elementary genus > 0 cases"];

Module[{r, diag},
  r = IntegrateTrager[x^2/y, {x, y, y^2 == x^3 + 1},
                      "MaxGenus" -> Infinity, "Diagnostics" -> True];
  diag = r["Diagnostics"];
  tassert["diagnostics contains 'verified'",
    KeyExistsQ[diag, "verified"] && diag["verified"] === True];
];

tSummary[];
