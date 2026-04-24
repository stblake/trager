(* ::Package:: *)

(* ::Title:: *)
(* End-to-end tests for IntegrateTrager *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

Off[IntegrateTrager::autoreduce];
Off[IntegrateTrager::scale];

(* Differentiation-based correctness check:                                 *)
(*   let F = IntegrateTrager[f, {x, y, y^n == g}]                          *)
(*   substitute y -> g^(1/n) everywhere, then verify dF/dx == f /. y -> g^(1/n)*)

integrateVerify[integrand_, n_, g_, x_Symbol, y_Symbol] := Module[
  {result, yRoot, fSub, diff, samples, tol, prec = 60},
  result = IntegrateTrager[integrand, {x, y, y^n == g}];
  If[MatchQ[result, _Failure], Return[<|"ok" -> False, "result" -> result|>]];
  yRoot = g^(1/n);
  fSub  = integrand /. y -> yRoot;
  diff  = Simplify[D[result /. y -> yRoot, x] - fSub];
  If[TrueQ[diff === 0],
    <|"ok" -> True, "result" -> result, "diff" -> diff|>,
    (* Symbolic Simplify failed; fall back to high-precision numerical       *)
    (* sampling (same strategy as IntegrateTrager's step-10 verifier).       *)
    samples = Quiet @ Block[{},
      SeedRandom[20240515];
      Table[N[diff /. x -> RandomReal[{-7/2, 11/2}, WorkingPrecision -> prec],
              prec], {6}]
    ];
    tol = 10^(-prec/2);
    <|"ok" -> AllTrue[samples,
                      NumericQ[#] && Abs[Re[#]] < tol && Abs[Im[#]] < tol &],
      "result" -> result, "diff" -> diff, "samples" -> samples|>
  ]
];

tsection["tier 1: basic elementary integrals, n = 2"];

tassert["1/Sqrt[x^2+1]",
  integrateVerify[1/y, 2, x^2 + 1, x, y]["ok"]];
tassert["x/Sqrt[x^2+1] (pure algebraic)",
  integrateVerify[x/y, 2, x^2 + 1, x, y]["ok"]];
tassert["1/Sqrt[x^2-1]",
  integrateVerify[1/y, 2, x^2 - 1, x, y]["ok"]];
tassert["1/(x Sqrt[x^2+1])",
  integrateVerify[1/(x y), 2, x^2 + 1, x, y]["ok"]];
tassert["1/Sqrt[1-x^2]",
  integrateVerify[1/y, 2, 1 - x^2, x, y]["ok"]];
tassert["x/Sqrt[1-x^2] (pure algebraic)",
  integrateVerify[x/y, 2, 1 - x^2, x, y]["ok"]];

tsection["tier 1: log cases with residues in a nontrivial algebraic extension"];

(* Sqrt[x^2 - 4x - 1]/(x^2 + 1): genus 0, elementary, but the Rothstein-   *)
(* Trager residue polynomial has roots in Q(Sqrt[1 +/- 2 I]) — a quartic   *)
(* extension. Simplify cannot prove the symbolic diff = 0, exercising the  *)
(* step-10 numerical-sampling fallback path.                                *)
tassert["y/(x^2+1) on y^2 = x^2-4x-1 (algebraic-extension residues)",
  integrateVerify[y/(x^2+1), 2, x^2 - 4 x - 1, x, y]["ok"]];

tsection["tier 1: higher radicals (n = 3, 4)"];
tsection["(algebraic-only cases, no log contribution, work correctly)"];

tassert["1/x^(1/3), i.e. 1/y on y^3 = x (algebraic, works)",
  integrateVerify[1/y, 3, x, x, y]["ok"]];
tassert["1/x^(2/3), i.e. 1/y on y^3 = x^2 (algebraic, works)",
  integrateVerify[1/y, 3, x^2, x, y]["ok"]];
tassert["1/x^(3/4), i.e. 1/y on y^4 = x^3 (algebraic, works)",
  integrateVerify[1/y, 4, x^3, x, y]["ok"]];

tsection["tier 4: non-elementary genus > 0 integrands"];

(* With the default "MaxGenus" -> Infinity, the pipeline runs through the  *)
(* torsion search and correctly reports NonElementary for classically non- *)
(* elementary integrands. The PositiveGenus gate is exercised in           *)
(* TestGenusPositive.m via explicit "MaxGenus" -> 0.                       *)

tassertFailure["y^2 = x^3+1 (elliptic, g=1)", "NonElementary",
  IntegrateTrager[1/y, {x, y, y^2 == x^3 + 1}]];
tassertFailure["y^2 = x^4+1 (g=1)", "NonElementary",
  IntegrateTrager[1/y, {x, y, y^2 == x^4 + 1}]];
tassertFailure["y^2 = x^5-x (hyperelliptic, g=2)", "NonElementary",
  IntegrateTrager[1/y, {x, y, y^2 == x^5 - x}]];

tsection["tier 4: input validation failures"];

tassertFailure["y^2 == 4 (constant radicand)", "DegenerateRadical",
  IntegrateTrager[1/y, {x, y, y^2 == 4}]];
tassertFailure["integrand with Exp", "BadInput",
  IntegrateTrager[Exp[x]/y, {x, y, y^2 == x^2 + 1}]];
tassertFailure["relation with irrational coeff", "UnsupportedBaseField",
  IntegrateTrager[1/y, {x, y, y^2 == x^2 + Sqrt[2]}]];

On[IntegrateTrager::autoreduce];
On[IntegrateTrager::scale];

tSummary[];
