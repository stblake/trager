(* ::Package:: *)

(* ::Title:: *)
(* Parametric integrand tests *)

(* ::Text:: *)
(* Exercises the ℚ(parameters) base-field code path. The user declares one *)
(* or more free symbols as transcendental parameters via the "Parameters"  *)
(* option (or relies on Automatic auto-detection); the antiderivative is   *)
(* then valid on a Zariski-open subset of parameter values.                *)
(*                                                                           *)
(* Verification differentiates the proposed result and substitutes a random *)
(* generic real for each parameter before testing zero, since Simplify on  *)
(* parametric algebraic-log expressions is generally not strong enough to  *)
(* canonicalise to literal 0.                                                *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

Off[IntegrateTrager::autoreduce];
Off[IntegrateTrager::scale];

(* parametricVerify: differentiate, substitute generic random values for x  *)
(* and every parameter, sample at multiple points. Same strategy as the     *)
(* top-level pipeline's numerical fallback verifier.                        *)

ClearAll[parametricVerify];
parametricVerify[integrand_, n_, g_, x_Symbol, y_Symbol, params_List] := Module[
  {result, yRoot, fSub, diff, samples, tol, prec = 50, nSamples = 6},
  result = IntegrateTrager[integrand, {x, y, y^n == g}, "Parameters" -> params];
  If[MatchQ[result, _Failure], Return[<|"ok" -> False, "result" -> result|>]];
  yRoot = g^(1/n);
  fSub  = integrand /. y -> yRoot;
  diff  = D[result /. y -> yRoot, x] - fSub;
  samples = Quiet @ Block[{},
    SeedRandom[20240515];
    Table[
      Module[{paramRules},
        paramRules = (# -> RandomReal[{1/3, 23/7},
                                      WorkingPrecision -> prec]) & /@ params;
        N[diff /. paramRules /. x -> RandomReal[{-7/2, 11/2},
                                                WorkingPrecision -> prec],
          prec]
      ],
      {nSamples}
    ]
  ];
  tol = 10^(-prec/2);
  <|"ok" -> AllTrue[samples,
                    NumericQ[#] && Abs[Re[#]] < tol && Abs[Im[#]] < tol &],
    "result" -> result, "samples" -> samples|>
];

(* Surface-syntax wrapper for tests that prefer the radical form.            *)
ClearAll[parametricVerifySurface];
parametricVerifySurface[integrand_, x_Symbol, params_List] := Module[
  {result, diff, samples, tol, prec = 50, nSamples = 6},
  result = IntegrateTrager[integrand, x, "Parameters" -> params];
  If[MatchQ[result, _Failure], Return[<|"ok" -> False, "result" -> result|>]];
  diff = D[result, x] - integrand;
  samples = Quiet @ Block[{},
    SeedRandom[20240515];
    Table[
      Module[{paramRules},
        paramRules = (# -> RandomReal[{1/3, 23/7},
                                      WorkingPrecision -> prec]) & /@ params;
        N[diff /. paramRules /. x -> RandomReal[{-7/2, 11/2},
                                                WorkingPrecision -> prec],
          prec]
      ],
      {nSamples}
    ]
  ];
  tol = 10^(-prec/2);
  <|"ok" -> AllTrue[samples,
                    NumericQ[#] && Abs[Re[#]] < tol && Abs[Im[#]] < tol &],
    "result" -> result, "samples" -> samples|>
];

tsection["tier 0: option machinery"];

(* "Parameters" -> Automatic should auto-detect free symbols.                *)
tassert["Automatic detects {a}",
  !MatchQ[
    IntegrateTrager[1/Sqrt[x^2 + a], x],
    _Failure
  ]];

(* Explicit "Parameters" -> {} on a parametric integrand should reject.      *)
tassert["empty Parameters on parametric integrand rejects",
  MatchQ[
    IntegrateTrager[1/Sqrt[x^2 + a], x, "Parameters" -> {}],
    _Failure
  ]];

(* Parameter equal to x must be rejected.                                    *)
tassertFailure["Parameters cannot include x",
  "BadInput",
  IntegrateTrager[1/Sqrt[x^2 + 1], {x, y, y^2 == x^2 + 1},
                  "Parameters" -> {x}]];

(* Parameter equal to y must be rejected.                                    *)
tassertFailure["Parameters cannot include y",
  "BadInput",
  IntegrateTrager[1/y, {x, y, y^2 == x^2 + 1},
                  "Parameters" -> {y}]];

(* Duplicate parameters must be rejected.                                    *)
tassertFailure["duplicate parameters rejected",
  "BadInput",
  IntegrateTrager[1/y, {x, y, y^2 == x^2 + 1},
                  "Parameters" -> {a, a}]];

tsection["tier 1: single parameter, square root"];

tassert["1/Sqrt[x^2+a]",
  parametricVerify[1/y, 2, x^2 + a, x, y, {a}]["ok"]];
tassert["1/(x Sqrt[x^2+a])",
  parametricVerify[1/(x y), 2, x^2 + a, x, y, {a}]["ok"]];
tassert["x/Sqrt[x^2+a]",
  parametricVerify[x/y, 2, x^2 + a, x, y, {a}]["ok"]];
tassert["1/Sqrt[a x^2 + 1]",
  parametricVerify[1/y, 2, a x^2 + 1, x, y, {a}]["ok"]];
tassert["1/Sqrt[x^2 + a^2]",
  parametricVerify[1/y, 2, x^2 + a^2, x, y, {a}]["ok"]];
tassert["1/Sqrt[x^2 - a]",
  parametricVerify[1/y, 2, x^2 - a, x, y, {a}]["ok"]];
tassert["x/Sqrt[x^4 + a]",
  parametricVerifySurface[x/Sqrt[x^4 + a], x, {a}]["ok"]];

tsection["tier 1: pure algebraic Hermite-only cases"];

tassert["x/Sqrt[x^2 + a] (pure algebraic)",
  parametricVerify[x/y, 2, x^2 + a, x, y, {a}]["ok"]];
tassert["Sqrt[x^2 + a]",
  parametricVerifySurface[Sqrt[x^2 + a], x, {a}]["ok"]];
tassert["x^2/Sqrt[x^2 + a]",
  parametricVerifySurface[x^2/Sqrt[x^2 + a], x, {a}]["ok"]];

tsection["tier 2: mixed algebraic + log"];

tassert["(x+1)/Sqrt[x^2 + a]",
  parametricVerifySurface[(x + 1)/Sqrt[x^2 + a], x, {a}]["ok"]];

tsection["tier 2b: two parameters (residue field algebraic over Q(a,b))"];

(* These exercise the case where the Rothstein-Trager residues are NOT in   *)
(* ℚ(a,b) but in an algebraic extension of it (here Sqrt[a + b^2]). The    *)
(* HNF and normalize-at-infinity steps must canonicalise rational           *)
(* functions in (a, b, Sqrt[a+b^2]) on each iteration to avoid expression  *)
(* blow-up.                                                                  *)

tassert["1/((x-b) Sqrt[x^2 + a])",
  parametricVerifySurface[1/((x - b) Sqrt[x^2 + a]), x, {a, b}]["ok"]];
tassert["1/Sqrt[a x^2 + b]",
  parametricVerifySurface[1/Sqrt[a x^2 + b], x, {a, b}]["ok"]];

tsection["tier 3: name-collision robustness"];

(* Internal Phase 2 shift point is named `a` in Module locals; verify this *)
(* does not collide with a user parameter actually named `a`.              *)
tassert["user parameter 'a' coexists with internal shift symbol",
  parametricVerify[1/y, 2, x^2 + a, x, y, {a}]["ok"]];

(* Parameter named z must not collide with the internal Phase 2 frame      *)
(* variable. We pass an explicit relation to keep z out of the radical so  *)
(* the surface form does not auto-detect it.                                *)
tassert["user parameter named 'z' does not collide with internal z-frame",
  parametricVerify[z/y, 2, x^2 + 1, x, y, {z}]["ok"]];

tsection["tier 4: out-of-scope rejections under parameters"];

(* Algebraic extension over a parameter (Sqrt[a] is not in ℚ(a)) must be *)
(* rejected as out-of-scope, not silently accepted.                       *)
tassertFailure["Sqrt[a] in radicand",
  "UnsupportedBaseField",
  IntegrateTrager[1/Sqrt[x^2 + Sqrt[a]], x]];

(* Genus-1 curve with parameter is still PositiveGenus (gated by MaxGenus). *)
tassertFailure["1/Sqrt[x^3 + a] is positive genus",
  "PositiveGenus",
  IntegrateTrager[1/Sqrt[x^3 + a], x, "MaxGenus" -> 0]];

tSummary[];
