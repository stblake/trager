(* ::Package:: *)

(* ::Title:: *)
(* Tests for buildIntegralBasis *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

tsection["buildIntegralBasis: quadratic cases (n=2)"];

Module[{b},
  b = buildIntegralBasis[2, x^2 + 1, x];
  tassert["is a basis descriptor", basisDescriptorQ[b]];
  tassertEqual["n = 2", 2, b["n"]];
  tassertEqual["d[0] = 1", 1, b["d"][[1]]];
  tassertEqual["d[1] = 1", 1, b["d"][[2]]];
  tassertEqual["pFactors", {{x^2 + 1, 1}}, b["pFactors"]];
];

Module[{b},
  b = buildIntegralBasis[2, x*(x - 1), x];
  (* pairs {{x, 1}, {x-1, 1}}; d[1] = x^0 (x-1)^0 = 1 *)
  tassertEqual["n=2, g=x(x-1): d[0]=1", 1, b["d"][[1]]];
  tassertEqual["n=2, g=x(x-1): d[1]=1", 1, b["d"][[2]]];
];

tsection["buildIntegralBasis: cubic cases (n=3)"];

Module[{b},
  b = buildIntegralBasis[3, x, x];
  tassertEqual["y^3=x: d[0]=1", 1, b["d"][[1]]];
  tassertEqual["y^3=x: d[1]=1", 1, b["d"][[2]]];
  tassertEqual["y^3=x: d[2]=1", 1, b["d"][[3]]];
];

Module[{b},
  b = buildIntegralBasis[3, x^2, x];
  (* d[i] = x^Floor[2i/3] = {1, 1, x} *)
  tassertEqual["y^3=x^2: d[0]=1", 1, b["d"][[1]]];
  tassertEqual["y^3=x^2: d[1]=1", 1, b["d"][[2]]];
  tassertEqual["y^3=x^2: d[2]=x", x, b["d"][[3]]];
];

Module[{b},
  b = buildIntegralBasis[3, x^2*(1 - x), x];
  (* pairs {{-1,1}? no -- -1 is in the leading; FactorList gives {{-1,1},{x,2},{x-1,1}} *)
  (* So pairs = {{x,2}, {x-1,1}}                                            *)
  (* d[0] = 1                                                               *)
  (* d[1] = x^Floor[2/3] * (x-1)^Floor[1/3] = 1                             *)
  (* d[2] = x^Floor[4/3] * (x-1)^Floor[2/3] = x * 1 = x                     *)
  tassertEqual["y^3=x^2(1-x): d[0]", 1, b["d"][[1]]];
  tassertEqual["y^3=x^2(1-x): d[1]", 1, b["d"][[2]]];
  tassertEqual["y^3=x^2(1-x): d[2]", x, b["d"][[3]]];
];

tsection["buildIntegralBasis: quartic case (n=4)"];

Module[{b},
  b = buildIntegralBasis[4, x^3, x];
  (* d[i] = x^Floor[3i/4] = {1, 1, x, x^2} *)
  tassertEqual["y^4=x^3: d[0]", 1, b["d"][[1]]];
  tassertEqual["y^4=x^3: d[1]", 1, b["d"][[2]]];
  tassertEqual["y^4=x^3: d[2]", x, b["d"][[3]]];
  tassertEqual["y^4=x^3: d[3]", x^2, b["d"][[4]]];
];

tsection["buildIntegralBasis: structural invariants"];

Module[{b, d, n},
  (* d[n-1] should be the LCM of all d[i]. Plan-critical for phase 3.     *)
  b = buildIntegralBasis[4, x^3, x];
  d = b["d"]; n = b["n"];
  tassertEqual["d[n-1] = LCM of all d[i], n=4 example",
    PolynomialLCM @@ d, d[[-1]]];
];

Module[{b, d, n},
  b = buildIntegralBasis[6, x^4 (x + 1)^5, x];
  (* pairs {{x,4}, {x+1,5}}                                                *)
  (* d[i] = x^Floor[4i/6] * (x+1)^Floor[5i/6]                              *)
  d = b["d"]; n = b["n"];
  tassertEqual["d[n-1] = LCM of all d[i], n=6 example",
    PolynomialLCM @@ d, d[[-1]]];
  (* Spot check individual d[i] *)
  tassertEqual["d[0]=1", 1, d[[1]]];
  tassertEqual["d[1]= x^0 (x+1)^0 =1", 1, d[[2]]];
  tassertEqual["d[2]= x^1 (x+1)^1 = x(x+1)",
    Expand[x*(x + 1)], Expand[d[[3]]]];
  tassertEqual["d[3]= x^2 (x+1)^2",
    Expand[x^2*(x + 1)^2], Expand[d[[4]]]];
  tassertEqual["d[4]= x^2 (x+1)^3",
    Expand[x^2*(x + 1)^3], Expand[d[[5]]]];
  tassertEqual["d[5]= x^3 (x+1)^4",
    Expand[x^3*(x + 1)^4], Expand[d[[6]]]];
];

Module[{b, d, n, i},
  (* Monotonic divisibility: d[i] | d[i+1] for all i. *)
  b = buildIntegralBasis[5, x^2 (x - 1)^3 (x + 2)^4, x];
  d = b["d"]; n = b["n"];
  Do[
    tassert["d[" <> ToString[i] <> "] divides d[" <> ToString[i + 1] <> "]",
      PolynomialQ[Cancel[d[[i + 2]] / d[[i + 1]]], x]
    ],
    {i, 0, n - 2}
  ];
];

(* ::Section:: *)
(* Schultz 2015 infinity exponents δ_i (Sch §4, Lemma 4.1).                  *)
(* See SchultzPlan.md §S.1. The sum rule δ_1 + … + δ_n = n + c(g − 1) is the *)
(* defining identity we pin regression tests against.                         *)

tsection["buildIntegralBasis: Schultz infinity exponents δ_i"];

Module[{b},
  b = buildIntegralBasis[2, x^2 + 1, x];
  (* y^2 = x^2 + 1, g_curve = 0, c = 1, so δ-sum = 2 + 0 = 2. deg(g)=2,      *)
  (* m̃ = 1, so ord_∞(y) = −1, i.e. at each ∞-place y behaves like x^1. So  *)
  (* δ_0 = 0 (the constant 1 is integral at infinity),                       *)
  (* δ_1 = ⌈2/2 − 0⌉ = 1 (y needs 1/x to be integral at infinity).          *)
  tassertEqual["δ for y^2 = x^2+1 is {0, 1}", {0, 1}, b["deltas"]];
  tassertEqual["c for y^2 = x^2+1 is 1", 1, b["c"]];
  tassertEqual["δ-sum rule for y^2 = x^2+1 (genus 0)",
    b["n"] + b["c"]*(0 - 1), Total[b["deltas"]]];
];

Module[{b},
  b = buildIntegralBasis[2, x^3 + 1, x];
  (* y^2 = x^3 + 1, elliptic (genus 1). ord_∞(y) = −3/gcd(2,3) · 1 = hmm    *)
  (* with gcd(2,3) = 1, ñ = 2, m̃ = 3. ord_∞(y) = −3, ord_∞(x) = −2,        *)
  (* so w_1 = y has scaled ord −3. Need δ_1 = ⌈3/2⌉ = 2.                   *)
  tassertEqual["δ for y^2 = x^3+1 is {0, 2}", {0, 2}, b["deltas"]];
  (* Sum rule: 0 + 2 = 2 = n + c(g−1) = 2 + (1−1) = 2.                      *)
  tassertEqual["δ-sum rule for y^2 = x^3+1 (genus 1)",
    b["n"] + b["c"]*(1 - 1), Total[b["deltas"]]];
];

Module[{b},
  b = buildIntegralBasis[3, x, x];
  (* y^3 = x, genus 0. n = 3, deg(g) = 1, gcd = 1. ñ = 3, m̃ = 1.           *)
  (* δ_0 = 0, δ_1 = ⌈1/3⌉ = 1, δ_2 = ⌈2/3⌉ = 1. Sum = 2.                    *)
  tassertEqual["δ for y^3 = x is {0, 1, 1}", {0, 1, 1}, b["deltas"]];
  tassertEqual["δ-sum rule for y^3 = x (genus 0)",
    b["n"] + b["c"]*(0 - 1), Total[b["deltas"]]];
];

Module[{b},
  b = buildIntegralBasis[4, x^3, x];
  (* y^4 = x^3, genus 0 (by computeGenus formula: 1 + (1/2)(1·(4−1)+(4−1)−8)  *)
  (* = 1 − 1 = 0). n = 4, deg(g) = 3. d_i = x^⌊3i/4⌋ = {1, 1, x, x^2}.       *)
  (* δ_0 = 0;                                                                  *)
  (* δ_1 = ⌈3/4 − 0⌉ = 1;                                                    *)
  (* δ_2 = ⌈6/4 − 1⌉ = 1;                                                    *)
  (* δ_3 = ⌈9/4 − 2⌉ = 1.                                                    *)
  (* Sum = 3 = 4 + (0 − 1). ✓                                                *)
  tassertEqual["δ for y^4 = x^3 is {0, 1, 1, 1}", {0, 1, 1, 1}, b["deltas"]];
  tassertEqual["δ-sum rule for y^4 = x^3 (genus 0)",
    b["n"] + b["c"]*(0 - 1), Total[b["deltas"]]];
];

Module[{b, gen},
  (* y^5 = x^2(x−1)^3(x+2)^4 -- multi-factor sanity check.                   *)
  b = buildIntegralBasis[5, x^2 (x - 1)^3 (x + 2)^4, x];
  (* All δ_i ≥ 0. *)
  tassert["all δ_i ≥ 0", AllTrue[b["deltas"], # >= 0 &]];
  (* Each δ_i is an integer. *)
  tassert["all δ_i integer", AllTrue[b["deltas"], IntegerQ]];
  (* Sum rule: with c = 1, sum = n + (g − 1). *)
  (* deg g = 9; using computeGenus (reduceIrreducibility will leave this   *)
  (* as-is because exponents mod n are 2,3,4 and gcd(5,2,3,4) = 1):         *)
  (* genus = 1 + (1/2)(1·(5-1) + 1·(5-1) + 1·(5-1) + (5 - gcd(5,9)) − 2·5) *)
  (*       = 1 + (1/2)(4 + 4 + 4 + 4 − 10) = 1 + 3 = 4.                    *)
  gen = computeGenus[5, x^2 (x - 1)^3 (x + 2)^4, x];
  tassertEqual["δ-sum rule for y^5 multi-factor",
    b["n"] + b["c"]*(gen - 1), Total[b["deltas"]]];
];

Module[{b, gen, gExpr},
  (* Tier 1b elliptic: y^2 = x^3 + p x -- just shape, not integrated here.   *)
  (* Base field Q with no parameters, genus 1, δ-sum must be 2.              *)
  gExpr = x^3 + x;
  b = buildIntegralBasis[2, gExpr, x];
  gen = computeGenus[2, gExpr, x];
  tassertEqual["δ-sum rule for y^2 = x^3 + x (genus 1)",
    b["n"] + b["c"]*(gen - 1), Total[b["deltas"]]];
];

tSummary[];
