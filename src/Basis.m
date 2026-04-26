(* ::Package:: *)

(* ::Title:: *)
(* Phase 1 -- buildIntegralBasis *)

(* ::Text:: *)
(* See TragerPlan.md Section 3.                                              *)
(*                                                                           *)
(* Builds the Trager integral basis for a simple radical extension          *)
(* Q(x)[y]/(y^n - g) in reduced form (0 < e_j < n for every irreducible     *)
(* factor p_j^e_j of g).                                                     *)
(*                                                                           *)
(*   d[i] = prod_j p_j^Floor[i * e_j / n]                                    *)
(*   w[i] = y^i / d[i]              for i = 0, ..., n-1                     *)
(*                                                                           *)
(* The list d is monotonically divisible: d[i] | d[i+1], so d[n-1] is the   *)
(* LCM of the full set. Phase 3 relies on this to construct its common      *)
(* denominator E = n * g * d[n-1].                                           *)

ClearAll[buildIntegralBasis];

(* The extra keys "deltas" and "c" are the Schultz 2015 infinity attributes   *)
(* (Sch §4, Lemma 4.1). At each infinity place on y^n = g with ramification  *)
(* ñ = n/gcd(n, deg g) and ord_∞(y) = −m̃ = −deg(g)/gcd(n, deg g), the       *)
(* order of w_i = y^i / d_i(x) is                                             *)
(*     ord_∞(w_i) = −i·m̃ + ñ·deg(d_i).                                      *)
(* The smallest nonnegative integer δ_i for which x^{−δ_i} w_i is integral   *)
(* at every infinity place is                                                 *)
(*     δ_i = max(0, ⌈i·deg(g)/n − deg(d_i)⌉).                                *)
(* Equivalently δ_i = ⌈Σ_j deg(p_j) · frac(i·e_j/n)⌉ ≥ 0. The sum rule       *)
(*     δ_0 + δ_1 + ⋯ + δ_{n−1} = n + c·(genus − 1)                          *)
(* (Sch Lemma 4.1 last display) is a single-line regression check. For a     *)
(* reduced simple radical y^n = g over ℚ(params) the constant-field degree  *)
(* c (Sch eq. 4.5) is always 1 — there are no extra constants in K = k(x, y)*)
(* beyond those already in k.                                                *)

buildIntegralBasis[n_Integer /; n >= 2, g_, x_Symbol] := Module[
  {factors, pairs, d, mDeg, degDi, deltas},
  factors = FactorList[g];
  pairs = Rest[factors];   (* first entry is the constant factor *)
  d = Table[
    Times @@ (#[[1]]^Floor[i * #[[2]] / n] & /@ pairs),
    {i, 0, n - 1}
  ];
  mDeg = Exponent[g, x];
  degDi = Exponent[#, x] & /@ d;
  deltas = Table[Max[0, Ceiling[i * mDeg / n - degDi[[i + 1]]]], {i, 0, n - 1}];
  <|
    "n" -> n,
    "g" -> g,
    "d" -> d,
    "pFactors" -> pairs,
    "x" -> x,
    "deltas" -> deltas,
    "c" -> 1
  |>
];
