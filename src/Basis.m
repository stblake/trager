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

buildIntegralBasis[n_Integer /; n >= 2, g_, x_Symbol] := Module[
  {factors, pairs, d},
  factors = FactorList[g];
  pairs = Rest[factors];   (* first entry is the constant factor *)
  d = Table[
    Times @@ (#[[1]]^Floor[i * #[[2]] / n] & /@ pairs),
    {i, 0, n - 1}
  ];
  <|
    "n" -> n,
    "g" -> g,
    "d" -> d,
    "pFactors" -> pairs,
    "x" -> x
  |>
];
