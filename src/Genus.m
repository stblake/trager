(* ::Package:: *)

(* ::Title:: *)
(* Phase 0 -- computeGenus *)

(* ::Text:: *)
(* See TragerPlan.md Section 2.                                              *)
(*                                                                           *)
(* Computes the genus of the curve y^n = g(x) using Riemann-Hurwitz applied  *)
(* to the Kummer cover (x, y) -> x. The input (n, g) is assumed already     *)
(* reduced by reduceIrreducibility: every irreducible factor of g appears   *)
(* with exponent in {1, 2, ..., n-1}.                                        *)
(*                                                                           *)
(* Formula:                                                                  *)
(*   2 g_curve - 2 = -2 n + Sum_i m_i * (n - gcd(n, e_i)) + (n - gcd(n, deg g)) *)
(* where g = c * prod p_i^e_i with p_i distinct irreducible of degree m_i.   *)

ClearAll[computeGenus];

computeGenus[n_Integer /; n >= 2, g_, x_Symbol] := Module[
  {factors, pairs, finiteRam, degG, infinityRam, twoGMinus2},

  (* If the radicand is a non-zero constant, the curve is degenerate; we    *)
  (* return -1 to signal "no curve". Callers should have caught this in     *)
  (* validateInput / reduceIrreducibility, but returning a sentinel avoids  *)
  (* silent garbage.                                                         *)
  If[FreeQ[g, x], Return[-1]];

  factors = FactorList[g];
  pairs = Rest[factors];   (* constant factor lives at factors[[1]] *)

  (* finite ramification: sum over irreducible factors of g *)
  finiteRam = Total[
    (Exponent[#[[1]], x] * (n - GCD[n, #[[2]]])) & /@ pairs
  ];

  degG = Exponent[g, x];
  infinityRam = n - GCD[n, degG];

  twoGMinus2 = -2 n + finiteRam + infinityRam;
  twoGMinus2 / 2 + 1
];

computeGenus[n_, g_, x_Symbol] := -1 (* malformed input, signal "no curve" *);
