(* ::Package:: *)

(* ::Title:: *)
(* torsionIfCan -- divisor-class torsion order + principal generator *)

(* ::Text:: *)
(* Trager 1984 Ch 6 §2 ("Good Reduction") and §3 ("Algorithms for Divisor *)
(* reduction"). Determines the torsion order of a degree-0 divisor in the *)
(* Jacobian and produces a principal generator when one exists.            *)
(*                                                                           *)
(* For a degree-0 divisor D on a genus-g curve, D represents a class in    *)
(* the Jacobian Pic^0(C). D is principal (i.e. "torsion of order 1") iff   *)
(* genus(C) = 0 OR D's class is trivial in a positive-genus Jacobian.      *)
(*                                                                           *)
(* torsionIfCan searches for the smallest k in [1, maxOrder] such that    *)
(* k D is principal. If such k is found, it returns                         *)
(*                                                                           *)
(*   <|"order" -> k, "function" -> v|>      with (v) = k D                *)
(*                                                                           *)
(* and the corresponding log term is  (1/k) log(v) with coefficient        *)
(* (residue) from Phase 4.                                                   *)
(*                                                                           *)
(* If no principal k D is found within the search bound, the divisor is   *)
(* (almost certainly) non-torsion, which in turn implies the integrand is *)
(* non-elementary -- we return a "failed" indicator that the caller       *)
(* promotes to Failure["NonElementary", ...].                                *)
(*                                                                           *)
(* TORSION BOUND.                                                            *)
(* Mazur's theorem (1977) gives a bound of 12 for torsion orders on       *)
(* elliptic curves over Q. For higher genus a computable bound exists      *)
(* via reduction mod good primes (Trager Ch 6 §2), but a conservative      *)
(* constant of 12 covers almost all practically-encountered cases in the   *)
(* simple-radical genus-1 regime. The caller may override via the         *)
(* MaxTorsionOrder option of IntegrateTrager.                                *)

ClearAll[torsionIfCan];

Options[torsionIfCan] = {
  MaxOrder -> 12,
  Verify   -> None   (* function AF-element ↦ True/False/$Unknown, or None *)
};

torsionIfCan[div_?divisorQ, basis_?basisDescriptorQ, y_Symbol,
             OptionsPattern[]] := Catch[Module[
  {maxOrd, currDiv, result, k, verifyFn, verifierFor},

  maxOrd   = OptionValue[MaxOrder];
  verifyFn = OptionValue[Verify];

  verifierFor[kVal_] :=
    If[verifyFn === None, None, Function[v, verifyFn[v, kVal]]];

  result = findPrincipalGenerator[div, basis, y, Verify -> verifierFor[1]];
  If[!tragerFailureQ[result],
    Throw[<|"order" -> 1, "function" -> result|>]
  ];

  currDiv = div;
  Do[
    currDiv = divisorAdd[currDiv, div, basis];
    If[tragerFailureQ[currDiv], Throw[currDiv]];

    result = findPrincipalGenerator[currDiv, basis, y,
                                    Verify -> verifierFor[k]];
    If[!tragerFailureQ[result],
      Throw[<|"order" -> k, "function" -> result|>]
    ],
    {k, 2, maxOrd}
  ];

  <|"order" -> "failed",
    "reason" -> "no principal k * D found within MaxOrder = " <> ToString[maxOrd],
    "lastResult" -> result|>
]];

(* Convenience constructor: a verifier for divDiff = div1 - div2 that calls  *)
(* verifyPrincipalGeneratorForPair at each k. Used by constructLogTerms.     *)

ClearAll[pairVerifier];
pairVerifier[div1_?divisorQ, div2_?divisorQ, basis_?basisDescriptorQ,
             y_Symbol] :=
  Function[{v, kVal},
    verifyPrincipalGeneratorForPair[v, div1, div2, kVal, basis, y]
  ];
