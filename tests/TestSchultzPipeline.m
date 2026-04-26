(* ::Package:: *)

(* ::Title:: *)
(* Tests for the SchultzPlan.md §S.7 pipeline wiring. *)

(* The Schultz path replaces Phases 2-6 of the default IntegrateTrager     *)
(* pipeline. Per SchultzPlan.md §S.7 acceptance, this suite:                *)
(*   1. Confirms the option dispatches to the Schultz code path.            *)
(*   2. Cross-checks Tier-1 inputs that the current S.6 implementation     *)
(*      handles (algebraic-only and finite-residue cases) against the      *)
(*      default pipeline -- the antiderivatives must match modulo the      *)
(*      logarithm constant.                                                  *)
(*   3. Documents the §S.6.2 deferred path: inputs whose only residues are *)
(*      at infinity currently return Failure[NonElementary] with the       *)
(*      "Schultz" Method tag, until Lemma 4.2 / 5.5 are implemented.        *)
(*                                                                          *)
(* All three behaviour categories are pinned down here so future S.6.2     *)
(* progress can be measured by which "deferred" tests start producing      *)
(* elementary antiderivatives.                                               *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

(* Helper: differentiate `result` and check `D[result, x] == integrand`     *)
(* on the curve y^n = g (i.e. after substituting y -> g^(1/n)). Returns    *)
(* True when the difference simplifies to zero and Numerator[Together[...]]*)
(* is zero. Used for cross-checking Schultz output against the integrand.  *)

ClearAll[derivativeMatchesQ];
derivativeMatchesQ[result_, integrand_, x_, ySym_, gExpr_, n_] := Module[
  {yRoot, diff, simp},
  yRoot = gExpr^(1/n);
  diff = D[result /. ySym -> yRoot, x] - (integrand /. ySym -> yRoot);
  simp = Together[diff];
  TrueQ[simp === 0] || zeroQ[Numerator[simp]] ||
    TrueQ[Simplify[simp] === 0]
];

(* ::Section:: *)
(* Option exists and is False by default.                                  *)

tsection["Option \"Schultz\" defaults to False"];

tassert["Options[IntegrateTrager] contains \"Schultz\" -> False",
  ("Schultz" /. Options[IntegrateTrager]) === False];

(* ::Section:: *)
(* Algebraic-only Tier-1 inputs: schultzHermiteReduce absorbs the entire   *)
(* integrand into algPart, and the residual log-term construction returns *)
(* {}. Cross-check: result agrees with the default pipeline output.        *)

tsection["Algebraic-only: x / sqrt(x^2 + 1)"];

Module[{integrand, schultzRes, defaultRes},
  integrand = x / Sqrt[x^2 + 1];
  schultzRes = IntegrateTrager[integrand, x, "Schultz" -> True];
  defaultRes = IntegrateTrager[integrand, x];
  tassert["Schultz returns a non-Failure",
    !MatchQ[schultzRes, _Failure]];
  tassertEqual["Schultz output matches default pipeline",
    defaultRes, schultzRes];
  tassert["Derivative of Schultz output matches integrand",
    derivativeMatchesQ[schultzRes, integrand, x, y, x^2 + 1, 2]];
];

tsection["Algebraic-only: x / sqrt(x^2 - 1)"];

Module[{integrand, schultzRes, defaultRes},
  integrand = x / Sqrt[x^2 - 1];
  schultzRes = IntegrateTrager[integrand, x, "Schultz" -> True];
  defaultRes = IntegrateTrager[integrand, x];
  tassert["Schultz returns a non-Failure",
    !MatchQ[schultzRes, _Failure]];
  tassertEqual["Schultz output matches default pipeline",
    defaultRes, schultzRes];
];

tsection["Algebraic-only: pure power 1/x^(1/3)"];

Module[{integrand, schultzRes, defaultRes},
  integrand = 1 / x^(1/3);
  schultzRes = IntegrateTrager[integrand, x, "Schultz" -> True];
  defaultRes = IntegrateTrager[integrand, x];
  tassert["Schultz returns a non-Failure",
    !MatchQ[schultzRes, _Failure]];
  tassertEqual["Schultz output matches default pipeline (modulo simplification)",
    defaultRes, schultzRes];
];

tsection["Algebraic-only: pure power 1/x^(2/3)"];

Module[{integrand, schultzRes},
  integrand = 1 / x^(2/3);
  schultzRes = IntegrateTrager[integrand, x, "Schultz" -> True];
  tassertEqual["Schultz integrates to 3 x^(1/3)",
    3 x^(1/3), schultzRes];
];

(* ::Section:: *)
(* Finite-residue log inputs: Hermite remainder is non-zero, residues at  *)
(* infinity vanish (eq. 4.11 = 0), schultzConstructLogTerms produces log  *)
(* terms via the principal-generator + torsion search (delegated to       *)
(* TragerLogTerms via the SchultzLogTerms bridge, S.6.1).                  *)

tsection["Finite-residue log: 1/(x sqrt(x^2 - 1))"];

Module[{integrand, schultzRes, defaultRes},
  integrand = 1 / (x * Sqrt[x^2 - 1]);
  schultzRes = IntegrateTrager[integrand, x, "Schultz" -> True];
  defaultRes = IntegrateTrager[integrand, x];
  tassert["Schultz returns a non-Failure",
    !MatchQ[schultzRes, _Failure]];
  tassert["Schultz output contains a Log term",
    !FreeQ[schultzRes, Log]];
  tassert["Derivative matches the integrand on the curve y^2 = x^2 - 1",
    derivativeMatchesQ[schultzRes, integrand, x, y, x^2 - 1, 2]];
  tassertEqual["Schultz output matches default pipeline",
    defaultRes, schultzRes];
];

tsection["Finite-residue log: 1/(x sqrt(x^2 + 1))"];

Module[{integrand, schultzRes},
  integrand = 1 / (x * Sqrt[x^2 + 1]);
  schultzRes = IntegrateTrager[integrand, x, "Schultz" -> True];
  tassert["Schultz returns a non-Failure",
    !MatchQ[schultzRes, _Failure]];
  tassert["Schultz output contains a Log term",
    !FreeQ[schultzRes, Log]];
  tassert["Derivative matches the integrand on the curve y^2 = x^2 + 1",
    derivativeMatchesQ[schultzRes, integrand, x, y, x^2 + 1, 2]];
];

(* ::Section:: *)
(* Inputs whose only residues are at infinity: handled directly by the unified *)
(* Lemma 4.1 path (S.6.1), no longer deferred to the §S.6.2 fail-in-style stub.*)
(* The Lemma 4.1 R(D) construction works uniformly across finite + infinity   *)
(* residues; the §S.6.2 path is reserved for genuinely non-elementary inputs. *)

tsection["1/sqrt(x^2 + 1) -- residues at infinity, integrates to arcsinh"];

Module[{integrand, schultzRes},
  integrand = 1 / Sqrt[x^2 + 1];
  schultzRes = IntegrateTrager[integrand, x, "Schultz" -> True];
  tassert["Schultz returns a non-Failure",
    !MatchQ[schultzRes, _Failure]];
  tassert["Schultz output contains a Log term",
    !FreeQ[schultzRes, Log]];
  tassert["Derivative matches the integrand",
    zeroQ[Numerator[Together[D[schultzRes, x] - integrand]]]];
];

tsection["1/sqrt(1 - x^2) -- residues at infinity, integrates to arcsin"];

Module[{integrand, schultzRes},
  integrand = 1 / Sqrt[1 - x^2];
  schultzRes = IntegrateTrager[integrand, x, "Schultz" -> True];
  tassert["Schultz returns a non-Failure",
    !MatchQ[schultzRes, _Failure]];
  tassert["Derivative matches the integrand",
    zeroQ[Numerator[Together[D[schultzRes, x] - integrand]]]];
];

(* ::Section:: *)
(* §S.0 contract: under "Schultz" -> True, "LogTermsMethod" is silently  *)
(* ignored (the Schultz path supplies its own log-term construction).    *)

tsection["§S.0 contract: \"LogTermsMethod\" is ignored under Schultz path"];

Module[{integrand, withTrager, withMiller, withInvalid},
  integrand = 1 / (x * Sqrt[x^2 - 1]);
  withTrager  = IntegrateTrager[integrand, x,
    "Schultz" -> True, "LogTermsMethod" -> "Trager"];
  withMiller  = IntegrateTrager[integrand, x,
    "Schultz" -> True, "LogTermsMethod" -> "Miller"];
  withInvalid = IntegrateTrager[integrand, x,
    "Schultz" -> True, "LogTermsMethod" -> "this-is-bogus"];
  tassertEqual["Trager and Miller LogTermsMethod produce identical Schultz output",
    withTrager, withMiller];
  tassertEqual["bogus LogTermsMethod is ignored (no BadInput failure)",
    withTrager, withInvalid];
];

(* ::Section:: *)
(* Diagnostics expose the Schultz subkeys so callers can introspect the *)
(* pipeline state.                                                       *)

tsection["Diagnostics surface the Schultz pipeline state"];

Module[{res, diag, sub},
  res = IntegrateTrager[1/(x Sqrt[x^2 - 1]), x,
    "Schultz" -> True, "Diagnostics" -> True, "LogTermsMethod" -> "Trager"];
  tassert["Diagnostics return form is an association",
    AssociationQ[res] && KeyExistsQ[res, "Result"] &&
      KeyExistsQ[res, "Diagnostics"]];
  diag = res["Diagnostics"];
  tassert["Diagnostics contain the \"schultz\" subtree",
    KeyExistsQ[diag, "schultz"]];
  sub = diag["schultz"];
  tassert["Schultz subtree carries schultzHermite key",
    AssociationQ[sub] && KeyExistsQ[sub, "schultzHermite"]];
  tassert["Schultz subtree carries schultzLogTerms key",
    KeyExistsQ[sub, "schultzLogTerms"]];
  tassert["Schultz subtree carries schultzShift key (identity record)",
    KeyExistsQ[sub, "schultzShift"]];
  tassert["schultzShift is the identity record (skipped -> True)",
    sub["schultzShift"]["skipped"] === True];
];

tSummary[];
