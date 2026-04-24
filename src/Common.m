(* ::Package:: *)

(* ::Title:: *)
(* Common utilities: type predicates, Failure helpers, diagnostic messages *)

(* ::Section:: *)
(* Diagnostic message channels *)

(* Declared against IntegrateTrager, the user-facing entry point. All         *)
(* diagnostic channels are non-fatal; they are printed only when the user     *)
(* supplies "Verbose" -> True, and attached to metadata when "Diagnostics"    *)
(* -> True.                                                                   *)

IntegrateTrager::autoreduce =
  "Binomial y^`1` - g factors over the algebraic closure; auto-reducing to \
y^`2` = `3`.";
IntegrateTrager::scale =
  "Rational radicand denominator cleared by substituting y -> q*y with q = `1`.";
IntegrateTrager::extension =
  "Residues require the algebraic number field `1`.";
IntegrateTrager::hermite =
  "Hermite reduction completed: `1` iterations, square-free denominator `2`.";
IntegrateTrager::genus =
  "Curve has genus `1`; out of scope (this implementation handles genus 0 only).";
IntegrateTrager::nonelementary =
  "Integrand on genus-`1` curve is provably non-elementary (residual after \
verification: `2`).";
IntegrateTrager::incomplete =
  "Integration path not yet implemented: `1`. This is a known gap in the \
current Trager port; see Subreason metadata for details.";
IntegrateTrager::torsion =
  "Residue divisor has torsion order `1` in Pic^0 (genus `2`).";
IntegrateTrager::principal =
  "Found principal generator for divisor via K[x]-module reduction at infinity.";

(* ::Section:: *)
(* Failure constructors *)

(* All Failure objects carry an association. We use a single entry point to *)
(* keep the metadata keys consistent and enable downstream caller inspection.*)

tragerFailure[tag_String, metadata_Association: <||>] :=
  Failure[tag, Join[<|"MessageTemplate" -> tag|>, metadata]];

tragerFailure[tag_String, rule_Rule, more___Rule] :=
  tragerFailure[tag, Association[rule, more]];

(* Predicate: is this value one of our Failure objects? *)
tragerFailureQ[x_] := MatchQ[x, _Failure];

(* ::Section:: *)
(* Type predicates for internal data *)

(* An "AF element" represents an element of K(x, y) with y^n = g. The        *)
(* internal Association schema must be kept in sync with §0 of the plan.     *)

afElementQ[af_Association] :=
  KeyExistsQ[af, "Type"] && af["Type"] === "AF" &&
  KeyExistsQ[af, "Coeffs"] && ListQ[af["Coeffs"]] &&
  KeyExistsQ[af, "n"] && IntegerQ[af["n"]] && af["n"] >= 2 &&
  KeyExistsQ[af, "g"] && Length[af["Coeffs"]] === af["n"];
afElementQ[_] := False;

(* Basis descriptor produced by buildIntegralBasis. *)

basisDescriptorQ[b_Association] :=
  KeyExistsQ[b, "n"] && IntegerQ[b["n"]] && b["n"] >= 2 &&
  KeyExistsQ[b, "g"] &&
  KeyExistsQ[b, "d"] && ListQ[b["d"]] && Length[b["d"]] === b["n"] &&
  KeyExistsQ[b, "pFactors"] && KeyExistsQ[b, "x"];
basisDescriptorQ[_] := False;

(* Divisor descriptor: locally-principal representation per Trager Ch 5 §3.  *)
(* <|"Type"->"Divisor", "h"->AF-element, "A"->polynomial-in-x|>              *)
(* Invariant: ord_P(h) = ord_P(D) at all places P lying over roots of A;    *)
(*            ord_P(D) = 0 at places away from roots of A.                   *)

divisorQ[d_Association] :=
  KeyExistsQ[d, "Type"] && d["Type"] === "Divisor" &&
  KeyExistsQ[d, "h"] && afElementQ[d["h"]] &&
  KeyExistsQ[d, "A"];
divisorQ[_] := False;

(* ::Subsection:: *)
(* Incomplete-implementation helper                                          *)
(*                                                                           *)
(* Returns a Failure["ImplementationIncomplete", ...] with a precise         *)
(* Subreason tag that callers can match against. Use this instead of the    *)
(* generic tragerFailure when documenting a known gap in our Trager port.   *)

incompleteFailure[subreason_String, metadata_Association: <||>] :=
  tragerFailure["ImplementationIncomplete",
    Join[<|"Subreason" -> subreason|>, metadata]];

incompleteFailure[subreason_String, rule_Rule, more___Rule] :=
  incompleteFailure[subreason, Association[rule, more]];

(* ::Section:: *)
(* Extension-generator detection                                             *)
(*                                                                           *)
(* Scans an arbitrary expression (including AF-element coefficient lists,    *)
(* polynomials, or divisor descriptors) for embedded algebraic numbers, and  *)
(* returns a deduplicated list of the Root[...] / AlgebraicNumber[...] heads *)
(* that appear. Callers use the returned list as the `ext` argument to       *)
(* polynomialExtendedGCDExt / hermiteNormalFormOverKz so that polynomial     *)
(* arithmetic is performed over ℚ(ext) rather than ℚ. An empty return value *)
(* means "no algebraic extension needed — work over ℚ".                      *)
(*                                                                           *)
(* Note: we do NOT include square-rooted or cube-rooted primitives like     *)
(* Sqrt[2], because RootReduce handles those natively via the Root[] head   *)
(* after a single reduction pass. The caller is still free to include       *)
(* specific Root[]/AlgebraicNumber[] generators explicitly when performance *)
(* matters.                                                                  *)

(* ::Section:: *)
(* Robust zero-test                                                          *)
(*                                                                           *)
(* PossibleZeroQ on expressions with nested Root[] / fractional-power         *)
(* radicals frequently emits `ztest1` warnings and conservatively assumes    *)
(* zero, which can lead to silent wrong results in downstream logic (HNF    *)
(* pivot selection, Hermite termination, residue filtering). zeroQ first    *)
(* normalises through Together + Cancel + RootReduce so the test runs on   *)
(* a canonical-form expression; RootReduce handles algebraic-number         *)
(* collisions exactly wherever it can, falling back to PossibleZeroQ's     *)
(* heuristic only for genuinely ambiguous transcendental input.             *)

ClearAll[zeroQ];
zeroQ[e_] := PossibleZeroQ[e // Together // Cancel // RootReduce];

ClearAll[detectExtensionGenerators];
detectExtensionGenerators[expr_] := Module[{roots, radicals},
  (* Explicit algebraic-number heads *)
  roots = Cases[expr, _Root | _AlgebraicNumber, {0, Infinity}];
  (* Fractional-power radicals: (c)^(p/q) with c a numeric constant and q>1.  *)
  (* Mathematica emits residues in this form — e.g. (-1/3)^(1/3) — rather    *)
  (* than as Root[] objects, so we must detect these too.                     *)
  radicals = Cases[expr,
    Power[c_, r_Rational] /; NumericQ[c] && Denominator[r] > 1 :>
      Power[c, r],
    {0, Infinity}
  ];
  DeleteDuplicates[Join[roots, radicals]]
];

(* ::Section:: *)
(* Rational-in-x and polynomial-in-x checks over Q *)

(* These avoid a dependence on order-of-arguments: we test directly against *)
(* the integer/rational coefficient classes that Mathematica uses.          *)

rationalPolynomialQ[expr_, x_Symbol] :=
  PolynomialQ[expr, x] &&
  AllTrue[CoefficientList[expr, x], Element[#, Rationals] &];

rationalFunctionQ[expr_, x_Symbol] := Module[{num, den},
  num = Together[expr] // Numerator;
  den = Together[expr] // Denominator;
  rationalPolynomialQ[num, x] && rationalPolynomialQ[den, x]
];

(* Predicate: expression is rational in (x, y) over Q.                       *)
(* Implementation: clear the y-denominator against y^n - g (handled later);  *)
(* here we only check the shape by treating y as an independent symbol.      *)

rationalInXYQ[expr_, x_Symbol, y_Symbol] := Module[{num, den},
  num = Together[expr] // Numerator;
  den = Together[expr] // Denominator;
  PolynomialQ[num, {x, y}] && PolynomialQ[den, {x, y}] &&
  AllTrue[
    Join[CoefficientList[num, {x, y}] // Flatten,
         CoefficientList[den, {x, y}] // Flatten],
    Element[#, Rationals] &
  ]
];
