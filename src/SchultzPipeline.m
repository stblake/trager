(* ::Package:: *)

(* ::Title:: *)
(* Schultz §S.7 -- pipeline driver                                            *)

(* ::Text:: *)
(* See SchultzPlan.md §S.7. Drop-in replacement for the Phase 2-6 segment of *)
(* IntegrateTrager when "Schultz" -> True. Wires together                    *)
(*                                                                            *)
(*   S.3  schultzHermiteReduce      (infinity-aware combined Hermite)         *)
(*   S.5  schultzResidues / 4.11    (consumed by S.6.1 internally)            *)
(*   S.6  schultzConstructLogTerms  (principal-generator + torsion search)    *)
(*   S.6.2 schultzFailInStyle       (structured non-elementary certificate)   *)
(*                                                                            *)
(* and finally calls the shared `reassemble` from src/Reassemble.m so the    *)
(* user-facing return form is identical to the default pipeline.              *)
(*                                                                            *)
(* What this driver does NOT do (intentionally):                              *)
(*   • No Mobius shift (Phase 2). Sch §4.3 absorbs infinity poles directly.  *)
(*     We synthesise an identity-shift record for `reassemble` so its Phase- *)
(*     2 reversal is a no-op.                                                 *)
(*   • No second Hermite call. schultzHermiteReduce already handles both     *)
(*     finite multiple poles (Lemma 4.4 part 1) and infinite poles (Lemma   *)
(*     4.4 part 2 / eq. 4.7-4.9).                                             *)
(*   • No "LogTermsMethod" branching. Schultz supplies its own log-term     *)
(*     construction (Sch §3.2 + §4.4 via S.6.1).                              *)
(*                                                                            *)
(* Failure modes (returned as Failure[...] objects, never thrown out of the   *)
(* enclosing IntegrateTrager Catch unintentionally):                         *)
(*   • schultzHermiteReduce internal inconsistency (passed through).         *)
(*   • Sch §4.3 infinity linear system unsolvable -> defer to fail-in-style. *)
(*   • Sch eq. 4.11 infinity residues non-zero post-Hermite -> defer to      *)
(*     fail-in-style (currently a structured "NonElementary" with the §S.6.2 *)
(*     deferred Lemma 5.5 stub fields).                                       *)
(*   • Torsion search exhausted within MaxTorsionOrder -> "NonElementary"    *)
(*     from `constructLogTerms` (re-used from the Trager method).             *)

(* ::Section:: *)
(* schultzPipeline                                                            *)
(*                                                                            *)
(* Inputs:                                                                     *)
(*   validated  - validateInput[...] association (post Phase-0 yScale rescale).*)
(*   reduced    - reduceIrreducibility[...] association.                      *)
(*   basis      - buildIntegralBasis[reduced["n"], reduced["g"], x] (already  *)
(*                carries "deltas" from §S.1).                                 *)
(*   x, y       - integration / generator symbols.                             *)
(*   simplifyOpt- value of "Simplify" option (forwarded to reassemble).        *)
(*   maxTorsionOpt - value of MaxTorsionOrder option (forwarded to            *)
(*                schultzConstructLogTerms; default 12 mirrors the Trager     *)
(*                method).                                                     *)
(*                                                                            *)
(* Output: <|"final" -> ..., "reducedFrame" -> ..., "diagnostics" -> ...|>   *)
(* matching the per-phase shape that IntegrateTrager already collects.        *)
(* Returns Failure[...] on out-of-scope or non-elementary input.               *)

ClearAll[schultzPipeline];
schultzPipeline[
  validated_Association,
  reduced_Association,
  basis_?basisDescriptorQ,
  x_Symbol, y_Symbol,
  simplifyOpt_,
  maxTorsionOpt_: 12
] := Catch[Module[
  {effectiveMaxTorsion = If[IntegerQ[maxTorsionOpt] && maxTorsionOpt > 0,
                            maxTorsionOpt, 12],
   hermRes, logTerms, shiftRecord, ra, diagnostics, remainderZeroQ},

  diagnostics = <||>;

  (* The Schultz path never runs Phase 2. We synthesise the identity-shift  *)
  (* record the default pipeline uses on its "Hermite-first, no shift"       *)
  (* branch so `reassemble` can be called with an identical signature.       *)
  shiftRecord = <|
    "integrand" -> validated["R"],
    "z"         -> x,
    "n"         -> reduced["n"],
    "g"         -> reduced["g"],
    "yScale"    -> 1,
    "a"         -> 0,
    "inverse"   -> Identity,
    "skipped"   -> True
  |>;
  AssociateTo[diagnostics, "schultzShift" -> shiftRecord];

  (* S.3: combined finite + infinity Hermite reduction. *)
  hermRes = schultzHermiteReduce[validated["R"], basis, y];
  If[tragerFailureQ[hermRes], Throw[hermRes]];
  AssociateTo[diagnostics, "schultzHermite" -> hermRes];

  (* If the infinity linear system was unsolvable, the integrand has a     *)
  (* multiple-pole-at-infinity contribution that Hermite alone cannot      *)
  (* absorb -- defer to the §S.6.2 fail-in-style certificate.              *)
  If[!TrueQ[hermRes["Dinf"]["solvable"]],
    Throw[schultzFailInStyle[hermRes["remainder"], hermRes["D"], basis, y,
      <|"Reason" -> "Sch §4.3 infinity-Hermite linear system unsolvable",
        "phase"  -> "schultzPipeline.hermite",
        "Dinf"   -> hermRes["Dinf"]|>]]
  ];

  (* If the Hermite remainder is identically zero in every AF coefficient, *)
  (* the antiderivative is purely algebraic — short-circuit before residue  *)
  (* extraction.                                                             *)
  remainderZeroQ = AllTrue[hermRes["remainder"]["Coeffs"],
    TrueQ[Together[#] === 0] &];
  If[remainderZeroQ,
    logTerms = {},
    (* §S.6.1 logarithmic part construction via Sch §4.4 + Lemma 4.1.       *)
    (* Combines finite + infinity residues uniformly into per-residue        *)
    (* Schultz divisors, ℚ-basis decomposes, and runs the principal-         *)
    (* generator search up to MaxTorsionOrder.                              *)
    logTerms = schultzConstructLogTerms[
      hermRes["remainder"], hermRes["D"], basis, y,
      MaxTorsionOrder -> effectiveMaxTorsion
    ];
    If[tragerFailureQ[logTerms], Throw[logTerms]]
  ];
  AssociateTo[diagnostics, "schultzLogTerms" -> logTerms];

  (* Phase 6 (shared with default pipeline): apply Phase-0 yScale + Phase-0 *)
  (* scale reversals, monicify logs, ArcTan rewrite, optional simplify.     *)
  ra = reassemble[
    hermRes["algPart"], logTerms, basis, y, shiftRecord,
    validated["scale"], x, y, simplifyOpt, reduced["yScale"]
  ];
  AssociateTo[diagnostics, "final"        -> ra["result"]];
  AssociateTo[diagnostics, "reducedFrame" -> ra["reducedFrame"]];

  <|
    "final"        -> ra["result"],
    "reducedFrame" -> ra["reducedFrame"],
    "diagnostics"  -> diagnostics
  |>
]];

(* End of module *)
