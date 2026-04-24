(* ::Package:: *)

(* ::Title:: *)
(* Phase 6 -- reassemble *)

(* ::Text:: *)
(* Combine the phase-3 algebraic part, the phase-5 log terms, and the      *)
(* phase-0 / phase-2 inverse substitutions into the final antiderivative.  *)

(* ::Section:: *)
(* Log-argument cleanup                                                      *)
(*                                                                           *)
(* HNF + lucky-integer normalisation in Phase 5 can leave a huge integer    *)
(* (or rational) multiplier in front of a log argument, because we keep    *)
(* clearing denominators and multiplying by leading coefficients to stay    *)
(* in K[z]. Since log(c · f) = log(c) + log(f) and log(c) is a constant    *)
(* absorbed into the integration constant, we can drop any purely numeric  *)
(* overall factor from each log argument with no loss of correctness.      *)
(*                                                                           *)
(* We also Collect each log arg by its radicals (Power[_, _Rational])      *)
(* so the display matches the user's preferred form A + y · B.              *)

ClearAll[stripLogContent];
stripLogContent[arg_] := Module[{expanded, content, simp},
  expanded = Expand[arg];
  (* FactorTermsList returns {numeric-content, primitive-part}.             *)
  content = Quiet @ FactorTermsList[expanded][[1]];
  simp = If[TrueQ[content === 0] || !NumberQ[content] || TrueQ[content === 1],
    expanded,
    Cancel[expanded / content]
  ];
  Collect[simp, Power[_, _Rational]]
];

ClearAll[monicifyLogs];
monicifyLogs[expr_] := expr /. Log[arg_] :> Log[stripLogContent[arg]];

ClearAll[reassemble];

reassemble[algAF_?afElementQ, logTerms_List, basis_?basisDescriptorQ,
           y_Symbol, shiftRecord_, phase0Scale_,
           originalX_Symbol, originalY_Symbol,
           simplifyResult_: True,
           reduceYScale_: 1] := Module[
  {algStd, logExpr, total, afterPhase2, afterPhase0Reduce, afterPhase0Scale,
   result, reducedFrame},

  (* Algebraic part in standard form (variable = basis["x"], generator = y). *)
  algStd = afToStandard[algAF, basis, y];

  (* Log part sum. *)
  logExpr = If[logTerms === {},
    0,
    Total[#[[1]] * Log[#[[2]]] & /@ logTerms]
  ];

  total = algStd + logExpr;

  (* Phase 2 inverse: substitute z -> 1/(x - a), y_new -> y_old * yScaleTotal *)
  (* evaluated at z = 1/(x - a). Yields an expression in (x, y_reduce).     *)
  If[AssociationQ[shiftRecord] && !MissingQ[shiftRecord],
    afterPhase2 = shiftRecord["inverse"][total],
    afterPhase2 = total
  ];

  (* reducedFrame is the antiderivative with y meaning the REDUCED generator*)
  (* (satisfying reduced["g"]^(1/reduced["n"])). This is what the top-level *)
  (* verifier differentiates against validated["R"], which was also updated *)
  (* to the reduced frame at the point of reduceIrreducibility rescale.     *)
  reducedFrame = afterPhase2;

  (* Phase 0 reduce reversal: forward was y_reduce = y_phase0 / reduceYScale.*)
  (* To reinterpret result-y (currently y_reduce) as y_phase0, substitute   *)
  (* y -> y / reduceYScale (so the formula's "y" now means y_phase0).       *)
  If[!TrueQ[Simplify[reduceYScale - 1] === 0],
    afterPhase0Reduce = afterPhase2 /. originalY -> originalY / reduceYScale,
    afterPhase0Reduce = afterPhase2
  ];

  (* Phase 0 scale reversal: if we cleared a rational-function denominator  *)
  (* from g via y_phase0 = q * y_user, undo by substituting y -> q * y.     *)
  If[AssociationQ[phase0Scale] && !MissingQ[phase0Scale],
    afterPhase0Scale = afterPhase0Reduce /.
      originalY -> phase0Scale["q"] * originalY,
    afterPhase0Scale = afterPhase0Reduce
  ];

  result = afterPhase0Scale;

  (* Strip numeric content from each Log argument. This is a no-op when   *)
  (* the generator was already monic-primitive, and a big display win    *)
  (* when Phase 5's HNF / lucky-integer step left a large scalar factor. *)
  result = monicifyLogs[result];

  If[simplifyResult,
    result = RootReduce[result]
  ];

  <|"result" -> result, "reducedFrame" -> reducedFrame|>
];
