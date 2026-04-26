(* ::Package:: *)

(* ::Title:: *)
(* Top-level: IntegrateTrager *)

(* ::Text:: *)
(* Runs the full Phase 0 -> 6 pipeline. See TragerPlan.md Section 1.        *)
(*                                                                           *)
(* Control flow: wrapped in Catch; any phase or verification step may Throw *)
(* a Failure object to short-circuit and return it as the final result.     *)

Clear[IntegrateTrager];

IntegrateTrager::usage =
  "IntegrateTrager[f, {x, y, y^n == g}] integrates an algebraic function f \
rational in (x, y), where y is a simple radical satisfying y^n = g(x) with \
g in Q[x] and n an integer >= 2. Returns an elementary antiderivative \
expressed as an algebraic part plus a sum of logarithmic terms (using Root[] \
for algebraic numbers when needed), or a Failure[...] object on out-of-scope \
or invalid input.\n\n\
IntegrateTrager[f, x] is a surface-syntax form that auto-detects a single \
algebraic radical pattern f^(k/n) in the integrand, synthesises an internal \
y and the relation y^n = g, delegates to the three-argument form, and \
substitutes y -> g^(1/n) in the result so the answer is expressed directly \
in the user's variables.\n\n\
Scope: genus-0 curves y^n = g(x) over Q. Out-of-scope inputs return Failure \
tags \"PositiveGenus\", \"NotSimpleRadical\", \"DegenerateRadical\", \
\"UnsupportedBaseField\", or \"BadInput\".\n\n\
Options (all option names are strings):\n\
  \"Verbose\" -> False      emit diagnostic messages during integration\n\
  \"Diagnostics\" -> False  return <|\"Result\" -> ..., \"Diagnostics\" -> ...|>\n\
  \"Simplify\" -> True      apply RootReduce/Simplify to the final result\n\
  \"ShiftBound\" -> 32      max |a| tried when searching for a regular Mobius shift\n\
  \"MaxGenus\" -> Infinity  gate on computed genus (0 = strict genus-0 only)\n\
  \"LogTermsMethod\" -> \"Auto\"  one of \"Auto\", \"Trager\", \"Miller\", \"Kauers\"; \
\"Auto\" tries Trager, then Miller, then Kauers, returning the first verified \
antiderivative\n\
  \"Parameters\" -> Automatic  list of free symbols treated as transcendental\n\
                              parameters (base field becomes Q(params)).\n\
                              Automatic auto-detects every free symbol in\n\
                              (integrand, relation) other than x and y.\n\
                              Antiderivatives in this mode are valid on a\n\
                              Zariski-open subset of parameter values\n\
                              (i.e. except at finitely many specialisations\n\
                              where the genus or factor structure changes).\n\n\
Examples:\n\
  IntegrateTrager[1/Sqrt[x^2 + 1], x]\n\
  IntegrateTrager[1/y, {x, y, y^2 == x^2 + 1}]\n\
  IntegrateTrager[((x^2 + 8)*(x^2 - 4)^(1/4))/(x^2 - 8)^2, x]";

(* Option names are strings to avoid colliding with the built-in symbols    *)
(* System`Verbose and System`Simplify, and to keep the public option surface *)
(* uniformly string-keyed.                                                   *)
Options[IntegrateTrager] = {
  "Verbose"         -> False,
  "Diagnostics"     -> False,
  "Simplify"        -> True,
  "ShiftBound"      -> 32,
  "MaxGenus"        -> Infinity,  (* Infinity: permissive (genus gate off). *)
                                  (* 0: strict genus-0 only.                 *)
                                  (* >= g: attempt genus <= g inputs.         *)
  "Schultz"         -> False,     (* Route through the Schultz 2015 variant  *)
                                  (* (SchultzPlan.md): drop-in replacement   *)
                                  (* for Phase 2-6, using the eta-basis with *)
                                  (* infinity exponents (S.1), the double-   *)
                                  (* ideal divisor representation (S.2),     *)
                                  (* the infinity-aware Hermite reduction    *)
                                  (* (S.3), the norm-resultant residues      *)
                                  (* (S.4-S.5), and the principal-generator  *)
                                  (* + fail-in-style log terms (S.6).        *)
                                  (* When True, "LogTermsMethod" is ignored. *)
  "Verify"          -> False,     (* Opt-in step-10 derivative-vs-integrand  *)
                                  (* check. Default False: return Phase-6    *)
                                  (* output as-is. When True, differentiate  *)
                                  (* the proposed antiderivative and compare *)
                                  (* (symbolically, then numerically), and   *)
                                  (* on mismatch promote to a NonElementary  *)
                                  (* or ImplementationIncomplete Failure.    *)
                                  (* The symbolic pass can be extremely slow *)
                                  (* on expressions containing Root/RootSum *)
                                  (* (Kauers log parts with degree ≥ 4      *)
                                  (* irreducible R(Z) factors), which is why *)
                                  (* it is off by default — callers who need *)
                                  (* correctness guarantees enable it at use *)
                                  (* site.                                     *)
  "LogTermsMethod"  -> "Auto",    (* "Auto" | "Trager" | "Miller" | "Kauers" *)
                                  (* "Auto" tries "Trager", "Miller", and    *)
                                  (* "Kauers" in order, returning the first  *)
                                  (* whose antiderivative passes the step-10  *)
                                  (* derivative-vs-integrand check. Each     *)
                                  (* method has its own algorithmic strengths *)
                                  (* and corner-case gaps -- "Trager" handles *)
                                  (* the parametric + algebraic-residue cases *)
                                  (* (Q(a,b)(Sqrt[a+b^2])) where Miller hits  *)
                                  (* MillerKauersTorsionBoundExceeded; Miller *)
                                  (* handles the parametric Q(a)(I) cases    *)
                                  (* (e.g. (a x^4+b)^(-1/4)) where Trager's   *)
                                  (* K[z]-HNF over Q(a)[z] blows up.          *)
                                  (* "MillerKauers" alias accepted for back- *)
                                  (* compat; canonical name is "Miller".     *)
  "Parameters"      -> Automatic, (* List of free symbols to treat as       *)
                                  (* transcendental parameters: the base    *)
                                  (* field becomes ℚ(params) instead of ℚ. *)
                                  (* Automatic = auto-detect every free     *)
                                  (* symbol in (integrand, relation) other  *)
                                  (* than x and y. Pass {} to force ℚ-only. *)
  "MaxTorsionOrder" -> 12         (* Bound on torsion search for divisors    *)
                                  (* on positive-genus curves (Sch §3.2 /    *)
                                  (* §S.6.1, TragerPlan.md §10.2). For the   *)
                                  (* default Mazur-bound = 12 fits elliptic  *)
                                  (* (genus-1) cases. Higher genera and the  *)
                                  (* Schultz-paper showcase example need     *)
                                  (* larger values (e.g. 30 for the          *)
                                  (* `(29x²+18x-3)/√(x⁶+...)` integral whose *)
                                  (* torsion order is 29).                    *)
};

(* Auto-detect parameters: every Symbol in (integrand, relation) that is    *)
(* (a) not x or y, (b) not in System` context, (c) has no value attached.   *)
(* The third condition rules out built-in mathematical constants like Pi,  *)
(* I, E, etc. (which already evaluate or are protected) and any user-bound *)
(* numeric symbol (which is a literal value, not a parameter).             *)

ClearAll[autoDetectParameters];
autoDetectParameters[expr_, x_Symbol, y_Symbol] := Module[{symbols},
  symbols = DeleteDuplicates @ Cases[{expr},
    s_Symbol /; s =!= x && s =!= y &&
                Context[s] =!= "System`" &&
                !ValueQ[s],
    {0, Infinity}
  ];
  symbols
];

(* Resolve the user's "Parameters" option value to an explicit list,        *)
(* auto-detecting when Automatic is passed. Validates that none of the      *)
(* parameters collide with x, y, or each other.                             *)

ClearAll[resolveParameters];
resolveParameters[optVal_, integrand_, relation_, x_Symbol, y_Symbol] := Module[
  {params, dups, badSymbols},
  params = If[optVal === Automatic,
    autoDetectParameters[{integrand, relation}, x, y],
    optVal
  ];
  If[!ListQ[params],
    Return[tragerFailure["BadInput",
      "Reason" -> "\"Parameters\" must be a list of symbols (or Automatic)",
      "Value"  -> optVal]]
  ];
  badSymbols = Select[params, !MatchQ[#, _Symbol] &];
  If[badSymbols =!= {},
    Return[tragerFailure["BadInput",
      "Reason" -> "every \"Parameters\" entry must be a Symbol",
      "BadEntries" -> badSymbols]]
  ];
  If[MemberQ[params, x] || MemberQ[params, y],
    Return[tragerFailure["BadInput",
      "Reason" -> "x and y cannot be parameters",
      "Parameters" -> params, "x" -> x, "y" -> y]]
  ];
  dups = Select[Tally[params], #[[2]] > 1 &];
  If[dups =!= {},
    Return[tragerFailure["BadInput",
      "Reason" -> "duplicate entries in \"Parameters\"",
      "Duplicates" -> dups[[All, 1]]]]
  ];
  params
];

(* "Auto" mode dispatcher: try Trager (the most algorithmically rigorous,    *)
(* with strict Z-basis structure), then Miller (faster than Trager on        *)
(* parametric + Gaussian-residue cases like (a x^4+b)^(-1/4) where Trager's *)
(* K[z]-HNF over Q(a,I)[z] blows up), then Kauers (heuristic, last-resort   *)
(* — its partial-result behaviour catches anything the first two miss).     *)
(* TimeConstrained budgets keep a slow Trager attempt (status §3.1) from    *)
(* dominating wall time on parametric inputs.                                *)
$tragerAutoMethodBudgetSeconds = {30, 90, 60};
$tragerAutoMethodSequence      = {"Trager", "Miller", "Kauers"};

ClearAll[autoModeIntegrate, autoExtractAntideriv, autoMethodSucceededQ];

(* Antiderivative extractor that knows how to peek inside the                *)
(* {"Diagnostics" -> True} return form <|"Result" -> ..., "Diagnostics" -> *)
(* ...|>.                                                                    *)
autoExtractAntideriv[res_Association] :=
  If[KeyExistsQ[res, "Result"], res["Result"], res];
autoExtractAntideriv[res_] := res;

(* A method has "succeeded" iff its antiderivative is not a Failure, not a  *)
(* TimeConstrained sentinel, and contains no HoldForm[IntegrateTrager][...] *)
(* residual (Kauers's partial-result wrap).                                  *)
autoMethodSucceededQ[res_] := With[{ad = autoExtractAntideriv[res]},
  !MatchQ[ad, _Failure] && ad =!= $tragerAutoTimedOut &&
    FreeQ[ad, HoldForm[IntegrateTrager]]
];

autoModeIntegrate[integrand_, {x_Symbol, y_Symbol, relation_},
                  opts : OptionsPattern[IntegrateTrager]] := Module[
  {filteredOpts, results, methodResult, idx, kauersAttempt},
  (* Strip both "LogTermsMethod" (we set it per-iteration) and "Verify" (we  *)
  (* force it True so the cascade can tell whether a method's output is     *)
  (* actually correct; the user-level default is False). Without the forced *)
  (* Verify, every method's Phase-6 output would pass autoMethodSucceededQ  *)
  (* on shape alone and Auto would lock in on Trager's partial result       *)
  (* instead of trying Miller / Kauers.                                     *)
  filteredOpts = FilterRules[{opts}, Except["LogTermsMethod" | "Verify"]];

  results = {};
  Do[
    methodResult = TimeConstrained[
      IntegrateTrager[integrand, {x, y, relation},
        Sequence @@ filteredOpts,
        "Verify"         -> True,
        "LogTermsMethod" -> $tragerAutoMethodSequence[[idx]]],
      $tragerAutoMethodBudgetSeconds[[idx]],
      $tragerAutoTimedOut
    ];
    AppendTo[results, $tragerAutoMethodSequence[[idx]] -> methodResult];
    If[autoMethodSucceededQ[methodResult], Return[methodResult, Module]],
    {idx, Length[$tragerAutoMethodSequence]}
  ];

  (* All methods failed/timed out. Prefer a Kauers partial result IF it     *)
  (* integrated at least some piece (final ≠ 0) — that carries genuine     *)
  (* progress the caller can inspect. A bare HoldForm[IntegrateTrager][...]*)
  (* (final == 0) means Kauers integrated nothing and we'd be hiding the    *)
  (* upstream NonElementary diagnosis behind a meaningless wrap, so prefer *)
  (* the actual Failure in that case.                                       *)
  kauersAttempt = "Kauers" /. results;
  Module[{kauersAd = autoExtractAntideriv[kauersAttempt]},
    If[!MatchQ[kauersAttempt, _Failure] &&
        kauersAttempt =!= $tragerAutoTimedOut &&
        !MatchQ[kauersAd, HoldForm[IntegrateTrager][__]] &&
        kauersAd =!= 0,
      Return[kauersAttempt, Module]
    ]
  ];

  (* Otherwise return the first meaningful (non-timeout) attempt — earlier *)
  (* methods (Trager, Miller) carry the most rigorous Failure diagnosis    *)
  (* (e.g. "NonElementary" with the AttemptedAntiderivative + Residual     *)
  (* metadata).                                                             *)
  Module[{nonTimeout = Select[results,
                              #[[2]] =!= $tragerAutoTimedOut &]},
    If[nonTimeout =!= {},
      First[nonTimeout][[2]],
      tragerFailure["AutoMethodsExhausted",
        "Reason"           -> "every method timed out",
        "MethodSequence"   -> $tragerAutoMethodSequence,
        "BudgetSeconds"    -> $tragerAutoMethodBudgetSeconds]
    ]
  ]
];

IntegrateTrager[integrand_, {x_Symbol, y_Symbol, relation_},
                opts : OptionsPattern[]] := Catch[Module[
  {
    verboseOpt    = TrueQ[OptionValue["Verbose"]],
    diagOpt       = TrueQ[OptionValue["Diagnostics"]],
    simplifyOpt   = TrueQ[OptionValue["Simplify"]],
    shiftBoundOpt = OptionValue["ShiftBound"],
    maxGenusOpt   = OptionValue["MaxGenus"],
    schultzOpt    = TrueQ[OptionValue["Schultz"]],
    verifyOpt     = TrueQ[OptionValue["Verify"]],
    logMethodOpt  = OptionValue["LogTermsMethod"],
    paramsOpt     = OptionValue["Parameters"],
    maxTorsionOpt = OptionValue["MaxTorsionOrder"],
    paramsResolved,
    logTermsFn,
    validated, reduced, genus, basis,
    zLoc, zResLoc, shiftResult, basisShifted, hermRes, residueRes, logTerms,
    final, diagnostics
  },

  (* Auto mode dispatches to the explicit-method form via                     *)
  (* autoModeIntegrate. Doing this BEFORE option validation keeps "Auto"     *)
  (* invisible to the per-method pipeline — every downstream branch sees a   *)
  (* concrete method name.                                                    *)
  If[logMethodOpt === "Auto",
    Throw[autoModeIntegrate[integrand, {x, y, relation}, opts]]
  ];

  paramsResolved = resolveParameters[paramsOpt, integrand, relation, x, y];
  If[tragerFailureQ[paramsResolved], Throw[paramsResolved]];

  (* Block the pipeline body so $tragerParameters is dynamically scoped     *)
  (* over every helper call. baseFieldElementQ, zeroQ, detectExtension-     *)
  (* Generators, and friends consult this variable; threading it through    *)
  (* every signature would touch every file with no algorithmic benefit.    *)
  Block[{$tragerParameters = paramsResolved},

  (* "LogTermsMethod" is ignored under "Schultz" -> True (Schultz supplies   *)
  (* its own residue + log-term construction via §S.6.1). We still validate  *)
  (* the option only on the default path, so an invalid LogTermsMethod still*)
  (* surfaces as BadInput in the common case.                                *)
  If[!schultzOpt,
    logTermsFn = Switch[logMethodOpt,
      "Trager",                          constructLogTerms,
      "Miller" | "MillerKauers",         MillerKauersLogTerms,
      "Kauers",                          KauersLogTerms,
      _, Throw[tragerFailure["BadInput",
        "Reason" -> "\"LogTermsMethod\" must be \"Auto\", \"Trager\", \"Miller\", or \"Kauers\"",
        "Value"  -> logMethodOpt]]
    ],
    logTermsFn = Null
  ];

  diagnostics = <||>;

  (* Small helper: abort-on-failure guard. *)
  (* If `value` is a Failure, Throw it; otherwise return the value.          *)
  SetAttributes[guard, HoldFirst];
  guard[expr_] := Module[{v = expr}, If[tragerFailureQ[v], Throw[v]]; v];

  (* Step 1: validate *)
  validated = guard[validateInput[integrand, x, y, relation]];
  AssociateTo[diagnostics, "phase0" -> validated];

  (* Step 2: reduceIrreducibility. If (n, g) changed or yScale != 1, we    *)
  (* must re-express the integrand in the new generator: y_old = y_new *   *)
  (* yScale. The gcd-of-exponents reduction (changing n -> n/d) does not   *)
  (* require integrand substitution -- the new y IS the old y, just with a *)
  (* different defining equation (a specific factor of y^n - g_old).       *)
  reduced = guard[reduceIrreducibility[validated["n"], validated["g"], x]];
  AssociateTo[diagnostics, "phase0_reduce" -> reduced];
  If[reduced["yScale"] =!= 1,
    Module[{integrandRescaled},
      integrandRescaled = Together[validated["R"] /. y -> y * reduced["yScale"]];
      integrandRescaled = reduceYDegree[
        integrandRescaled, x, y, reduced["n"], reduced["g"]
      ];
      validated = Association[validated, "R" -> integrandRescaled];
    ]
  ];

  (* Step 3: computeGenus. Gate by "MaxGenus". *)
  genus = computeGenus[reduced["n"], reduced["g"], x];
  AssociateTo[diagnostics, "genus" -> genus];
  If[genus > maxGenusOpt,
    Throw[tragerFailure["PositiveGenus",
      "Genus" -> genus, "n" -> reduced["n"], "g" -> reduced["g"],
      "MaxGenusOption" -> maxGenusOpt
    ]]
  ];

  (* Step 4: buildIntegralBasis *)
  basis = buildIntegralBasis[reduced["n"], reduced["g"], x];
  AssociateTo[diagnostics, "basis" -> basis];

  If[schultzOpt,
    (* === Schultz pipeline (SchultzPlan.md §S.7) =========================== *)
    (* Drop-in replacement for Phases 2-6: the SchultzPipeline driver runs   *)
    (* the infinity-aware Hermite reduction, the eq. 4.10 / 4.11 residues   *)
    (* and the §S.6 principal-generator + fail-in-style log-term path, and  *)
    (* delegates to the same `reassemble` Phase 6 used by the default path. *)
    Module[{spr},
      spr = schultzPipeline[validated, reduced, basis, x, y, simplifyOpt,
                            maxTorsionOpt];
      If[tragerFailureQ[spr], Throw[spr]];
      AssociateTo[diagnostics, "schultz" -> spr["diagnostics"]];
      final = spr["final"];
      AssociateTo[diagnostics, "final"        -> final];
      AssociateTo[diagnostics, "reducedFrame" -> spr["reducedFrame"]];
    ],
    (* === Default pipeline (Phases 2-6 unchanged) ========================== *)

  (* Steps 5 + 6: Hermite-first strategy (per TragerPlan.md §12).           *)
  (* If the integrand's form f·dx is already regular at every infinity      *)
  (* place on the curve, Phase 2 is not only unnecessary but harmful — the *)
  (* Möbius shift introduces a z-factor in both the basis dmax and the     *)
  (* Hermite denominator D, causing them to share a common factor at z = 0 *)
  (* and driving the Rothstein-Trager double resultant to identically zero.*)
  (* So we run Hermite in the original x-frame first, check regularity at  *)
  (* infinity, and fall back to Phase 2 only when the form really does     *)
  (* have a pole at infinity (tier-1 `1/sqrt(...)` cases).                  *)
  Module[{integrandAF},
    integrandAF = rationalizeToAF[validated["R"], basis, y];
    If[afFormRegularAtInfinity[integrandAF, basis],
      (* Skip Phase 2. Build an identity shift record for Phase 6. *)
      shiftResult = <|
        "integrand" -> validated["R"],
        "z"         -> x,
        "n"         -> reduced["n"],
        "g"         -> reduced["g"],
        "yScale"    -> 1,
        "a"         -> 0,
        "inverse"   -> Identity,
        "skipped"   -> True
      |>;
      basisShifted = basis;
      hermRes = guard[hermiteReduce[validated["R"], basis, y]],
      (* Pole at infinity detected: apply Phase 2 and redo Hermite.        *)
      shiftResult = guard[shiftAwayFromInfinity[validated["R"], x, y,
                                                 reduced["n"], reduced["g"],
                                                 zLoc, shiftBoundOpt]];
      basisShifted = buildIntegralBasis[shiftResult["n"], shiftResult["g"],
                                        shiftResult["z"]];
      hermRes = guard[hermiteReduce[shiftResult["integrand"], basisShifted,
                                     y]]
    ]
  ];
  AssociateTo[diagnostics, "phase2" -> shiftResult];
  AssociateTo[diagnostics, "phase3" -> hermRes];

  (* Steps 7 + 8: residues and log terms in z-frame. Phase 5 currently      *)
  (* relies on Mathematica's Integrate on the z-frame univariate pull-back  *)
  (* (see TragerLogTerms.m header for status notes).                          *)
  If[AllTrue[hermRes["remainder"]["Coeffs"], TrueQ[Together[#] === 0] &],
    residueRes = <|"residues" -> {}|>;
    logTerms = {},
    residueRes = guard[computeResidues[hermRes["remainder"], hermRes["D"],
                                        basisShifted, y, zResLoc]];
    (* Liouville structural check (Trager Ch 5 §4, Ch 6 §3). After Hermite *)
    (* the remainder ω has square-free denominator, so its only poles are *)
    (* simple. If computeResidues returns no residues, every such pole has*)
    (* zero residue and lies above a branch place — i.e. the form is      *)
    (* regular at every place on the lifted Riemann surface. That makes  *)
    (* ω a holomorphic (first-kind) differential. Genus 0 admits no non- *)
    (* zero holomorphic differentials (H^0(C, Ω^1) = 0), so this state   *)
    (* on genus 0 is an internal bug; for genus ≥ 1 the integrand is     *)
    (* non-elementary by Liouville since first-kind differentials carry  *)
    (* no log component and are exact only when zero.                    *)
    If[residueRes["residues"] === {},
      Module[{remainderStd},
        remainderStd = afToStandard[hermRes["remainder"], basisShifted, y];
        Which[
          genus === 0,
            Throw[incompleteFailure["Phase4ResiduesEmptyOnGenus0",
              "Reason"    -> "computeResidues returned no residues but the \
Hermite remainder is non-zero. Genus 0 admits no non-zero holomorphic \
differentials, so this indicates a missed pole during the Z^k strip in \
computeResidues, or a Hermite reduction defect.",
              "Remainder" -> remainderStd,
              "D"         -> hermRes["D"],
              "n"         -> reduced["n"],
              "g"         -> reduced["g"]]],
          True,
            Throw[tragerFailure["NonElementary",
              "Genus"     -> genus,
              "n"         -> reduced["n"],
              "g"         -> reduced["g"],
              "Reason"    -> "Hermite remainder is a non-zero first-kind \
differential on a positive-genus curve; no elementary antiderivative exists \
(Liouville).",
              "AttemptedAntiderivative" ->
                afToStandard[hermRes["algPart"], basisShifted, y],
              "Remainder" -> remainderStd]]
        ]
      ]
    ];
    logTerms = guard[logTermsFn[residueRes["residues"], hermRes["remainder"],
                                  hermRes["D"], basisShifted, y,
                                  Multiplicities -> residueRes["multiplicities"],
                                  QBasis         -> residueRes["qBasis"],
                                  BasisCoeffs    -> residueRes["basisCoeffs"]]];
  ];
  AssociateTo[diagnostics, "phase4" -> residueRes];
  AssociateTo[diagnostics, "phase5" -> logTerms];

  (* Step 9: reassemble (applies phase-2 + phase-0-reduce + phase-0-scale inverses). *)
  (* Returns an association with "result" (user-facing, in original y frame) *)
  (* and "reducedFrame" (pre-reduce-reversal, with y = reduced generator).   *)
  Module[{ra = reassemble[hermRes["algPart"], logTerms, basisShifted, y,
                           shiftResult, validated["scale"], x, y, simplifyOpt,
                           reduced["yScale"]]},
    final = ra["result"];
    AssociateTo[diagnostics, "final" -> final];
    AssociateTo[diagnostics, "reducedFrame" -> ra["reducedFrame"]];
  ]
  ];  (* end If[schultzOpt, ..., default-branch] *)

  (* Step 10: OPT-IN verification of the antiderivative (see "Verify" option).*)
  (* Differentiate the proposed result and compare to the original integrand*)
  (* under y -> g^(1/n). Verification happens in the REDUCED frame, because *)
  (* validated["R"] was rewritten in the reduced generator at the Phase 0   *)
  (* rescale step. On mismatch we cannot distinguish (i) a genuinely non-   *)
  (* elementary integrand (legitimate on genus > 0) from (ii) a Phase-5     *)
  (* implementation gap. We report ImplementationIncomplete for genus-0     *)
  (* failures (Phase-5 bug) and NonElementary for genus > 0.                 *)
  (*                                                                         *)
  (* The verifier first tries symbolic Simplify + zeroQ. If that cannot     *)
  (* decide (common when the antiderivative contains nested algebraic       *)
  (* numbers like Sqrt[Sqrt[1+2 I]] etc.), it falls back to high-precision  *)
  (* numerical sampling at several random rational x-values. A meromorphic  *)
  (* function vanishes on an open set iff it vanishes identically, so       *)
  (* multiple agreeing zero samples at >40-digit precision is a reliable    *)
  (* identity test for our (rational + algebraic + log) class of expressions.*)
  (*                                                                         *)
  (* Skipped by default because the symbolic pass is expensive on large    *)
  (* algebraic expressions (Simplify over nested Root/RootSum can take     *)
  (* minutes and still fail to prove zero, leaving numerics as the only     *)
  (* ground truth anyway). Enable "Verify" -> True for a correctness check *)
  (* at the cost of wall time.                                               *)
  If[verifyOpt,
  Module[{yRoot, integrandSub, reducedFrameAntideriv, diff, diffSimp,
          symbolicZero, numericVerified, samples, tol, prec = 60, nSamples = 6},
    yRoot = reduced["g"]^(1/reduced["n"]);
    integrandSub = validated["R"] /. y -> yRoot;
    reducedFrameAntideriv = diagnostics["reducedFrame"];
    diff = D[reducedFrameAntideriv /. y -> yRoot, x] - integrandSub;
    diffSimp = Quiet @ Simplify[diff];
    symbolicZero = TrueQ[diffSimp === 0] || TrueQ[zeroQ[diffSimp]];
    numericVerified = False;
    If[!symbolicZero,
      (* Numerical fallback: sample at random reals with high working      *)
      (* precision. The samples are accepted as zero if every sample's     *)
      (* magnitude (real and imaginary parts) is below 10^(-prec/2).       *)
      (* SeedRandom for reproducibility across invocations.                *)
      (* In parametric mode every parameter is also bound to a random      *)
      (* generic real, so the sample tests "generically zero" — exactly   *)
      (* the semantics the algorithm guarantees on the Zariski-open set.  *)
      samples = Quiet @ Block[{},
        SeedRandom[20240515];
        Table[
          Module[{paramRules},
            paramRules = (# -> RandomReal[{1/3, 23/7},
                                          WorkingPrecision -> prec]) & /@
                         $tragerParameters;
            N[diffSimp /. paramRules /. x -> RandomReal[{-7/2, 11/2},
                                          WorkingPrecision -> prec], prec]
          ],
          {nSamples}
        ]
      ];
      tol = 10^(-prec/2);
      numericVerified = AllTrue[samples,
        NumericQ[#] && Abs[Re[#]] < tol && Abs[Im[#]] < tol &]
    ];
    Which[
      symbolicZero,
        AssociateTo[diagnostics, "verified" -> True],
      numericVerified,
        AssociateTo[diagnostics, "verified" -> "numerical"];
        AssociateTo[diagnostics, "verifySamples" -> samples],
      logMethodOpt === "Kauers",
        (* Kauers is a heuristic: it may fail to handle every R_z factor   *)
        (* and silently leaves the rest unintegrated. Return a partial     *)
        (* result of the form                                              *)
        (*     final + IntegrateTrager[residual, x, opts]                  *)
        (* where residual = integrand − d/dx(final) is the un-integrated   *)
        (* differential in pure-x form (diffSimp = D[attempted, x] − f).    *)
        (* The inner call is wrapped as HoldForm[IntegrateTrager][...] so  *)
        (* its head is HoldForm[IntegrateTrager] (no matching rules) and    *)
        (* it stays unevaluated — displayed cleanly as IntegrateTrager[…],  *)
        (* letting the caller inspect, differentiate, or re-dispatch with   *)
        (* a different LogTermsMethod.                                      *)
        Module[{residual = -diffSimp},
          AssociateTo[diagnostics,
            "partialResult" -> <|
              "Method"                  -> "Kauers",
              "AttemptedAntiderivative" -> final,
              "Residual"                -> residual
            |>];
          final = final + HoldForm[IntegrateTrager][residual, x, opts];
        ],
      genus === 0,
        Throw[incompleteFailure["Phase5PrincipalGenerator",
          "Integrand" -> integrand,
          "Genus" -> genus,
          "AttemptedAntiderivative" -> final,
          "Residual" -> diffSimp,
          "Reason" -> "Phase 5 produced an antiderivative whose derivative \
does not match the integrand. This indicates the K[z]-module / principal-\
generator algorithm in findPrincipalGenerator produced an element of the \
K[z]_(z)-localization that is not in the original K[z]-submodule I_D, OR \
selected a pole-free-at-infinity generator that has additional spurious zeros \
outside supp(D). See src/PrincipalGen.m and src/TragerLogTerms.m for \
algorithmic details and the port plan in TragerPlan.md §13."
        ]],
      True,
        Throw[tragerFailure["NonElementary",
          "Genus" -> genus, "n" -> reduced["n"], "g" -> reduced["g"],
          "AttemptedAntiderivative" -> final,
          "Residual" -> diffSimp
        ]]
    ]
  ]];

  If[diagOpt,
    <|"Result" -> final, "Diagnostics" -> diagnostics|>,
    final
  ]

  ] (* end Block[$tragerParameters] *)
]];
