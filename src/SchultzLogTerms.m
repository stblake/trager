(* ::Package:: *)

(* ::Title:: *)
(* Schultz §S.6.1 -- logarithmic part construction via Lemma 4.1               *)

(* ::Text:: *)
(* See SchultzPlan.md §S.6, Sch §3.2 (eq. 3.3-3.4), §4.4 (eq. 4.10-4.11),      *)
(* and §4.1 Lemma 4.1 (principal-generator test).                              *)
(*                                                                              *)
(* Given a Schultz-Hermite-reduced integrand                                    *)
(*    ω = Σ_i (a_i / b) η_i dx                                                  *)
(* with squarefree b and the Lemma 4.4 invariant deg(a_i) + δ_i < deg(b), this *)
(* module produces a list                                                       *)
(*    {{c_1, F_1}, …, {c_m, F_m}}                                               *)
(* representing the logarithmic part Σ_j c_j · log(F_j) of the antiderivative. *)
(* When the residue divisors are not torsion within MaxTorsionOrder a          *)
(* `Failure["NonElementary", …]` is returned (Sch §5 fail-in-style territory). *)
(*                                                                              *)
(* PIPELINE (Sch §3.2 / §4.4 / §S.6.1):                                         *)
(*                                                                              *)
(* 1. Compute residue values at every place, finite AND infinite, using        *)
(*    `schultzResidues` (Sch eq. 4.10 + 4.11 driver).                           *)
(*                                                                              *)
(* 2. For each distinct residue value z_k, build the Schultz divisor δ(z_k)    *)
(*    via `schultzCombinedResidueDivisor`. δ(z_k) is the divisor of every      *)
(*    place where ω has residue z_k, summed across ramification indices.       *)
(*                                                                              *)
(* 3. ℚ-basis decomposition (Sch §3.2). Pick a ℚ-basis {b_1, …, b_p} of the   *)
(*    span of the residue values, with integer combination matrix M_kj such   *)
(*    that z_k = Σ_j M_kj b_j. Per direction j, the residue divisor is          *)
(*       Δ_j = Σ_k M_kj · δ(z_k)                                                *)
(*    (divisor sum = ideal product), of degree 0 by the residue theorem.        *)
(*                                                                              *)
(* 4. Torsion search (Sch §4.1 Lemma 4.1, §S.6.1). For each j, search for the *)
(*    smallest c_j with c_j · Δ_j principal, using                              *)
(*    `schultzTorsionPrincipalGenerator`. The principal generator F_j ∈ K is   *)
(*    extracted from R(c_j · Δ_j) via the direct linear-algebra computation   *)
(*    in src/SchultzPrincipal.m (Lemma 4.1: D principal of degree 0 ⟺          *)
(*    dim_k R(D) = 1, in which case the unique k-basis element is the          *)
(*    generator).                                                                *)
(*                                                                              *)
(* 5. Emit log terms (b_j / c_j) · log(F_j) per direction.                      *)
(*                                                                              *)
(* The test on non-zero infinity residues in the previous implementation —     *)
(* which deferred to §S.6.2 fail-in-style on residues at infinity — was        *)
(* incorrect: non-zero residues at infinity are part of the elementary log    *)
(* contribution and must be combined with finite residues into the divisor    *)
(* δ(z_k) per Sch §4.4. The current implementation handles both uniformly.    *)

(* ::Section:: *)
(* Helpers                                                                       *)

(* schultzResiduesUnified[Acoeffs, b, basis, ZVar] -> Association.              *)
(*                                                                              *)
(* Wraps `schultzResidues` and reorganises its output into a list of           *)
(*   <|"residue" -> z_k, "ramifications" -> {ℓ_1, …, ℓ_p},                     *)
(*     "atFinite" -> Boolean, "atInfinity" -> Boolean|>                         *)
(* keyed by distinct residue value. A residue may appear at multiple             *)
(* ramification indices and at both finite and infinite places.                  *)

ClearAll[schultzResiduesUnified];
schultzResiduesUnified[Acoeffs_List, b_, basis_?basisDescriptorQ,
                       ZVar_Symbol] := Module[
  {residueData, finite, infinity, allEntries, byResidue, residue},
  residueData = schultzResidues[Acoeffs, b, basis, ZVar];
  finite       = residueData["finite"];
  infinity     = residueData["infinity"];

  (* Flatten into per-(residue, ramification, isFinite) entries.                *)
  allEntries = Join[
    Flatten[
      KeyValueMap[
        Function[{ell, residueList},
          Map[<|"residue" -> #, "ramification" -> ell,
                "isFinite" -> True, "isInfinity" -> False|> &, residueList]
        ],
        finite
      ],
      1
    ],
    Flatten[
      KeyValueMap[
        Function[{ell, residueList},
          Map[<|"residue" -> #, "ramification" -> ell,
                "isFinite" -> False, "isInfinity" -> True|> &, residueList]
        ],
        infinity
      ],
      1
    ]
  ];

  (* Group by residue value. Each group becomes a single entry whose            *)
  (* "ramifications" merges over both finite and infinite contributions.        *)
  byResidue = GroupBy[
    allEntries,
    #["residue"] &
  ];

  KeyValueMap[
    Function[{residueValue, entries},
      <|
        "residue"        -> residueValue,
        "ramifications"  -> DeleteDuplicates[Map[#["ramification"] &, entries]],
        "atFinite"       -> AnyTrue[entries, #["isFinite"] &],
        "atInfinity"     -> AnyTrue[entries, #["isInfinity"] &]
      |>
    ],
    byResidue
  ]
];

(* combineDivisorsByExponents — multiply Schultz divisors with integer power.  *)
(*                                                                              *)
(* Δ_j = ∏_k δ(z_k)^{m_kj} (ideal product of integer powers).                   *)
(* Folds via `schultzDivisorMultiply` after raising each constituent to its    *)
(* m_kj power via `schultzDivisorPower` (handles negative exponents through    *)
(* `schultzDivisorInverse`).                                                     *)

ClearAll[combineDivisorsByExponents];
combineDivisorsByExponents[
  divisors_List, exponents_List, basis_?basisDescriptorQ
] := Module[{nonZero, scaled, scaledFailure, result},
  nonZero = Pick[
    Transpose[{divisors, exponents}],
    Map[# =!= 0 &, exponents]
  ];
  If[nonZero === {},
    Return[schultzDivisorTrivial[basis]]
  ];
  scaled = Map[
    schultzDivisorPower[#[[1]], #[[2]]] &,
    nonZero
  ];
  (* Propagate the first Failure encountered while raising divisors to    *)
  (* their integer powers — typically a deferred schultzDivisorInverse    *)
  (* for n >= 3.                                                            *)
  scaledFailure = SelectFirst[scaled, tragerFailureQ, None];
  If[scaledFailure =!= None, Return[scaledFailure]];
  result = First[scaled];
  Do[result = schultzDivisorMultiply[result, sd], {sd, Rest[scaled]}];
  If[tragerFailureQ[result], Return[result]];
  result
];

(* ::Section:: *)
(* schultzConstructLogTerms                                                     *)

ClearAll[schultzConstructLogTerms];

Options[schultzConstructLogTerms] = {
  MaxTorsionOrder -> 12,
  "DegreeBuffer"  -> 0
};

(* schultzConstructLogTerms[integrandAF, b, basis, y, opts] -> list of pairs.  *)
(*                                                                              *)
(* Inputs:                                                                       *)
(*   integrandAF  - post-Hermite AF element (Σ a_i/b η_i)                        *)
(*   b            - squarefree denominator polynomial in basis["x"]             *)
(*                  (passed explicitly: avoids subtle mismatches when b has a  *)
(*                  unit factor folded into the integrand's denominator).      *)
(*   basis        - basis descriptor (with "deltas" populated, §S.1)            *)
(*   y            - generator symbol                                             *)
(*                                                                              *)
(* Output: a list of {coefficient, F_standard_form} pairs, where coefficient is *)
(* a constant in K = ℚ(α)(params) and F_standard is a polynomial-in-(x, y)    *)
(* expression for the log argument.                                             *)
(*                                                                              *)
(* On failure: returns Failure[...] tagged either                               *)
(*    "NonElementary" (residue divisor not torsion within bound), or           *)
(*    "ImplementationIncomplete" (a known gap surfaced).                        *)

schultzConstructLogTerms[integrandAF_?afElementQ, b_,
                        basis_?basisDescriptorQ, y_Symbol,
                        OptionsPattern[]] := Catch[Module[
  {n, x, ad, Acoeffs, ZVar, residueEntries, residueValues, divisors,
   qbInfo, qBasis, basisCoeffs, logTerms, maxOrd,
   degreeBuffer, j, exponents, deltaJ, torRes, coeff, fStd},

  n = basis["n"]; x = basis["x"];
  maxOrd = OptionValue[MaxTorsionOrder];
  degreeBuffer = OptionValue["DegreeBuffer"];

  (* Step 1: integrand → AF coefficients.                                        *)
  ad = commonDenominatorAF[integrandAF, x];
  Acoeffs = ad["A"];

  (* Step 2: residues at finite + infinite places.                              *)
  ZVar = Unique["zRes"];
  residueEntries = schultzResiduesUnified[Acoeffs, b, basis, ZVar];
  If[residueEntries === {}, Throw[{}]];
  residueValues = Map[#["residue"] &, residueEntries];

  (* Step 3: per-residue Schultz divisors.                                       *)
  divisors = Map[
    Function[entry,
      schultzCombinedResidueDivisor[
        Acoeffs, b, basis, y,
        entry["residue"],
        entry["ramifications"]
      ]
    ],
    residueEntries
  ];

  (* Step 4: ℚ-basis decomposition of residue span.                              *)
  qbInfo = residueQBasis[residueValues];
  qBasis      = qbInfo["qBasis"];
  basisCoeffs = qbInfo["basisCoeffs"];

  If[qBasis === {} || basisCoeffs === {}, Throw[{}]];
  If[Length[basisCoeffs] =!= Length[residueValues],
    Throw[incompleteFailure["SchultzLogTermsShapeMismatch",
      "ResidueCount"   -> Length[residueValues],
      "BasisCoeffRows" -> Length[basisCoeffs]]]
  ];

  (* Step 5: torsion search per ℚ-basis direction.                               *)
  logTerms = {};
  Do[
    exponents = basisCoeffs[[All, j]];
    deltaJ = combineDivisorsByExponents[divisors, exponents, basis];
    If[tragerFailureQ[deltaJ], Throw[deltaJ]];

    torRes = schultzTorsionPrincipalGenerator[
      deltaJ, schultzDivisorPower,
      "MaxOrder"     -> maxOrd,
      "DegreeBuffer" -> degreeBuffer
    ];

    If[torRes["order"] === "failed",
      Throw[tragerFailure["NonElementary",
        "BasisElement"    -> qBasis[[j]],
        "BasisCoeffs"     -> exponents,
        "Divisor"         -> deltaJ,
        "MaxTorsionOrder" -> maxOrd,
        "Method"          -> "Schultz",
        "Reason"          -> "no principal c · Δ_j found within MaxTorsionOrder \
via Sch Lemma 4.1; integrand has no elementary antiderivative within this bound"
      ]]
    ];

    coeff = Together[qBasis[[j]] / torRes["order"]];
    fStd  = afToStandard[torRes["function"], basis, y];
    AppendTo[logTerms, {coeff, fStd}],
    {j, Length[qBasis]}
  ];

  logTerms
]];

(* End of module *)
