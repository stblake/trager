(* ::Package:: *)

(* ::Title:: *)
(* Phase 5 -- Trager log-term construction                                   *)

(* ::Text:: *)
(* Given Phase-3's simple-pole remainder G/D (in z-frame) and Phase-4's    *)
(* residue decomposition (distinct residues with a chosen Z-basis), produce *)
(* the log-part                                                              *)
(*                                                                           *)
(*   sum_i  Zbasis[i] * log( v_i ) / order_i                                *)
(*                                                                           *)
(* of the antiderivative. Each v_i is an AF element; the pair (c_i, v_i)   *)
(* with c_i = Zbasis[i]/order_i represents an elementary log summand.      *)
(*                                                                           *)
(* This is a pure algebraic construction — no call to Integrate. The      *)
(* algorithm is the Z-basis decomposition of the residue span (Trager     *)
(* 1984 Ch 5 §1: residues span a finite-dimensional Q-vector space; pick *)
(* a Z-basis and form one residue divisor per basis direction). Each      *)
(* basis-direction divisor is then tested for principality / torsion via *)
(* the algorithms of Ch 6, yielding one log term per Z-basis element.    *)
(*                                                                           *)
(* PIPELINE.                                                                 *)
(*                                                                           *)
(* Let { r_1, ..., r_n } be the distinct residues of the differential and  *)
(* { Zbasis[1], ..., Zbasis[m] } a Z-basis of their Q-span with integer    *)
(* matrix M such that r_j = Sum_i M[j][i] * Zbasis[i].                     *)
(*                                                                           *)
(* 1. For each distinct residue r_j, build the residue divisor             *)
(*       Q_j := residueDivisor( Gtilde, D, r_j )                           *)
(*    whose support is the set of places at which the differential has    *)
(*    residue r_j (with the appropriate multiplicity).                     *)
(*                                                                           *)
(* 2. For each Zbasis index i, form the integer linear combination         *)
(*       D_i := Sum_j M[j][i] * Q_j                                        *)
(*    This has degree zero: row i of M^T corresponds to the "Zbasis[i]     *)
(*    direction" across residues, and Liouville's identity for the sum    *)
(*    of residues forces Sum_j M[j][i] * mult_j = 0 (the trace of the     *)
(*    residue divisor in the Zbasis[i] direction vanishes).                *)
(*                                                                           *)
(* 3. Test each D_i for principality (genus 0) or torsion (genus >= 1) via *)
(*    torsionIfCan. It returns (order_i, gen_i) with div(gen_i) =          *)
(*    order_i * D_i. For elementary integrands in the simple-radical       *)
(*    setting, order_i <= MaxTorsionOrder.                                 *)
(*                                                                           *)
(* 4. Emit log term  (Zbasis[i] / order_i) * log(gen_i).                   *)
(*                                                                           *)
(* PRINCIPAL-GENERATOR VERIFICATION.                                        *)
(*                                                                           *)
(* torsionIfCan's Verify hook is given integerCombinationVerifier[], which *)
(* checks that at every place P over supp(D) the candidate v satisfies    *)
(*   ord_P(v) = k * Sum_{j : P in supp(Q_j)} M[j][i]                      *)
(* This rules out spurious pole-free-at-infinity rows whose divisors are   *)
(* in I_D but are not N*D_i (higher-genus Jacobians can have multiple      *)
(* degree-0 divisors of the same support pattern).                          *)

(* ::Section:: *)
(* divisorZCombination -- integer linear combination of per-residue       *)
(* divisors, omitting zero-coefficient terms so we never ask divisorAdd   *)
(* to combine a trivial (A=1) divisor with a real one.                    *)

ClearAll[divisorZCombination];
divisorZCombination[exponents_List, Qlist_List, basis_?basisDescriptorQ,
                    y_Symbol] := Module[
  {pairs, nonZero, result, scaled},

  If[Length[exponents] =!= Length[Qlist],
    Return[incompleteFailure["DivisorZCombinationLengthMismatch",
      "ExponentLength" -> Length[exponents],
      "QlistLength"    -> Length[Qlist]]]
  ];

  pairs = Transpose[{exponents, Qlist}];
  nonZero = Select[pairs, #[[1]] =!= 0 &];

  If[nonZero === {},
    Return[incompleteFailure["DivisorZCombinationAllZero",
      "Exponents" -> exponents,
      "Reason"    -> "every integer coefficient is zero; combination is the \
identity divisor (principal, no log contribution)"]]
  ];

  result = divisorScale[nonZero[[1, 1]], nonZero[[1, 2]], basis];
  If[tragerFailureQ[result], Return[result]];

  Do[
    scaled = divisorScale[pair[[1]], pair[[2]], basis];
    If[tragerFailureQ[scaled], Return[scaled]];
    result = divisorAdd[result, scaled, basis];
    If[tragerFailureQ[result], Return[result]],
    {pair, Rest[nonZero]}
  ];

  result
];

(* ::Section:: *)
(* verifyPrincipalGeneratorForIntCombo                                     *)
(*                                                                           *)
(* Given a candidate v claimed to generate k * (Sum_j c_j * Q_j), verify   *)
(*   ord_P(v) = k * Sum_{j : P in supp(Q_j)} c_j                           *)
(* at every place P over supp(A). This is the integer-combination          *)
(* analogue of verifyPrincipalGeneratorForPair in PlaceOrder.m.             *)

ClearAll[verifyPrincipalGeneratorForIntCombo];
verifyPrincipalGeneratorForIntCombo[v_?afElementQ,
                                    exponents_List, Qlist_List,
                                    k_Integer,
                                    basis_?basisDescriptorQ, y_Symbol] :=
  Catch[Module[
    {A, places, hjVal, expOrdForThis, expOrd, actOrd, branchResult,
     unknownSeen = False},

    A = Qlist[[1]]["A"];
    places = enumeratePlacesOverA[A, basis, y];

    Do[
      Module[{beta = place["beta"], yBeta = place["yBeta"],
              isBranch = place["isBranch"]},

        expOrdForThis = 0;
        Do[
          hjVal = afValueAt[Qlist[[j]]["h"], beta, yBeta, basis, y];
          If[zeroQ[hjVal],
            expOrdForThis += exponents[[j]]
          ],
          {j, Length[Qlist]}
        ];
        expOrd = k * expOrdForThis;

        If[isBranch,
          If[expOrd =!= 0,
            unknownSeen = True;
            Continue[]
          ];
          branchResult = afOrderAtBranchPlace[v, beta, basis, y];
          Which[
            branchResult === 0, Null,
            branchResult === $Unknown, unknownSeen = True; Continue[],
            True, Throw[False]
          ],
          actOrd = afOrderAtNonBranchPlace[v, beta, yBeta, basis, y];
          If[actOrd === $Failed,
            unknownSeen = True; Continue[]
          ];
          actOrd = Simplify[actOrd];
          If[TrueQ[actOrd =!= expOrd],
            Throw[False]
          ]
        ]
      ],
      {place, places}
    ];

    If[unknownSeen, $Unknown, True]
  ]];

ClearAll[integerCombinationVerifier];
integerCombinationVerifier[exponents_List, Qlist_List,
                           basis_?basisDescriptorQ, y_Symbol] :=
  Function[{v, kVal},
    verifyPrincipalGeneratorForIntCombo[v, exponents, Qlist, kVal, basis, y]
  ];

(* ::Section:: *)
(* constructLogTerms                                                        *)

ClearAll[constructLogTerms];

Options[constructLogTerms] = {
  MaxTorsionOrder  -> 12,
  Multiplicities   -> Automatic,
  QBasis           -> Automatic,
  BasisCoeffs      -> Automatic
};

constructLogTerms[residues_List, remainderAF_?afElementQ, Dpoly_,
                  basis_?basisDescriptorQ, y_Symbol,
                  OptionsPattern[]] := Catch[Module[
  {n, z, maxOrd, mults, qBasis, basisCoeffs, GtildeStd, GtildeAF, Qlist,
   m, exponents, Di, verifier, tor, coeff, vArg, logTerms, qbInfo},

  n = basis["n"];
  z = basis["x"];
  maxOrd = OptionValue[MaxTorsionOrder];
  mults  = OptionValue[Multiplicities];
  If[mults === Automatic, mults = ConstantArray[1, Length[residues]]];

  qBasis      = OptionValue[QBasis];
  basisCoeffs = OptionValue[BasisCoeffs];

  If[qBasis === Automatic || basisCoeffs === Automatic,
    qbInfo = residueQBasis[residues];
    If[qBasis === Automatic,      qBasis      = qbInfo["qBasis"]];
    If[basisCoeffs === Automatic, basisCoeffs = qbInfo["basisCoeffs"]];
  ];

  (* Degenerate: empty residue list or zero-dim span -> no log part. *)
  If[residues === {} || qBasis === {}, Throw[{}]];

  If[Length[residues] =!= Length[basisCoeffs],
    Throw[incompleteFailure["ConstructLogTermsShapeMismatch",
      "ResidueCount"  -> Length[residues],
      "BasisCoeffRows" -> Length[basisCoeffs]]]
  ];

  (* Gtilde = remainder * Dpoly, reduced modulo y^n = g so Gtilde is    *)
  (* y-polynomial of degree < n with K(z) coefficients.                 *)
  GtildeStd = afToStandard[remainderAF, basis, y] * Dpoly;
  GtildeStd = reduceYDegree[Expand[GtildeStd], z, y, n, basis["g"]];
  GtildeAF  = afFromStandard[GtildeStd, basis, y];

  (* Build one residue divisor per distinct residue. *)
  Qlist = Table[
    Module[{Qj = residueDivisor[GtildeAF, Dpoly, residues[[j]], basis, y,
                                Multiplicity -> mults[[j]]]},
      If[tragerFailureQ[Qj], Throw[Qj]];
      Qj
    ],
    {j, Length[residues]}
  ];

  m = Length[qBasis];
  logTerms = {};

  Do[
    exponents = basisCoeffs[[All, i]];
    Di = divisorZCombination[exponents, Qlist, basis, y];
    If[tragerFailureQ[Di], Throw[Di]];

    verifier = integerCombinationVerifier[exponents, Qlist, basis, y];
    tor = torsionIfCan[Di, basis, y,
                       MaxOrder -> maxOrd,
                       Verify   -> verifier];
    If[tragerFailureQ[tor], Throw[tor]];

    If[tor["order"] === "failed",
      Throw[tragerFailure["NonElementary",
        "BasisElement"    -> qBasis[[i]],
        "BasisCoeffs"     -> exponents,
        "Divisor"         -> Di,
        "MaxTorsionOrder" -> maxOrd,
        "LastResult"      -> tor["lastResult"],
        "Reason"          -> "no principal k * D_i found within torsion bound; \
integrand has no elementary antiderivative (Liouville)"]]
    ];

    coeff = Together[qBasis[[i]] / tor["order"]];
    vArg  = afToStandard[tor["function"], basis, y];

    AppendTo[logTerms, {coeff, vArg}],
    {i, m}
  ];

  logTerms
]];
