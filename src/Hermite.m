(* ::Package:: *)

(* ::Title:: *)
(* Phase 3 -- hermiteReduce *)

(* ::Text:: *)
(* See TragerPlan.md Section 5.                                              *)
(*                                                                           *)
(* Reduces the multiple-pole part of an integrand to a simple-pole remainder.*)
(* Because the Trager basis w[i] = y^i / d[i] is diagonal (w[i]' = s_i w[i] *)
(* is a scalar multiple of w[i]), Trager's matrix M from the plan is        *)
(* diagonal: M[l, i] = E s_i * delta_{l, i}. The Hermite congruence decouples*)
(* into n independent scalar congruences per iteration:                     *)
(*                                                                           *)
(*   A[i] ≡ C_i(z) * B[i]   (mod V)    with C_i = U * (V s_i - k V')        *)
(*                                                                           *)
(* where s_i = i g'/(n g) - d[i]'/d[i]. When V does not divide g or d[i],   *)
(* V s_i vanishes mod V and C_i = -k U V'. When V does divide g (the branch *)
(* point case), V s_i contributes a non-zero rational constant mod V and   *)
(* must be kept. We compute C_i as a rational function, clear its           *)
(* denominator (which is coprime to V by construction), and solve via       *)
(* PolynomialExtendedGCD.                                                    *)

(* ::Section:: *)
(* Rationalize the integrand into AF form (K(z) coefficients).               *)

(* Given a rational expression in (z, y), returns an AF element whose        *)
(* coefficients are rational functions in z only. This folds any y in the    *)
(* denominator back into the numerator via the AF-ring inverse.              *)

ClearAll[rationalizeToAF];
rationalizeToAF[integrand_, basis_?basisDescriptorQ, y_Symbol] := Module[
  {n, g, z, together, num, den, numReduced, denReduced, numAF, denAF, invAF},
  n = basis["n"]; g = basis["g"]; z = basis["x"];
  together = Together[integrand];
  num = reduceYDegree[Numerator[together], z, y, n, g];
  den = reduceYDegree[Denominator[together], z, y, n, g];
  numAF = afFromStandard[num, basis, y];
  denAF = afFromStandard[den, basis, y];
  invAF = afInverse[denAF, basis];
  afTimes[numAF, invAF, basis]
];

(* Extract the common K[z] denominator of an AF element's coefficients.     *)
(* Returns {A_list, D} with A_i = D * coeff_i  (so A_i ∈ Q[z]).               *)

ClearAll[commonDenominatorAF];
commonDenominatorAF[af_?afElementQ, z_Symbol] := Module[{coeffs, denoms, denom, A},
  coeffs = Together /@ af["Coeffs"];
  denoms = Denominator /@ coeffs;
  denom = PolynomialLCM @@ denoms;
  A = Table[Together[denom * coeffs[[i]]], {i, Length[coeffs]}];
  <|"A" -> A, "D" -> denom|>
];

(* ::Section:: *)
(* hermiteReduce                                                             *)

ClearAll[hermiteReduce];

(* checkPoleAt (optional): when given a value, assert algPart has no pole at *)
(* basis["x"] == checkPoleAt after reduction. This is the plan's non-elementarity *)
(* invariant (post-phase-2 z=0 case) and is not a meaningful check on the    *)
(* un-shifted input -- callers outside the pipeline should omit it.          *)

hermiteReduce[integrand_, basis_?basisDescriptorQ, y_Symbol,
              checkPoleAt_: Missing[]] := Catch[Module[
  {n, g, d, z, integrandAF, algAF,
   iter, maxIter, ad, Acoeffs, denom, factors, sortedFactors, V, j, U, k, Vprime,
   BList, congBase, egcd, sFactor, Bi, HCoeffs, HAF, dHAF,
   algCoeffs, coeff, invariantOK, finalAD},

  n = basis["n"]; g = basis["g"]; d = basis["d"]; z = basis["x"];

  integrandAF = rationalizeToAF[integrand, basis, y];
  algAF = afMake[ConstantArray[0, n], basis];

  maxIter = 100;       (* safety cap; Hermite terminates well before this *)
  iter = 0;

  (* --- main Hermite loop --- *)
  While[True,
    iter++;
    If[iter > maxIter,
      Throw[tragerFailure["InternalInconsistency",
        "Invariant" -> "HermiteIterationCap",
        "iter" -> iter, "denom" -> denom
      ]]
    ];

    ad = commonDenominatorAF[integrandAF, z];
    Acoeffs = ad["A"]; denom = ad["D"];

    (* Find a factor V of denom with multiplicity >= 2, preferring highest mult.*)
    (* FactorSquareFreeList[denom] returns {{const, 1}, {sq-free factor, mult}, ...} *)
    factors = Rest[FactorSquareFreeList[denom]];
    sortedFactors = SortBy[factors, -Last[#] &];
    If[sortedFactors === {} || Last[First[sortedFactors]] < 2,
      Break[]
    ];
    {V, j} = First[sortedFactors];
    U = PolynomialQuotient[denom, V^j, z];
    k = j - 1;
    Vprime = D[V, z];              (* Mathematica's built-in derivative *)

    (* --- solve the n congruences A[i] ≡ C_i * B[i] (mod V), i = 0..n-1 --- *)
    BList = Table[
      Module[{si, Ci, CiNum, CiDen, egcd, sFact},
        si = Together[
          i * D[g, z] / (n * g) - D[d[[i + 1]], z] / d[[i + 1]]
        ];
        Ci = Together[U * (V * si - k * Vprime)];
        CiNum = Numerator[Ci];
        CiDen = Denominator[Ci];
        egcd = PolynomialExtendedGCD[CiNum, V, z];
        If[!PolynomialQ[egcd[[1]], z] || Exponent[egcd[[1]], z] > 0,
          Throw[tragerFailure["InternalInconsistency",
            "Invariant" -> "HermiteNonInvertibleCongruence",
            "V" -> V, "U" -> U, "k" -> k, "i" -> i,
            "Ci" -> Ci, "gcd" -> egcd[[1]]
          ]]
        ];
        sFact = egcd[[2, 1]] / egcd[[1]];
        (* B_i * Ci ≡ A_i (mod V)                                           *)
        (* <=> B_i * CiNum ≡ A_i * CiDen (mod V)                           *)
        (* <=> B_i ≡ A_i * CiDen * sFact (mod V)                           *)
        PolynomialRemainder[
          Expand[Acoeffs[[i + 1]] * CiDen * sFact], V, z
        ]
      ],
      {i, 0, n - 1}
    ];

    (* --- build H = Sum[B_i w_i / V^k] and its derivative --- *)
    HCoeffs = Together[# / V^k] & /@ BList;
    HAF = afMake[HCoeffs, basis];
    dHAF = afD[HAF, basis];

    algAF = afPlus[algAF, HAF, basis];
    integrandAF = afMinus[integrandAF, dHAF, basis];
  ];

  (* --- pole-at-infinity invariant (pipeline-level, opt-in) --- *)
  (* When checkPoleAt is provided, assert that algAF has no pole at         *)
  (* basis["x"] == checkPoleAt. Used by the pipeline with checkPoleAt = 0   *)
  (* after phase-2 (z = 0 corresponds to x = infinity).                     *)
  If[!MissingQ[checkPoleAt],
    invariantOK = AllTrue[algAF["Coeffs"], Function[c,
      Module[{denomC = Denominator[Together[c]]},
        (denomC /. z -> checkPoleAt) =!= 0
      ]
    ]];
    If[!invariantOK,
      Throw[tragerFailure["InternalInconsistency",
        "Invariant" -> "PoleAtInfinityAfterHermite",
        "algPart" -> algAF,
        "checkPoleAt" -> checkPoleAt,
        "g" -> g, "n" -> n
      ]]
    ]
  ];

  (* --- final extraction: remainder in (A_i, D) form --- *)
  finalAD = commonDenominatorAF[integrandAF, z];

  <|
    "algPart"   -> algAF,
    "remainder" -> integrandAF,
    "remainderA" -> finalAD["A"],
    "D"         -> finalAD["D"],
    "iterations" -> iter - 1
  |>
]];
