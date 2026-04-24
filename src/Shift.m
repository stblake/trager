(* ::Package:: *)

(* ::Title:: *)
(* Phase 2 -- shiftAwayFromInfinity *)

(* ::Text:: *)
(* See TragerPlan.md Section 4.                                              *)
(*                                                                           *)
(* Applies the Mobius substitution x = a + 1/z with a chosen a in Q, then    *)
(* absorbs the appropriate power of z into the algebraic generator so that  *)
(* the transformed relation is y^n = gNew(z) with gNew a polynomial. The    *)
(* key bookkeeping step is the ceil(m/n) scaling: with m = deg_x(g),        *)
(*   k = Ceiling[m/n],  y_new = y * z^k,  gNew(z) = z^(kn - m) * G(z)       *)
(* where G(z) = z^m * g(a + 1/z). The exponent kn - m is in {0, ..., n-1}, *)
(* so gNew is always a polynomial in z.                                      *)
(*                                                                           *)
(* After constructing gNew we re-run reduceIrreducibility to fold any       *)
(* high-multiplicity z-factors produced by the scaling into the generator.  *)

(* ::Section:: *)
(* shiftAwayFromInfinity                                                     *)

ClearAll[shiftAwayFromInfinity];

shiftAwayFromInfinity[integrand_, x_Symbol, y_Symbol, n_Integer, g_,
                     z_Symbol, searchBound_Integer: 32] := Module[
  {a, aCandidates, denomXY, integrandAtA, gAtA, m, G, k, kMinusMTotal,
   gNewRaw, reduction, gNewReduced, nReduced, yScaleFromReduce, yScaleTotal,
   ySubstitution, integrandTransformed, differentialFactor, genus},


  (* --- Steps 1 + 2: choose a and construct gNew(z) ---                     *)
  (* For each candidate a we compute the transformed radicand               *)
  (*   gNew_raw(z) = z^(kn - m) * z^m * g(a + 1/z)                          *)
  (* and accept the first a such that                                        *)
  (*   (i)  the integrand's (x,y)-denominator does not vanish at x = a      *)
  (*   (ii) gNew_raw is a non-constant polynomial in z                      *)
  (* Condition (ii) subsumes the stricter "a not a root of g" rule from the *)
  (* plan: allowing a to be a root of g is fine as long as the Mobius image *)
  (* doesn't degenerate, which only happens when a is a root of full        *)
  (* multiplicity m of g and n divides m -- a case reduceIrreducibility     *)
  (* already would have collapsed to DegenerateRadical in phase 0.          *)
  aCandidates = Join[{0}, Flatten[Table[{i, -i}, {i, 1, searchBound}]]];
  denomXY = Denominator[Together[integrand]];
  m = Exponent[g, x];
  k = Ceiling[m/n];
  kMinusMTotal = k*n - m;                 (* in {0, 1, ..., n-1} *)

  Module[{found = Missing[], candidateGNew = Null},
    Do[
      If[MissingQ[found],
        integrandAtA = Expand[denomXY /. x -> cand];
        If[integrandAtA =!= 0,
          G = Expand[z^m * (g /. x -> cand + 1/z)];
          gNewRaw = Expand[G * z^kMinusMTotal];
          If[PolynomialQ[gNewRaw, z] && !FreeQ[gNewRaw, z],
            found = cand;
            candidateGNew = gNewRaw
          ]
        ];
      ],
      {cand, aCandidates}
    ];
    a = found;
    gNewRaw = candidateGNew
  ];

  If[MissingQ[a],
    Return[tragerFailure["InfinityShiftFailed",
      "Bound" -> searchBound,
      "Reason" -> "no rational a in the search range produced a valid non-constant gNew and a non-vanishing integrand denominator",
      "g" -> g
    ]]
  ];

  (* --- Step 3: fold high-multiplicity factors via reduceIrreducibility --- *)
  reduction = reduceIrreducibility[n, gNewRaw, z];
  If[tragerFailureQ[reduction], Return[reduction]];
  nReduced          = reduction["n"];
  gNewReduced       = reduction["g"];
  yScaleFromReduce  = reduction["yScale"];
  (* yScaleTotal is the ratio y_new / y_old in the z-variable. The initial  *)
  (* shift sets y_mid = y_old * z^k (so y_mid^n = gNew_raw); reduce then   *)
  (* sets y_new = y_mid / yScale_reduce. Composing: y_new/y_old = z^k /    *)
  (* yScale_reduce. Getting this direction wrong breaks the round-trip.    *)
  yScaleTotal       = Together[z^k / yScaleFromReduce];

  (* --- Step 4: transform the integrand ---                                 *)
  (* Substitutions:                                                          *)
  (*   x       -> a + 1/z                                                   *)
  (*   y_old   -> y_new / yScaleTotal    (capturing both the z^k step and   *)
  (*                                     anything reduceIrreducibility ate)*)
  (*   dx      -> -dz / z^2                                                 *)
  (* We keep the symbol y; inside the transformed integrand it now plays    *)
  (* the role of y_new (with y^n = gNewReduced in the z variable).          *)
  ySubstitution = y / yScaleTotal;
  differentialFactor = -1/z^2;
  integrandTransformed = Together[
    (integrand /. {x -> a + 1/z, y -> ySubstitution}) * differentialFactor
  ];
  integrandTransformed =
    reduceYDegree[integrandTransformed, z, y, nReduced, gNewReduced];

  (* --- Step 5: genus sanity check ---                                      *)
  (* Birational maps preserve genus. We first put the input curve into its  *)
  (* absolutely irreducible form (genus is only defined there), then compare*)
  (* against the shifted/reduced curve's genus.                             *)
  Module[{inputReduced, genusBefore, genusAfter},
    inputReduced = reduceIrreducibility[n, g, x];
    If[tragerFailureQ[inputReduced],
      genusBefore = -1,     (* can't be computed; skip comparison *)
      genusBefore = computeGenus[inputReduced["n"], inputReduced["g"], x]
    ];
    genusAfter = computeGenus[nReduced, gNewReduced, z];
    If[genusBefore >= 0 && genusAfter =!= genusBefore,
      Return[tragerFailure["InternalInconsistency",
        "Invariant" -> "GenusNotPreservedByBirational",
        "GenusBefore" -> genusBefore,
        "GenusAfter" -> genusAfter,
        "g" -> g, "gNew" -> gNewReduced, "n" -> nReduced, "a" -> a
      ]]
    ]
  ];

  (* --- Step 6: build the inversion closure and return ---                  *)
  (* The inverse converts an expression in (z, y_new) to (x, y_old) via     *)
  (* z -> 1/(x - a) and y_new -> y_old * yScaleTotal(1/(x - a)). It does    *)
  (* NOT undo the -1/z^2 differential factor -- that is the caller's job    *)
  (* when a round-trip is required (see tests).                             *)
  Module[{aVal = a, xVar = x, yVar = y, zVar = z, ySubstInv},
    ySubstInv = yScaleTotal /. z -> 1/(xVar - aVal);
    <|
      "integrand" -> integrandTransformed,
      "z" -> z,
      "n" -> nReduced,
      "g" -> gNewReduced,
      "yScale" -> yScaleTotal,
      "a" -> a,
      "inverse" -> Function[expr,
        expr /. {zVar -> 1/(xVar - aVal), yVar -> yVar * ySubstInv}
      ]
    |>
  ]
];
