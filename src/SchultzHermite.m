(* ::Package:: *)

(* ::Title:: *)
(* Schultz 2015 §4.3 -- infinity-aware Hermite reduction *)

(* ::Text:: *)
(* See SchultzPlan.md §S.3 and Sch §4.3 (Lemmas 4.4-4.5, eq. 4.6-4.9).        *)
(*                                                                            *)
(* Subsumes the Mobius-shift Phase 2 (src/Shift.m) and finite Hermite Phase 3 *)
(* (src/Hermite.m) into a single reduction that handles BOTH finite multiple *)
(* poles AND poles at infinity directly, in the η-basis of the integral      *)
(* basis equipped with the Sch §4 infinity exponents δ_i (basis["deltas"]).  *)
(*                                                                            *)
(* Pipeline:                                                                  *)
(*   1. Express ω = Σ_i (a_i / b) η_i dx, with η_i = w_{i-1} = y^{i-1}/d_{i-1}.*)
(*   2. While b is not squarefree: solve the Trager finite congruence        *)
(*      A_i ≡ -k U V' B_i + T Σ_l B_l M_{l, i}  (mod V)                       *)
(*      and subtract d(Σ_i B_i η_i / V^k) into algPart. (Lemma 4.4 part 1.)  *)
(*   3. Once b is squarefree, check `deg(a_i) + δ_i < deg(b)` for every i.   *)
(*      If yes, no pole-at-infinity issue: done.                              *)
(*   4. Otherwise (Lemma 4.4 part 2 / eq. 4.7-4.9), seek f_i, g_i ∈ k[x] with*)
(*        a_i = b·f_i' + (b/E)·Σ_j f_j·M_{j,i} + g_i                          *)
(*        deg(f_i) ≤ N − δ_i,  deg(g_i) < deg(b) − δ_i                       *)
(*        N := max_i(deg a_i + δ_i + 1 − deg b)                               *)
(*      and subtract Σ_i f_i η_i into algPart.                                 *)
(*      Solvable ⇒ remainder is "Schultz-good". Unsolvable ⇒ defer to the   *)
(*      §S.6 fail-in-style decomposition.                                     *)
(*                                                                            *)
(* Return shape:                                                              *)
(*    <|                                                                       *)
(*      "algPart"   -> AF element (the integrated piece),                     *)
(*      "remainder" -> AF element (the un-integrated piece),                  *)
(*      "D"         -> squarefree finite denominator b ∈ k[x],                *)
(*      "Dinf"      -> <|                                                      *)
(*         "solvable" -> True | False,                                         *)
(*         "N"        -> integer (eq. 4.7 degree budget),                     *)
(*         "deltas"   -> basis["deltas"]                                       *)
(*       |>,                                                                    *)
(*      "iterations" -> integer (finite-Hermite iterations used)               *)
(*    |>                                                                        *)

(* ::Section:: *)
(* η-basis derivation matrix (Sch §4.3).                                       *)
(*                                                                              *)
(* Returns the n × n matrix M ∈ k[x]^{n×n} with                                *)
(*    E·η_i' = Σ_j M[j, i] · η_j         where E = n·g·d_{n-1}.                *)
(* For the simple-radical normal basis η_i = w_{i-1} = y^{i-1}/d_{i-1},       *)
(* η_i' = s_{i-1} η_i with s_{i-1} = (i-1)·g'/(n·g) − d_{i-1}'/d_{i-1}, so M  *)
(* is diagonal:                                                                  *)
(*    M[i, i] = E·s_{i-1}                                                       *)
(*            = (i-1)·g'·d_{n-1} − n·g·(d_{n-1}/d_{i-1})·d_{i-1}'              *)
(* (always polynomial since d_{i-1} | d_{n-1} by basis normality).             *)
(*                                                                              *)
(* The function is written generically against the basis descriptor so that   *)
(* once a non-diagonal η-basis is supplied (e.g. for general algebraic       *)
(* extensions), the same call site continues to work.                          *)

ClearAll[integralBasisDerivativeMatrix];
integralBasisDerivativeMatrix[basis_?basisDescriptorQ] := Module[
  {n, g, d, x, gp, dn1, M, di, dipi},
  n = basis["n"]; g = basis["g"]; d = basis["d"]; x = basis["x"];
  gp = D[g, x];
  dn1 = d[[n]];
  M = ConstantArray[0, {n, n}];
  Do[
    di = d[[i]];
    dipi = D[di, x];
    M[[i, i]] = Together[
      (i - 1) * gp * dn1 - n * g * (dn1 / di) * dipi
    ],
    {i, 1, n}
  ];
  M
];

(* ::Section:: *)
(* Finite squarefree-decomposition step.                                       *)
(*                                                                              *)
(* Given an AF element ω = Σ_i (a_i/b) η_i dx (after rationalizeToAF +         *)
(* commonDenominatorAF), find a factor V of b with multiplicity j ≥ 2.        *)
(* Returns Missing[] if b is squarefree.                                        *)

ClearAll[schultzPickHighMultiplicityFactor];
schultzPickHighMultiplicityFactor[b_, x_Symbol] := Module[
  {factors, sortedFactors, V, j},
  factors = Rest[FactorSquareFreeList[b]];
  sortedFactors = SortBy[factors, -Last[#] &];
  If[sortedFactors === {} || Last[First[sortedFactors]] < 2,
    Missing["squarefree"],
    {V, j} = First[sortedFactors];
    {V, j}
  ]
];

(* schultzSolveFiniteCongruence[Acoeffs, b, V, j, M, basis] -> {BList, HAF}.   *)
(*                                                                              *)
(* Solves the n simultaneous congruences (Sch eq. 4.6 / Trager Ch 4 §2 eq.11)  *)
(*    A_i ≡ -k·U·V'·B_i + T·Σ_l B_l·M_{l,i}  (mod V)                           *)
(* with U = b/V^j, k = j-1, T = U·V/E, E = n·g·d_{n-1}. Returns the polynomial*)
(* B_i list and assembles H = Σ_i B_i η_i / V^k as an AF element so the       *)
(* caller can compute dH and subtract.                                          *)
(*                                                                              *)
(* For the simple-radical w-basis, M is diagonal and the system decouples per *)
(* i — exactly what the existing src/Hermite.m solves, so this function      *)
(* must agree with hermiteReduce per-iteration on simple-radical input. The   *)
(* general formulation (using the η-basis derivation matrix M) is in place    *)
(* for future non-diagonal bases.                                               *)

ClearAll[schultzSolveFiniteCongruence];
schultzSolveFiniteCongruence[
  Acoeffs_List, b_, V_, j_Integer, MMat_List, basis_?basisDescriptorQ
] := Module[
  {n, g, d, x, dn1, E, U, k, Vprime, T, BList},
  n = basis["n"]; g = basis["g"]; d = basis["d"]; x = basis["x"];
  dn1 = d[[n]];
  E = Together[n * g * dn1];
  U = PolynomialQuotient[b, V^j, x];
  k = j - 1;
  Vprime = D[V, x];
  T = Together[U * V / E];

  (* For diagonal M (the simple-radical case) the system decouples per i.      *)
  (* The general non-diagonal case is left for future bases — the simple-      *)
  (* radical scope of this plan is fully covered by the diagonal branch.       *)
  BList = Table[
    Module[{Mii, Ci, CiNum, CiDen, egcd, sFact},
      Mii = MMat[[i, i]];
      (* C_i = T·M[i, i] − k·U·V' (the "in-basis" coefficient of B_i in the    *)
      (* finite Hermite congruence). For diagonal M this matches the U·(V s_i  *)
      (* − k V') of src/Hermite.m bit-for-bit since T·M[i,i] = U·V·s_{i-1}.    *)
      Ci = Together[T * Mii - k * U * Vprime];
      CiNum = Numerator[Ci]; CiDen = Denominator[Ci];
      egcd = PolynomialExtendedGCD[CiNum, V, x];
      If[!PolynomialQ[egcd[[1]], x] || Exponent[egcd[[1]], x] > 0,
        Throw[tragerFailure["InternalInconsistency",
          "Invariant" -> "SchultzHermiteNonInvertibleCongruence",
          "V" -> V, "U" -> U, "k" -> k, "i" -> i,
          "Ci" -> Ci, "gcd" -> egcd[[1]]
        ]]
      ];
      sFact = egcd[[2, 1]] / egcd[[1]];
      PolynomialRemainder[
        Expand[Acoeffs[[i]] * CiDen * sFact], V, x
      ]
    ],
    {i, 1, n}
  ];
  BList
];

(* ::Section:: *)
(* Infinity linear system (Sch §4.3 eq. 4.7-4.9).                              *)
(*                                                                              *)
(* Inputs: a_i ∈ k[x] (current numerators of integrand mod squarefree b),     *)
(*         b ∈ k[x] squarefree, basis with δ_i.                                 *)
(* Decision: if deg(a_i) + δ_i < deg(b) for every i, the form has no pole at  *)
(*           infinity that needs absorbing — return solvable = True with no   *)
(*           change.                                                            *)
(* Otherwise: parametrize f_i = Σ_l u_{i,l}·x^l with deg ≤ N − δ_i,           *)
(*            g_i = Σ_l v_{i,l}·x^l with deg < deg(b) − δ_i,                   *)
(*            and solve the linear system over k arising from the polynomial  *)
(*            identity                                                          *)
(*               a_i = b·f_i' + (b/E)·Σ_j f_j·M_{j,i} + g_i.                   *)
(*                                                                              *)
(* The polynomial identity may have rational-function intermediate terms      *)
(* (b·f_j/E·M_{j,i}); we clear by multiplying through by the LCM of the per-   *)
(* term denominators (always a divisor of E·d_{i-1} for the diagonal case).  *)
(* Mathematica's SolveAlways handles this directly: equate the resulting     *)
(* polynomial coefficients to zero and solve over k.                          *)

(* schultzInfinityNeedsReductionQ[Acoeffs, b, deltas, x] -> True | False.       *)

ClearAll[schultzInfinityNeedsReductionQ];
schultzInfinityNeedsReductionQ[Acoeffs_List, b_, deltas_List, x_Symbol] :=
  Module[{degB, degsA, i, n},
    n = Length[Acoeffs];
    degB = Exponent[b, x];
    AnyTrue[Range[n], Function[i,
      Module[{ai = Together[Acoeffs[[i]]], degAi},
        degAi = If[zeroQ[ai], -Infinity, Exponent[ai, x]];
        degAi + deltas[[i]] >= degB
      ]
    ]]
  ];

(* schultzInfinityBudget[Acoeffs, b, deltas, x] -> integer N (eq. 4.7).         *)

ClearAll[schultzInfinityBudget];
schultzInfinityBudget[Acoeffs_List, b_, deltas_List, x_Symbol] :=
  Module[{degB, n, vals, i},
    n = Length[Acoeffs];
    degB = Exponent[b, x];
    vals = Table[
      Module[{ai = Together[Acoeffs[[i]]], degAi},
        degAi = If[zeroQ[ai], -Infinity, Exponent[ai, x]];
        degAi + deltas[[i]] + 1 - degB
      ],
      {i, 1, n}
    ];
    Max[vals, 0]
  ];

(* schultzSolveInfinityLinearSystem[Acoeffs, b, basis] -> Association.          *)
(*                                                                              *)
(* Returns                                                                      *)
(*    <|"solvable" -> True,  "fList" -> {f_1, ..., f_n}, "N" -> N|>             *)
(* on success, or                                                               *)
(*    <|"solvable" -> False, "N" -> N|>                                         *)
(* if the linear system has no solution over k.                                 *)
(*                                                                              *)
(* Sch §4.3 (page 13) requires the assumption E | b before the polynomial       *)
(* identity a_i = E·T·f_i' + T·Σ_j f_j·M_{j,i} + g_i can be solved with f_i,    *)
(* g_i ∈ k[x]: with T = b/E this gives b·f_i' + (b/E)·Σ M f + g_i, where the   *)
(* middle term needs E | b for `T·M_{j,i} = (b/E)·M_{j,i}` to land in k[x].    *)
(* When the integrand's b does not satisfy E | b, the paper says: "we multiply *)
(* the a_i and b by a suitable common factor so that there there is a          *)
(* polynomial T with b = ET". We implement that as scale = E/gcd(E,b); then    *)
(* new_b = scale·b satisfies E | new_b, and we work with (scale·a_i, new_b)    *)
(* throughout. The output f_i is unchanged by this rescaling — it represents   *)
(* the SAME exact differential dF — so callers do not see the rescale.         *)

ClearAll[schultzSolveInfinityLinearSystem];
schultzSolveInfinityLinearSystem[
  Acoeffs_List, b_, basis_?basisDescriptorQ
] := Module[
  {n, g, d, x, deltas, dn1, E, MMat, degB, N0,
   scale, bScaled, AScaled, degBScaled,
   fPolys, gPolys, equations, eqList, vars, sol, fSolved,
   ulist, vlist},
  n = basis["n"]; g = basis["g"]; d = basis["d"]; x = basis["x"];
  deltas = basis["deltas"];
  dn1 = d[[n]];
  E = Together[n * g * dn1];
  MMat = integralBasisDerivativeMatrix[basis];
  degB = Exponent[b, x];

  (* If no reduction needed, return trivially solvable.                       *)
  If[!schultzInfinityNeedsReductionQ[Acoeffs, b, deltas, x],
    Return[<|
      "solvable" -> True,
      "fList"    -> ConstantArray[0, n],
      "N"        -> 0
    |>]
  ];

  N0 = schultzInfinityBudget[Acoeffs, b, deltas, x];

  (* Sch §4.3 rescaling: enforce E | b_scaled by multiplying a_i and b by      *)
  (* scale = E / gcd(E, b). The deg(g_i) bound moves up to deg(b_scaled) − δ_i.*)
  (* The N bound is rescaling-invariant (deg(a_i) − deg(b) is preserved).      *)
  scale = Together[E / PolynomialGCD[E, b]];
  bScaled = Expand[scale * b];
  AScaled = Expand[scale * #] & /@ Acoeffs;
  degBScaled = Exponent[bScaled, x];

  (* Allocate symbolic coefficient unknowns. We use temporary unique symbols   *)
  (* — Module[{...}, Unique[]] would also work, but Table[Unique[]] keeps     *)
  (* names traceable in failure metadata.                                      *)
  ulist = Table[
    Table[Unique["u" <> ToString[i] <> "n"], {l, 0, Max[N0 - deltas[[i]], -1]}],
    {i, 1, n}
  ];
  vlist = Table[
    Table[Unique["v" <> ToString[i] <> "n"],
      {l, 0, Max[degBScaled - deltas[[i]] - 1, -1]}],
    {i, 1, n}
  ];

  (* f_i(x) = Σ_l u_{i,l} x^l, deg ≤ N − δ_i. If N − δ_i < 0 the polynomial  *)
  (* is zero (no unknowns).                                                    *)
  fPolys = Table[
    If[N0 - deltas[[i]] < 0,
      0,
      Sum[ulist[[i, l + 1]] * x^l, {l, 0, N0 - deltas[[i]]}]
    ],
    {i, 1, n}
  ];
  gPolys = Table[
    If[degBScaled - deltas[[i]] - 1 < 0,
      0,
      Sum[vlist[[i, l + 1]] * x^l,
        {l, 0, degBScaled - deltas[[i]] - 1}]
    ],
    {i, 1, n}
  ];

  (* Equation (after rescaling): a_scaled_i = b_scaled·f_i' +                  *)
  (* (b_scaled/E)·Σ_j f_j·M_{j,i} + g_i. Multiply through by E to keep         *)
  (* everything polynomial; SolveAlways then equates x-coefficients to 0.      *)
  equations = Table[
    Module[{lhs, rhs, sumPart},
      sumPart = Sum[fPolys[[j]] * MMat[[j, i]], {j, 1, n}];
      lhs = E * AScaled[[i]];
      rhs = E * bScaled * D[fPolys[[i]], x] + bScaled * sumPart +
            E * gPolys[[i]];
      Together[lhs - rhs]
    ],
    {i, 1, n}
  ];

  vars = Flatten[Join[ulist, vlist]];

  (* SolveAlways expects {eq1 == 0, eq2 == 0, ...}. We feed numerators since  *)
  (* "Together" guarantees each equation is a single rational expression with *)
  (* all unknowns in the numerator (denominators are E·k[x] units, which are *)
  (* nonzero for generic x — Sch's formulation guarantees this).               *)
  eqList = Map[Numerator[#] == 0 &, equations];

  sol = Quiet @ SolveAlways[eqList, x];

  If[sol === {} || !MatchQ[sol, {_List, ___}],
    (* No solution — system is unsolvable, fail-in-style territory.            *)
    Return[<|"solvable" -> False, "N" -> N0|>]
  ];

  fSolved = Together[fPolys /. First[sol]];
  (* SolveAlways may leave free unknowns; substitute them to 0 to get one     *)
  (* canonical solution.                                                       *)
  fSolved = fSolved /. (s_Symbol /; MemberQ[vars, s]) -> 0;

  <|
    "solvable" -> True,
    "fList"    -> fSolved,
    "N"        -> N0
  |>
];

(* ::Section:: *)
(* Top-level schultzHermiteReduce.                                              *)

ClearAll[schultzHermiteReduce];
schultzHermiteReduce[
  integrand_, basis_?basisDescriptorQ, y_Symbol
] := Catch[Module[
  {n, g, d, x, dn1, E, MMat, integrandAF, algAF,
   iter, maxIter, ad, Acoeffs, denom, factorPick, V, j, U, k, BList,
   HCoeffs, HAF, dHAF, finalAD, infResult, fList, FAF, dFAF},

  n = basis["n"]; g = basis["g"]; d = basis["d"]; x = basis["x"];
  dn1 = d[[n]];
  E = Together[n * g * dn1];
  MMat = integralBasisDerivativeMatrix[basis];

  integrandAF = rationalizeToAF[integrand, basis, y];
  algAF = afMake[ConstantArray[0, n], basis];

  (* Phase A: finite multiple-pole loop. Identical structure to                *)
  (* src/Hermite.m's main loop, but using the η-basis derivation matrix M     *)
  (* via schultzSolveFiniteCongruence.                                         *)
  maxIter = 100; iter = 0;
  While[True,
    iter++;
    If[iter > maxIter,
      Throw[tragerFailure["InternalInconsistency",
        "Invariant" -> "SchultzHermiteIterationCap",
        "iter" -> iter
      ]]
    ];
    ad = commonDenominatorAF[integrandAF, x];
    Acoeffs = ad["A"]; denom = ad["D"];
    factorPick = schultzPickHighMultiplicityFactor[denom, x];
    If[MissingQ[factorPick], Break[]];
    {V, j} = factorPick;
    BList = schultzSolveFiniteCongruence[Acoeffs, denom, V, j, MMat, basis];
    HCoeffs = Together[# / V^(j - 1)] & /@ BList;
    HAF = afMake[HCoeffs, basis];
    dHAF = afD[HAF, basis];
    algAF = afPlus[algAF, HAF, basis];
    integrandAF = afMinus[integrandAF, dHAF, basis];
  ];

  (* Phase B: at this point denom is squarefree. Test pole-at-infinity         *)
  (* condition; if violated, attempt the Sch §4.3 linear-system reduction.     *)
  ad = commonDenominatorAF[integrandAF, x];
  Acoeffs = ad["A"]; denom = ad["D"];

  infResult = schultzSolveInfinityLinearSystem[Acoeffs, denom, basis];

  If[infResult["solvable"] && AnyTrue[infResult["fList"], !zeroQ[#] &],
    (* Subtract dF where F = Σ_i f_i η_i. The η_i-coefficients of F as an AF  *)
    (* element are exactly fList — η_i is w_{i-1}, so the i-th coefficient of *)
    (* F in the w-basis is f_i.                                                *)
    fList = infResult["fList"];
    FAF = afMake[fList, basis];
    dFAF = afD[FAF, basis];
    algAF = afPlus[algAF, FAF, basis];
    integrandAF = afMinus[integrandAF, dFAF, basis];
    (* Recompute denom after the subtraction; it should remain squarefree     *)
    (* and the pole-at-infinity condition should now hold.                    *)
    ad = commonDenominatorAF[integrandAF, x];
    Acoeffs = ad["A"]; denom = ad["D"];
  ];

  finalAD = commonDenominatorAF[integrandAF, x];

  <|
    "algPart"    -> algAF,
    "remainder"  -> integrandAF,
    "remainderA" -> finalAD["A"],
    "D"          -> finalAD["D"],
    "Dinf"       -> <|
      "solvable" -> infResult["solvable"],
      "N"        -> infResult["N"],
      "deltas"   -> basis["deltas"]
    |>,
    "iterations" -> iter - 1
  |>
]];
