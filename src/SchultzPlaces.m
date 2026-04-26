(* ::Package:: *)

(* ::Title:: *)
(* Schultz 2015 §4.4 -- ramification structure, divisor of dx, and D_l         *)

(* ::Text:: *)
(* See SchultzPlan.md §S.4 and Sch §4.4 (Lemma 4.6).                            *)
(*                                                                              *)
(* For the simple-radical case y^n = g(x) the ramification structure is        *)
(* completely determined by the squarefree decomposition g = c·∏_j p_j^{e_j} : *)
(*                                                                              *)
(*   - Over each ℚ-irreducible factor p_j there are gcd(n, e_j) places, each *)
(*     of ramification index ℓ_j = n / gcd(n, e_j).                            *)
(*   - At infinity there are d_∞ = gcd(n, deg g) places, each of ramification *)
(*     ℓ_∞ = n / d_∞.                                                            *)
(*                                                                              *)
(* Lemma 4.6 prescribes an iterative algorithm `A_n / B_n` for computing the   *)
(* divisor `D_l = Σ_{r(P) = l} P` without Puiseux expansions. For the simple- *)
(* radical scope of this project — and especially for SQUAREFREE g, which     *)
(* already covers every Tier 1 / Tier 1b test in the plan — that iteration   *)
(* collapses to the direct formulas below. The full Lemma 4.6 iteration is    *)
(* deferred to a later pass; the same downstream API (`schultzDlDivisor`,    *)
(* `divisorOfDx`) will then continue to work because the underlying ideal    *)
(* representations are identical.                                              *)
(*                                                                              *)
(* --- Why the direct construction works for the simple-radical normal basis -*)
(*                                                                              *)
(* At a finite place P over α (a root of p_j of multiplicity e_α := e_j),    *)
(* with ramification ℓ_α := ℓ_j = n / gcd(n, e_α) and y-order μ_α := e_α /     *)
(* gcd(n, e_α), the order of η_i = w_{i-1} at P is                             *)
(*                                                                              *)
(*   ord_P(η_i) = (i-1)·μ_α − ℓ_α·v_α(d_{i-1})                                *)
(*             = (i-1)·μ_α − ℓ_α·⌊(i-1)·e_α / n⌋.                              *)
(*                                                                              *)
(* For squarefree g (e_α = 1 for every factor): μ_α = 1, ℓ_α = n, and          *)
(*   ord_P(η_i) = (i-1) − n·⌊(i-1)/n⌋ = i − 1   for 1 ≤ i ≤ n.                *)
(*                                                                              *)
(* The ideal of f ∈ K with ord_P(f) ≥ M at every ramification-ℓ_α place has,  *)
(* in the η-basis, an a-matrix that is diag(p_l_finite^{m_1}, p_l_finite^{m_2},*)
(* ..., p_l_finite^{m_n}) where                                                 *)
(*    m_i = max(0, ⌈(M − ord_P(η_i)) / ℓ_α⌉).                                  *)
(*                                                                              *)
(* For squarefree g, ramification ℓ = n, vanishing weight M = ℓ - 1 = n - 1   *)
(* (this is `div(dx)`):                                                         *)
(*    m_i = ⌈((n − 1) − (i − 1)) / n⌉ = ⌈(n − i) / n⌉ = 1 if i < n, 0 if i = n.*)
(*                                                                              *)
(* For squarefree g and M = 1 (this is `D_n`):                                  *)
(*    m_i = ⌈(1 − (i − 1)) / n⌉ = ⌈(2 − i) / n⌉ = 1 if i = 1, 0 otherwise.    *)
(*                                                                              *)
(* The infinity-side construction is analogous via the ψ-basis and δ_i.       *)

(* ::Section:: *)
(* Ramification data                                                            *)
(*                                                                              *)
(* `ramificationData[basis]` returns                                            *)
(*    <|                                                                         *)
(*      "finite"   -> { <|"factor"->p_j, "exponent"->e_j, "gcd"->gcd(n,e_j),    *)
(*                        "ramification"->ℓ_j, "placeCount"->gcd(n,e_j)|>, … },*)
(*      "infinity" -> <|"degree"->deg(g), "gcd"->d_∞, "ramification"->ℓ_∞,    *)
(*                       "placeCount"->d_∞|>                                    *)
(*    |>.                                                                        *)
(* Place counts are over k(x); each place has residue degree (deg(p_j) /       *)
(* placeCount) for finite factors, and 1 for infinity-place pieces above k    *)
(* (ignoring further splitting that may happen over an algebraic extension —  *)
(* such splitting is Sch §10 and out of scope here).                            *)

ClearAll[ramificationData];
ramificationData[basis_?basisDescriptorQ] := Module[
  {n, g, x, factors, mDeg, dInf, finiteData},
  n = basis["n"]; g = basis["g"]; x = basis["x"];

  factors = basis["pFactors"];
  finiteData = Map[
    Function[{pe},
      Module[{p = pe[[1]], e = pe[[2]], gcdNE},
        gcdNE = GCD[n, e];
        <|
          "factor"       -> p,
          "exponent"     -> e,
          "gcd"          -> gcdNE,
          "ramification" -> n / gcdNE,
          "placeCount"   -> gcdNE
        |>
      ]
    ],
    factors
  ];

  mDeg = Exponent[g, x];
  dInf = GCD[n, mDeg];
  <|
    "finite"   -> finiteData,
    "infinity" -> <|
      "degree"        -> mDeg,
      "gcd"           -> dInf,
      "ramification"  -> n / dInf,
      "placeCount"    -> dInf
    |>
  |>
];

(* `ramificationsByIndex[basis]` collates the data into a map                  *)
(*   ℓ ↦ <|"finiteFactors"->{p_{j_1}, …}, "infinityCount"->Integer|>.         *)
(* Used by divisorOfDx and schultzDlDivisor.                                  *)

ClearAll[ramificationsByIndex];
ramificationsByIndex[basis_?basisDescriptorQ] := Module[
  {data, byL, lInf, dInf},
  data = ramificationData[basis];
  byL = <||>;
  Scan[
    Function[{f},
      Module[{ell = f["ramification"], existing},
        existing = Lookup[byL, ell, <|"finiteFactors" -> {}, "infinityCount" -> 0|>];
        existing["finiteFactors"] = Append[existing["finiteFactors"], f["factor"]];
        byL[ell] = existing
      ]
    ],
    data["finite"]
  ];
  lInf = data["infinity"]["ramification"];
  dInf = data["infinity"]["placeCount"];
  Module[{existing = Lookup[byL, lInf, <|"finiteFactors" -> {}, "infinityCount" -> 0|>]},
    existing["infinityCount"] = existing["infinityCount"] + dInf;
    byL[lInf] = existing
  ];
  byL
];

(* ::Section:: *)
(* Helper: per-η_i vanishing exponent at a finite ramification-ℓ place           *)
(*                                                                              *)
(* `etaFiniteOrder[basis, i, e_α, ℓ]` returns ord_P(η_i) at a place P over a  *)
(* root α of multiplicity e_α with ramification ℓ = n/gcd(n,e_α).              *)
(* Used to compute the per-i vanishing-weight constraint for divisor          *)
(* construction.                                                                *)

ClearAll[etaFiniteOrder];
etaFiniteOrder[basis_?basisDescriptorQ, i_Integer, eAlpha_Integer, ell_Integer] :=
  Module[{n, gcdN, mu},
    n = basis["n"];
    gcdN = GCD[n, eAlpha];
    mu = eAlpha / gcdN;
    (i - 1) * mu - ell * Floor[(i - 1) * eAlpha / n]
  ];

(* `etaInfinityOrder[basis, i, ramification ℓ_∞]` returns ord_P(ψ_i) at the   *)
(* infinity place(s) — same number at every ∞ place because the local         *)
(* uniformizer is t with t^{ℓ_∞} ~ x^{-1} and ψ_i = x^{-δ_{i-1}}·η_{i-1} has  *)
(* ord_∞(ψ_i) = δ_{i-1}·ℓ_∞ + ord_∞(η_{i-1}).                                 *)
(* For η_{i-1} = y^{i-1}/d_{i-1}, ord_∞(η_{i-1}) = -(i-1)·m̃ + ℓ_∞·deg(d_{i-1})*)
(* with m̃ = deg(g)/d_∞.                                                        *)

ClearAll[etaInfinityOrder];
etaInfinityOrder[basis_?basisDescriptorQ, i_Integer] := Module[
  {n, x, d, m, mTilde, dInf, lInf, deltas, eta, di, ord},
  n = basis["n"]; x = basis["x"]; d = basis["d"]; m = Exponent[basis["g"], x];
  dInf = GCD[n, m]; lInf = n / dInf; mTilde = m / dInf;
  deltas = basis["deltas"];
  di = d[[i]];
  ord = -(i - 1) * mTilde + lInf * Exponent[di, x];
  deltas[[i]] * lInf + ord
];

(* ::Section:: *)
(* divisorOfDx                                                                  *)
(*                                                                              *)
(* div(dx) = Π_{P finite} P^{r(P)-1} · Π_{P ∞} P^{-r(P)-1}                      *)
(*                                                                              *)
(* For the η-basis at finite places, the i-th diagonal entry of the a-matrix   *)
(* is the polynomial whose roots' x-coordinates carry the right amount of    *)
(* vanishing for f to have ord_P ≥ ℓ_α − 1 at every finite ramification-ℓ_α    *)
(* place P. For squarefree g this collapses to the simple expression          *)
(*    diag(g, g, ..., g, 1)   (n−1 copies of g, then 1 in the n-th slot)      *)
(* derived in the comment header.                                               *)

ClearAll[divisorOfDx];
divisorOfDx[basis_?basisDescriptorQ] := Module[
  {n, g, x, mDeg, dInf, lInf, factors, aFin, aInf, i,
   ordEtaI, ordPsiI, mFin, kInf, weightFin, weightInfDx, factorPower},

  n = basis["n"]; g = basis["g"]; x = basis["x"];
  mDeg = Exponent[g, x]; dInf = GCD[n, mDeg]; lInf = n / dInf;
  factors = basis["pFactors"];

  (* Finite a-matrix: diagonal entry [i, i] = ∏_j p_j^{m_{i,j}}                *)
  (* with m_{i,j} = ⌈((ℓ_j − 1) − ord_P(η_i)) / ℓ_j⌉ when positive, 0 else.   *)
  aFin = Table[ConstantArray[0, n], {n}];
  weightFin = Function[{eAlpha, ell, i}, Module[{ord, raw},
    ord = etaFiniteOrder[basis, i, eAlpha, ell];
    raw = (ell - 1) - ord;
    Max[0, Ceiling[raw / ell]]
  ]];
  Do[
    aFin[[i, i]] = Module[{prod = 1},
      Do[
        Module[{p = factors[[k, 1]], e = factors[[k, 2]],
                gcdNE, ell, m},
          gcdNE = GCD[n, e]; ell = n / gcdNE;
          If[ell >= 2,
            m = weightFin[e, ell, i];
            If[m > 0, prod = Together[prod * p^m]]
          ]
        ],
        {k, 1, Length[factors]}
      ];
      prod
    ],
    {i, 1, n}
  ];

  (* Infinity b-matrix: diagonal entry x^{e_max(i)} where                      *)
  (*   e_max(i) = ⌊(ord_P(ψ_i) − K) / ℓ_∞⌋   with K = −ℓ_∞ − 1                *)
  (*           = ⌊(ord_P(ψ_i) + ℓ_∞ + 1) / ℓ_∞⌋.                              *)
  (* Off-diagonal entries are zero (the ideal is principal-per-component       *)
  (* in the simple-radical basis).                                              *)
  aInf = Table[ConstantArray[0, n], {n}];
  weightInfDx = Function[{i}, Module[{ord, K},
    ord = etaInfinityOrder[basis, i];
    K = -lInf - 1;
    Floor[(ord - K) / lInf]
  ]];
  Do[
    Module[{e = weightInfDx[i]},
      aInf[[i, i]] = Together[x^e]
    ],
    {i, 1, n}
  ];

  schultzDivisorMake[aFin, aInf, basis]
];

(* ::Section:: *)
(* schultzDlDivisor                                                             *)
(*                                                                              *)
(* `schultzDlDivisor[basis, ℓ]` returns the SchultzDivisor representing the     *)
(* effective divisor `D_ℓ = Σ_{r(P) = ℓ} P` (sum of all places with           *)
(* ramification index exactly ℓ, each with weight 1).                          *)
(*                                                                              *)
(* SCOPE NOTE.                                                                  *)
(*   • Finite ℓ = 1 (non-branch finite places) is an INFINITE collection of   *)
(*     places and cannot be represented as a finite ideal directly; the Sch   *)
(*     Lemma 4.6 iteration is the prescribed route for that case and is       *)
(*     deferred. For ℓ = 1 we therefore set the FINITE ideal to the trivial   *)
(*     I_n (no constraint at finite places). In reduced simple-radical form   *)
(*     no finite factor of g has ramification 1, so this trivial finite side  *)
(*     correctly reflects the absence of ℓ=1 finite branch contributions.    *)
(*   • Infinite ℓ = 1 (at most n places) is FINITE and meaningful: we emit   *)
(*     the infinity-side ideal whose support is exactly the ramification-1   *)
(*     infinity places. This is needed by S.5 (eq. 4.11 residue computation) *)
(*     for inputs like ∫ dx/√(x²+1) whose only residues live at ramification *)
(*     1 at infinity (lInf = gcd(n, deg g) / 1 = 1).                          *)
(*                                                                              *)
(* For ℓ ≥ 1, the divisor support is:                                          *)
(*   - Every ℚ-irreducible factor p_j of g with ℓ_j = ℓ (vacuous for ℓ = 1   *)
(*     in reduced form): places over its roots, weight 1.                      *)
(*   - Every infinity place: present iff ℓ_∞ = ℓ, weight 1.                    *)

ClearAll[schultzDlDivisor];
schultzDlDivisor[basis_?basisDescriptorQ, ell_Integer] /; ell >= 1 := Module[
  {n, x, factors, mDeg, dInf, lInf, includedFactors, includesInfinity,
   aFin, aInf, i, weightFin, weightInfDl},

  n = basis["n"]; x = basis["x"];
  mDeg = Exponent[basis["g"], x]; dInf = GCD[n, mDeg]; lInf = n / dInf;
  factors = basis["pFactors"];

  (* Filter to factors whose ramification matches ℓ. *)
  includedFactors = Cases[factors,
    {p_, e_} /; (n / GCD[n, e]) === ell :> {p, e}
  ];
  includesInfinity = (lInf === ell);

  (* Finite a-matrix: diagonal entry[i, i] = ∏_{factor included} p_j^{m_{i,j}} *)
  (* with m_{i,j} = ⌈(1 − ord_P(η_i)) / ℓ⌉ clamped to 0.                       *)
  weightFin = Function[{eAlpha, i}, Module[{ord, raw},
    ord = etaFiniteOrder[basis, i, eAlpha, ell];
    raw = 1 - ord;
    Max[0, Ceiling[raw / ell]]
  ]];
  aFin = Table[ConstantArray[0, n], {n}];
  Do[
    aFin[[i, i]] = Module[{prod = 1},
      Do[
        Module[{p = pe[[1]], e = pe[[2]], m},
          m = weightFin[e, i];
          If[m > 0, prod = Together[prod * p^m]]
        ],
        {pe, includedFactors}
      ];
      prod
    ],
    {i, 1, n}
  ];

  (* Infinity b-matrix: diagonal entry x^{e_max(i)} where                      *)
  (*   e_max(i) = ⌊(ord_∞(ψ_i) − 1) / ℓ_∞⌋   when ℓ_∞ = ℓ                      *)
  (*           or = 0 (identity) otherwise.                                     *)
  aInf = Table[ConstantArray[0, n], {n}];
  weightInfDl = Function[{i}, Module[{ord, e},
    ord = etaInfinityOrder[basis, i];
    e = If[includesInfinity, Floor[(ord - 1) / lInf], 0];
    Together[x^e]
  ]];
  Do[
    aInf[[i, i]] = weightInfDl[i],
    {i, 1, n}
  ];

  schultzDivisorMake[aFin, aInf, basis]
];

(* `schultzDlDivisorMap[basis]` returns a map ℓ ↦ schultzDlDivisor[basis, ℓ]   *)
(* over every ramification index ℓ ≥ 1 that appears in the ramification       *)
(* structure of the curve. ℓ = 1 entries (when present) carry the meaningful  *)
(* infinity-side data and trivial finite side; ℓ ≥ 2 entries carry both       *)
(* sides as in Sch Lemma 4.6.                                                  *)

ClearAll[schultzDlDivisorMap];
schultzDlDivisorMap[basis_?basisDescriptorQ] := Module[
  {byL, ells},
  byL = ramificationsByIndex[basis];
  ells = Sort[Keys[byL]];
  AssociationMap[Function[ell, schultzDlDivisor[basis, ell]], ells]
];

(* End of module *)
