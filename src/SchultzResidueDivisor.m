(* ::Package:: *)

(* ::Title:: *)
(* Schultz §4.4 -- residue divisor builder                                     *)

(* ::Text:: *)
(* See Sch §4.4 (pp. 14-15). For a Schultz-Hermite-reduced differential       *)
(*    ω = Σ_i (a_i / b) η_i dx                                                  *)
(* (b squarefree, deg(a_i) + δ_i < deg(b)), each residue value z_0 of ω at a *)
(* place of ramification ℓ corresponds to a divisor δ_ℓ(z_0) of places where *)
(* ω has that residue, given by                                                *)
(*                                                                              *)
(*    δ_ℓ(z)^∞ = (b'(x)·z − ℓ·Σ_i a_i(x) η_i) · O^∞ + b(x) · O^∞ + (D_ℓ)^∞,    *)
(*    δ_ℓ(z)_∞ = ((b(x)/x^{deg b})·z + ℓ·Σ_i a_i(x) x^{1+δ_i}/x^{deg b}        *)
(*                 · η_i/x^{δ_i}) · O_∞ + (D_ℓ)_∞                              *)
(*                                                                              *)
(* (the formulas immediately above eq. 4.10 / 4.11). Each is an *ideal sum*    *)
(* (placewise minimum of orders, Sch §4.1 table on p. 8) of constituent        *)
(* fractional ideals. Stacking the constituent matrices and HNF'ing produces  *)
(* a canonical n × n basis for δ_ℓ(z_0).                                        *)
(*                                                                              *)
(* For finite residues z_0, only the finite ideal sum contributes a non-        *)
(* trivial divisor; the infinity-side ideal collapses to (D_ℓ)_∞ when z_0 is  *)
(* not also a residue at infinity. Conversely for infinity residues. The      *)
(* formulas naturally handle both cases without branching.                     *)
(*                                                                              *)
(* The total residue divisor at residue value z_0 is then                       *)
(*    δ(z_0) = ∏_ℓ δ_ℓ(z_0)                                                     *)
(* (ideal product over ramification indices, computed via                      *)
(* schultzDivisorMultiply); but for the simple-radical scope, residues at      *)
(* ramification ≥ 2 vanish (branch places contribute no residue, Trager Ch 5  *)
(* §4), so most residues come from ramification ℓ = 1 only and the ℓ-product *)
(* collapses to a single δ_1(z_0).                                              *)

(* ::Section:: *)
(* Helper: build the "principal ideal F · O^∞" matrix in η-coords (rows).      *)
(*                                                                              *)
(* For F ∈ K an AF element, F · O^∞ has k[x]-basis {F·η_i : i = 1..n}.         *)
(* Each row is the η-coordinates of F·η_i.                                      *)

ClearAll[principalFinIdealMatrix];
principalFinIdealMatrix[fAF_?afElementQ, basis_?basisDescriptorQ, y_Symbol] :=
  Module[{Mf},
    Mf = multiplicationMatrix[fAF, basis, y];
    Map[schultzCanon, Transpose[Mf], {2}]
  ];

(* Helper: build the "principal ideal F · O_∞" matrix in (η · x^{-δ})-coords. *)
(*                                                                              *)
(* Row i, col j of the result = (F·(η·x^{-δ})_i)_{(η·x^{-δ})_j}                *)
(*                            = Mf[j, i] · x^{δ_j − δ_i}.                       *)

ClearAll[principalInfIdealMatrix];
principalInfIdealMatrix[fAF_?afElementQ, basis_?basisDescriptorQ, y_Symbol] :=
  Module[{n, deltas, x, Mf},
    n = basis["n"];
    deltas = basis["deltas"];
    x = basis["x"];
    Mf = multiplicationMatrix[fAF, basis, y];
    Table[
      schultzCanon[Mf[[j, i]] * x^(deltas[[j]] - deltas[[i]])],
      {i, n}, {j, n}
    ]
  ];

(* ::Section:: *)
(* b-aware D_1 ideal (Sch §4.4 page 14, special-case for r = 1).               *)
(*                                                                              *)
(* Per Schultz, eq. 4.10's (D_1)^∞ for residue extraction is NOT the curve-     *)
(* invariant D_1 (which would be infinite-support and undefined as an ideal),  *)
(* but the b-restricted version                                                 *)
(*                                                                              *)
(*   (D_1)^∞ = b(x) O^∞ / (b(x) O^∞ + (D_2²)^∞ (D_3³)^∞ ⋯)                     *)
(*                                                                              *)
(* This is the product of places over roots of b with ramification index 1.   *)
(*                                                                              *)
(* For the simple-radical case y^n = g with squarefree b, this simplifies to:  *)
(* the product of ℚ-irreducible factors p_j of b for which the ramification    *)
(* of places over p_j's roots is exactly 1 — i.e. p_j with gcd(p_j, g_{ram>1}) *)
(* trivial in the relevant sense.                                                *)
(*                                                                              *)
(* For y^n = g with g = ∏ p_k^{e_k}, ramification at place over root α of      *)
(* p_j(x) is n / gcd(n, ord_α(g)). Since g = ∏ p_k^{e_k}, ord_α(g) = e_k when *)
(* α is a root of p_k (= 0 otherwise). So ram = n / gcd(n, e_k) for α a root  *)
(* of p_k, or n / gcd(n, 0) = 1 for α not a root of any p_k.                    *)
(*                                                                              *)
(* Returns the Schultz divisor (D_1[b])^∞ that should be used in eq. 4.10's       *)
(* finite-residue formula.                                                       *)

ClearAll[schultzD1ForB];
schultzD1ForB[b_, basis_?basisDescriptorQ] := Module[
  {x, n, gFactors, bFactors, ramOnePoly, p, e, ramOfP, gMatch,
   curveDl, finiteFromB},
  x = basis["x"];
  n = basis["n"];

  gFactors = basis["pFactors"];  (* {{p_k, e_k}, ...} from g = ∏ p_k^{e_k}.   *)
  bFactors = Rest @ FactorList[b];  (* {{p, mult}, ...} from b's factorization. *)

  ramOnePoly = 1;
  Do[
    Module[{pFactor = bf[[1]], pMult = bf[[2]]},
      If[!FreeQ[pFactor, x] && PolynomialQ[pFactor, x] && Exponent[pFactor, x] >= 1,
        (* Look up p in g's factor list to find its multiplicity in g.         *)
        gMatch = SelectFirst[gFactors,
          PolynomialGCD[pFactor, #[[1]]] === #[[1]] &,
          {Null, 0}
        ];
        e = gMatch[[2]];   (* exponent in g, or 0 if pFactor not a factor of g *)
        ramOfP = n / GCD[n, e];
        If[ramOfP === 1,
          (* pFactor's places have ramification 1; include in the b-aware D_1. *)
          ramOnePoly = Together[ramOnePoly * pFactor^pMult]
        ]
      ]
    ],
    {bf, bFactors}
  ];

  (* Build the Schultz divisor:                                                 *)
  (*   aFin: b-aware (places of ramification 1 over roots of b).               *)
  (*   aInf: curve-only D_1's aInf (independent of b — captures the            *)
  (*         ramification-1 places at infinity per Sch §S.4).                   *)
  finiteFromB = schultzDivisorFromFinitePoly[ramOnePoly, basis];
  curveDl = schultzDlDivisorMap[basis];
  If[KeyExistsQ[curveDl, 1],
    <|
      "Type"  -> "SchultzDivisor",
      "aFin"  -> finiteFromB["aFin"],
      "aInf"  -> curveDl[1]["aInf"],
      "basis" -> basis
    |>,
    finiteFromB
  ]
];

(* ::Section:: *)
(* schultzResidueDivisor — Schultz divisor of places where ω has residue z_0.  *)
(*                                                                              *)
(* Inputs:                                                                      *)
(*   Acoeffs       - {a_1, …, a_n}, the η-coefficients of ω after              *)
(*                  Schultz-Hermite reduction (b factored out).                *)
(*   b             - squarefree polynomial in basis["x"].                       *)
(*   basis         - basis descriptor with "deltas" populated.                  *)
(*   y             - generator symbol (for AF arithmetic).                      *)
(*   z0            - the specific residue value to build the divisor for. May *)
(*                  live in K = ℚ(α) for some algebraic α arising from         *)
(*                  Phase-4 residues; the AF arithmetic handles α as a          *)
(*                  symbolic constant.                                           *)
(*   ell           - ramification index (≥ 1).                                  *)
(*                                                                              *)
(* Output: a Schultz divisor representing δ_ell(z_0).                           *)

ClearAll[schultzResidueDivisor];
schultzResidueDivisor[
  Acoeffs_List, b_, basis_?basisDescriptorQ, y_Symbol,
  z0_, ell_Integer
] := Module[
  {n, x, deltas, bPrime, degB, FAF, GAF, FFinMat, GInfMat,
   bPolyMat, dEll, finStack, infStack, aFinNew, aInfNew},

  n = basis["n"]; x = basis["x"]; deltas = basis["deltas"];
  bPrime = D[b, x];
  degB = Exponent[b, x];

  (* F = b'(x) · z_0 − ℓ · Σ_i a_i η_i.                                          *)
  (* η-coords:  F_1 = b' · z_0 − ℓ · a_1,  F_i = − ℓ · a_i  for i ≥ 2.          *)
  (* `schultzCanon` (rather than `Together`) is essential when z_0 is an        *)
  (* algebraic-number residue (e.g. ζ_3 cube roots of unity from cubic-radical *)
  (* integrands): without RootReduce-canonicalization here, the Mf entries      *)
  (* downstream carry algebraic-number bloat that secretly evaluates to 0/0   *)
  (* on division, derailing the Schultz HNF pivot loop.                          *)
  FAF = afMake[
    Prepend[
      Map[schultzCanon[-ell * #] &, Rest[Acoeffs]],
      schultzCanon[bPrime * z0 - ell * Acoeffs[[1]]]
    ],
    basis
  ];

  (* G = (b/x^{deg b}) · z_0 + ℓ · Σ_i (a_i x^{1+δ_i}/x^{deg b}) (η_i / x^{δ_i})*)
  (*   = (b z_0)/x^{deg b}  +  ℓ · x^{1−deg b} · Σ_i a_i η_i.                    *)
  (* η-coords:  G_1 = (b z_0 + ℓ x a_1)/x^{deg b},                                *)
  (*            G_j = (ℓ x a_j)/x^{deg b}  for j ≥ 2.                            *)
  GAF = afMake[
    Prepend[
      Map[schultzCanon[(ell * x * #) / x^degB] &, Rest[Acoeffs]],
      schultzCanon[(b * z0 + ell * x * Acoeffs[[1]]) / x^degB]
    ],
    basis
  ];

  FFinMat = principalFinIdealMatrix[FAF, basis, y];
  GInfMat = principalInfIdealMatrix[GAF, basis, y];

  bPolyMat = b * IdentityMatrix[n];
  (* For ell = 1, eq. 4.10 needs the b-aware (D_1[b])^∞ instead of the curve-     *)
  (* only D_1 (which is undefined for ell = 1 as it would have infinite         *)
  (* support; cf. Sch §4.4 page 14). For ell ≥ 2, D_ell is curve-invariant      *)
  (* and finite-support, so we use schultzDlDivisorMap directly.                 *)
  dEll = If[ell === 1,
    schultzD1ForB[b, basis],
    schultzDlDivisorMap[basis][ell]
  ];

  (* δ_ell(z_0)^∞ = (F)·O^∞ + (b)·O^∞ + (D_ell)^∞.                              *)
  finStack = Join[FFinMat, bPolyMat, dEll["aFin"]];
  aFinNew = schultzHNFFinite[finStack, x];

  (* δ_ell(z_0)_∞ = (G)·O_∞ + (D_ell)_∞.                                         *)
  infStack = Join[GInfMat, dEll["aInf"]];
  aInfNew = schultzHNFInfinity[infStack, x];
  aInfNew = If[Length[aInfNew] > n, Take[aInfNew, n], aInfNew];

  <|
    "Type"  -> "SchultzDivisor",
    "aFin"  -> aFinNew,
    "aInf"  -> aInfNew,
    "basis" -> basis
  |>
];

(* ::Section:: *)
(* schultzCombinedResidueDivisor — total divisor δ(z_0) summed over ℓ.         *)
(*                                                                              *)
(* For a residue value z_0, multiply the per-ramification δ_ell(z_0) divisors *)
(* together (ideal product = divisor sum). For simple radicals, residues at   *)
(* ramification ≥ 2 vanish, so the typical case has just ℓ = 1.                *)
(*                                                                              *)
(* Inputs:                                                                      *)
(*   Acoeffs, b, basis, y - same as schultzResidueDivisor.                     *)
(*   z0                   - residue value.                                     *)
(*   ramificationList    - list of ramification indices ℓ for which z_0       *)
(*                          appears as a residue (typically {1} for simple     *)
(*                          radicals).                                         *)

ClearAll[schultzCombinedResidueDivisor];
schultzCombinedResidueDivisor[
  Acoeffs_List, b_, basis_?basisDescriptorQ, y_Symbol,
  z0_, ramificationList_List
] := Module[{divisors, result},
  divisors = Map[
    schultzResidueDivisor[Acoeffs, b, basis, y, z0, #] &,
    ramificationList
  ];
  Which[
    divisors === {}, schultzDivisorTrivial[basis],
    Length[divisors] === 1, First[divisors],
    True,
      Fold[schultzDivisorMultiply, First[divisors], Rest[divisors]]
  ]
];

(* End of module *)
