(* ::Package:: *)

(* ::Title:: *)
(* Schultz 2015 §4.4 -- residue divisors via norm resultants                   *)

(* ::Text:: *)
(* Implements the equations                                                    *)
(*                                                                              *)
(*   (4.10)   Res_x(Norm(b'(x)·z − r·Σ a_i η_i), Norm(b·O^∞ + (D_r)^∞)) = 0    *)
(*   (4.11)   Res_{1/x}(Norm((b/x^{deg b})·z + r·Σ (a_i·x^{1+δ_i}/x^{deg b})·  *)
(*                       (η_i/x^{δ_i})), Norm((D_r)_∞)) = 0                     *)
(*                                                                              *)
(* The roots of the resulting z-polynomial are exactly the residues of         *)
(*   ω = Σ_i (a_i / b) η_i dx                                                   *)
(* at the finite (eq. 4.10) and infinite (eq. 4.11) places with ramification  *)
(* index r.                                                                     *)
(*                                                                              *)
(* Assumptions (enforced by prior phases):                                     *)
(*   • ω's Hermite-reduced representation: b is squarefree and deg(a_i) + δ_i *)
(*     < deg(b) for every i. These are Lemma 4.4's conditions, ensuring ω has *)
(*     at worst simple poles.                                                   *)
(*   • The basis descriptor carries "deltas" (§S.1).                            *)
(*                                                                              *)
(* The Norm here is Norm_{K/k(x)} for the finite side (computed as the        *)
(* determinant of the multiplication-by-element matrix on the η-basis) and    *)
(* Norm_{K/k((1/x))} at the infinity side (same formula, but with the ψ-basis *)
(* interpretation). The Res_x / Res_{1/x} are ordinary polynomial resultants. *)
(*                                                                              *)
(* Reference: Schultz 2015 §4.4, pp. 14-15.                                    *)

(* ::Section:: *)
(* Norm on the η-basis                                                          *)
(*                                                                              *)
(* Norm_{K/k(x)}(f) for an AF element f is the determinant of its               *)
(* multiplication matrix in the η-basis. `afNorm` in src/Arithmetic.m          *)
(* already implements this; we re-export it here under a Schultz-flavoured     *)
(* name for clarity at call sites.                                              *)

ClearAll[schultzNormAF];
schultzNormAF[fAF_?afElementQ, basis_?basisDescriptorQ] := afNorm[fAF, basis];

(* Norm of a Schultz divisor: det of its aFin (finite) or aInf (infinity)     *)
(* matrix. Returns {finiteNorm, infinityNorm}.                                  *)

ClearAll[schultzDivisorNorm];
schultzDivisorNorm[d_?schultzDivisorQ] := {
  Together[Det[d["aFin"]]],
  Together[Det[d["aInf"]]]
};

(* ::Section:: *)
(* Extended AF elements with a free variable z                                  *)
(*                                                                              *)
(* Eq. (4.10)'s first Norm is of an element in K[z]: polynomial in the          *)
(* indeterminate z with coefficients in K. Our AF data structure holds         *)
(* rational-in-x coefficients; we extend to rational-in-(x, z) by letting      *)
(* those coefficients carry z as an additional symbol. The multiplication     *)
(* matrix is then polynomial in z, and its determinant (the Norm) is a         *)
(* polynomial in z with k[x] / k[[1/x]] coefficients.                           *)
(*                                                                              *)
(* `afOfLinearInZ[zeroTerm, linearTerm, basis]` builds the AF element          *)
(*     A(z) = zeroTerm_AF + z · linearTerm_AF                                   *)
(* where both inputs are AF elements and z is an external symbol. The result   *)
(* is an AF element whose Coeffs are polynomials in z with k(x) coefficients. *)

ClearAll[afOfLinearInZ];
afOfLinearInZ[zeroAF_?afElementQ, linearAF_?afElementQ, z_Symbol,
              basis_?basisDescriptorQ] := afMake[
  MapThread[Together[#1 + z * #2] &,
    {zeroAF["Coeffs"], linearAF["Coeffs"]}],
  basis
];

(* ::Section:: *)
(* Finite residue polynomial (eq. 4.10)                                         *)
(*                                                                              *)
(* Inputs:                                                                      *)
(*   Acoeffs — list of a_i ∈ k[x] (squarefree b already factored out).         *)
(*   b       — squarefree polynomial in k[x].                                   *)
(*   r       — ramification index (integer ≥ 1).                                *)
(*   dLDiv   — Schultz divisor D_r (only its aFin matters here).                *)
(*   basis   — basis descriptor.                                                *)
(*   z       — free symbol for the residue variable.                            *)
(*                                                                              *)
(* Output: a polynomial in z whose roots are the residue values at finite      *)
(* ramification-r places. Returns 0 when no such places carry residues.         *)
(*                                                                              *)
(* Construction:                                                                *)
(*   1. Build AF element A_fin(z) = b'(x)·z − r·Σ a_i η_i.                      *)
(*   2. N1(x, z) = afNorm[A_fin(z)] ∈ k(x)[z].                                  *)
(*   3. N2(x) = det(HNF of row-stack(b·I_n, aFin_{D_r})) ∈ k[x].                *)
(*   4. Return Resultant[Numerator[N1(x, z)], N2(x), x], then strip             *)
(*      superfluous x-dependence (the result should be purely in z).            *)

ClearAll[schultzResidueFinitePoly];
schultzResidueFinitePoly[
  Acoeffs_List, b_, r_Integer, dLDiv_?schultzDivisorQ,
  basis_?basisDescriptorQ, z_Symbol
] := Module[
  {n, x, bPrime, zeroAF, linearAF, Afin, N1, N1Num,
   idealSum, idealSumHNF, N2, res},
  n = basis["n"]; x = basis["x"];
  bPrime = D[b, x];

  (* Step 1: build Afin(z) = b'(x)·z − r·Σ a_i η_i as an AF element.           *)
  (* η_1 = 1 carries the constant z-linear part; the other η_i carry only the *)
  (* r·a_i scale factor. Negative of the a-sum per eq. 4.10.                   *)
  linearAF = afMake[
    Join[{bPrime}, ConstantArray[0, n - 1]],
    basis
  ];
  zeroAF = afMake[
    Map[Together[-r * #] &, Acoeffs],
    basis
  ];
  Afin = afMake[
    Table[
      Together[zeroAF["Coeffs"][[i]] + z * linearAF["Coeffs"][[i]]],
      {i, 1, n}
    ],
    basis
  ];

  (* Step 2: N1(x, z) = Norm(Afin). Uses the multiplication matrix on η. *)
  N1 = schultzNormAF[Afin, basis];
  N1Num = Numerator[Together[N1]];

  (* Step 3: Norm of the ideal b·O^∞ + (D_r)^∞. Row-stack b·I_n with aFin     *)
  (* (the D_r finite matrix), take HNF over k[x], then det.                   *)
  idealSum = Join[b * IdentityMatrix[n], dLDiv["aFin"]];
  idealSumHNF = schultzHNFFinite[idealSum, x];
  N2 = Together[Det[idealSumHNF]];

  If[zeroQ[N2], Return[0]];

  (* Step 4: Res_x(N1, N2). N1 is polynomial in x when N2 is — the             *)
  (* resultant is a polynomial in z.                                            *)
  res = Resultant[N1Num, Numerator[Together[N2]], x];
  Together[res]
];

(* ::Section:: *)
(* Infinity residue polynomial (eq. 4.11)                                       *)
(*                                                                              *)
(* Output: a polynomial in z whose roots are the residue values at infinite    *)
(* ramification-r places.                                                       *)
(*                                                                              *)
(* Construction (expanded form of eq. 4.11):                                   *)
(*   Let P(x, z) = [b·z + r·x·Σ a_i η_i] / x^{deg b}.                          *)
(*   Compute Norm(P) ∈ k(x)[z]. Factor out x^{deg b} from numerator; what      *)
(*   remains is a Laurent polynomial in 1/x with z-polynomial coefficients.   *)
(*   The Res_{1/x} with Norm((D_r)_∞) then extracts the appropriate            *)
(*   coefficient of (1/x)^? (where ? = ord_{1/x} of Norm((D_r)_∞)).             *)
(*                                                                              *)
(* The Norm((D_r)_∞) = det(aInf) is always a power of 1/x (monomial diagonal  *)
(* in HNF). The Res_{1/x} is then the coefficient of (1/x)^0 in P (when        *)
(* Norm((D_r)_∞) = 1) or of (1/x)^{ord} (when > 0). Because SeriesTake at      *)
(* x = ∞ gives us the constant term directly, we implement via Limit or       *)
(* by constructive extraction.                                                  *)
(*                                                                              *)
(* Because the Norm at infinity is always 1/x^{power}, the Res_{1/x} reduces  *)
(* to extracting the Laurent-series coefficient of (1/x)^(that power). Below  *)
(* we compute this via Series[…, {x, Infinity, power}].                        *)

ClearAll[schultzResidueInfinityPoly];
schultzResidueInfinityPoly[
  Acoeffs_List, b_, r_Integer, dLDiv_?schultzDivisorQ,
  basis_?basisDescriptorQ, z_Symbol
] := Module[
  {n, x, degB, sumAF, exprAF, N1, N2infinity, invXPower, extracted, sRes, c},
  n = basis["n"]; x = basis["x"];
  degB = Exponent[b, x];

  (* Step 1: build sumAF = Σ a_i η_i ∈ AF. *)
  sumAF = afMake[Map[Together, Acoeffs], basis];

  (* Step 2: form exprAF = (b·z + r·x·sumAF)/x^{deg b} as an AF element.       *)
  (* In AF coordinates: coefficient of η_i is                                    *)
  (*    i = 1: (b·z + r·x·a_1)/x^{deg b},                                       *)
  (*    i ≥ 2: r·x·a_i/x^{deg b}.                                                *)
  exprAF = afMake[
    Table[
      If[i === 1,
        Together[(b * z + r * x * Acoeffs[[i]]) / x^degB],
        Together[r * x * Acoeffs[[i]] / x^degB]
      ],
      {i, 1, n}
    ],
    basis
  ];

  (* Step 3: Norm of exprAF. *)
  N1 = Together[schultzNormAF[exprAF, basis]];

  (* Step 4: Per Sch p.15, "if this power of 1/x is positive, the resultant  *)
  (* should be evaluated by taking the CONSTANT TERM of the first norm".     *)
  (* I.e. always extract SeriesCoefficient[N1, {x, Infinity, 0}] — the       *)
  (* (1/x)^0 = 1 coefficient. The order of Norm((D_r)_∞) only governs        *)
  (* whether the formula applies at all (must be positive).                  *)
  N2infinity = Together[Det[dLDiv["aInf"]]];
  invXPower = valInfinity[N2infinity, x];
  If[invXPower <= 0,
    (* Ramification-r does not contribute at infinity for this divisor.        *)
    Return[0]
  ];

  sRes = SeriesCoefficient[N1, {x, Infinity, 0}];
  Together[sRes]
];

(* ::Section:: *)
(* Residue extraction                                                           *)
(*                                                                              *)
(* Given the residue polynomial (in z), factor over ℚ (or ℚ(params)) and      *)
(* return the distinct residue values. Strip Z^k factors since branch-place   *)
(* zero residues contribute factors of z to the resultant (simple radicals:   *)
(* branch places have residue 0 per Trager Ch 5 §4).                           *)

ClearAll[residueValuesFromPoly];
residueValuesFromPoly[poly_, z_Symbol] := Module[{p, stripped, factors, roots},
  p = Together[poly];
  If[zeroQ[p], Return[{}]];
  (* Strip the z^k factor — zero residues at branch places. *)
  stripped = p / z^Exponent[p, z, Min];
  factors = FactorList[stripped];
  roots = Flatten[
    Map[
      Function[{fe},
        Module[{f = fe[[1]], m = fe[[2]], vars, deg},
          If[FreeQ[f, z], {},
            vars = {z};
            deg = Exponent[f, z];
            Which[
              deg === 1,
                {Together[-Coefficient[f, z, 0] / Coefficient[f, z, 1]]},
              True,
                Table[Root[
                  Evaluate[
                    Sum[Coefficient[f, z, i] * Slot[1]^i, {i, 0, deg}]
                  ] &,
                  k
                ], {k, deg}]
            ]
          ]
        ]
      ],
      factors
    ]
  ];
  DeleteDuplicates[roots]
];

(* ::Section:: *)
(* Top-level driver                                                             *)
(*                                                                              *)
(* `schultzResidues[integrandAF, b, basis, z]` returns an association           *)
(*   <|                                                                          *)
(*     "finite"   -> <| r -> {residue values at ramification-r finite places},  *)
(*                      ... |>,                                                  *)
(*     "infinity" -> <| r -> {residue values at ramification-r infinity places},*)
(*                      ... |>                                                    *)
(*   |>                                                                           *)
(* iterated over every ramification index present in the D_ℓ map.               *)

ClearAll[schultzResidues];
schultzResidues[Acoeffs_List, b_, basis_?basisDescriptorQ, z_Symbol] :=
  Module[{dmap, finiteResidues, infinityResidues, ells,
          polyFin, polyInf, dForR},
    dmap = schultzDlDivisorMap[basis];
    ells = Keys[dmap];
    (* Sch §4.4 page 14: for the eq. 4.10 finite residue formula, ramification *)
    (* index r = 1 needs the b-aware (D_1[b])^∞ instead of the curve-only D_1   *)
    (* (which would be infinite-support and meaningless). For r ≥ 2, D_r is   *)
    (* curve-invariant and finite, so we use dmap[r] directly.                  *)
    dForR = Function[r,
      If[r === 1, schultzD1ForB[b, basis], dmap[r]]
    ];
    finiteResidues = AssociationMap[
      Function[r,
        polyFin = schultzResidueFinitePoly[Acoeffs, b, r, dForR[r], basis, z];
        residueValuesFromPoly[polyFin, z]
      ],
      ells
    ];
    infinityResidues = AssociationMap[
      Function[r,
        polyInf = schultzResidueInfinityPoly[Acoeffs, b, r, dmap[r], basis, z];
        residueValuesFromPoly[polyInf, z]
      ],
      ells
    ];
    <|"finite" -> finiteResidues, "infinity" -> infinityResidues|>
  ];

(* End of module *)
