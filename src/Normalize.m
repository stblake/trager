(* ::Package:: *)

(* ::Title:: *)
(* Normalization helpers for the Phase-5 principal-generator search *)

(* ::Text:: *)
(* Implements the three building blocks for "normal at infinity"           *)
(* reduction (Trager 1984 Ch 2 §3 "Normalize at infinity" and Ch 6 §1     *)
(* "Principal Divisors"):                                                   *)
(*                                                                           *)
(*   1. hermiteNormalFormOverKz  — genuine polynomial Hermite Normal Form *)
(*      on a matrix of K[z]-polynomial entries.                            *)
(*   2. infOrderRational, infValueRational — order/leading-value at z=∞   *)
(*      of a rational function in z.                                        *)
(*   3. normalizeAtInfinity — iterative column combination that kills      *)
(*      linear dependencies of leading-at-infinity terms over Q.           *)
(*                                                                           *)
(* The legacy helpers polyOrderAtZero, zAdicOrderAtZero, rationalDegInZ,   *)
(* noPoleAtInfinityRowQ, and polynomialHNFOverKz are kept for the existing *)
(* unit tests — they remain mathematically correct, just insufficient on   *)
(* their own for principal-generator construction.                          *)

(* ::Section:: *)
(* Order at zero (retained for unit tests)                                  *)

ClearAll[polyOrderAtZero];
polyOrderAtZero[p_, z_] := Module[{coeffs, k, len},
  If[zeroQ[p], Return[Infinity]];
  coeffs = CoefficientList[Expand[p], z];
  len = Length[coeffs];
  k = 1;
  While[k <= len && zeroQ[coeffs[[k]]], k++];
  If[k > len, Infinity, k - 1]
];

ClearAll[zAdicOrderAtZero];
zAdicOrderAtZero[expr_, z_Symbol] := Module[{together, num, den},
  If[zeroQ[expr], Return[Infinity]];
  together = Together[expr];
  num = Numerator[together];
  den = Denominator[together];
  polyOrderAtZero[num, z] - polyOrderAtZero[den, z]
];

(* ::Section:: *)
(* Degree and leading coefficient of a rational function in z              *)
(*                                                                           *)
(* rationalDegInZ[p/q, z] = deg(p) − deg(q). Positive = pole at z=∞,       *)
(* negative = zero at z=∞.                                                  *)

ClearAll[rationalDegInZ];
rationalDegInZ[expr_, z_Symbol] := Module[{together, num, den},
  If[zeroQ[expr], Return[-Infinity]];
  together = Together[expr];
  num = Numerator[together];
  den = Denominator[together];
  Exponent[Expand[num], z] - Exponent[Expand[den], z]
];

(* ::Section:: *)
(* infOrderRational / infValueRational                                      *)
(*                                                                           *)
(* For a rational function p(z)/q(z), the order at infinity is             *)
(*   infOrder = deg(q) − deg(p)    (positive → zero at ∞, negative → pole) *)
(* The "infinity value" is the leading-coefficient ratio:                  *)
(*   if infOrder > 0:  infValue = 0                                        *)
(*   if infOrder == 0: infValue = lc(p)/lc(q)                              *)
(*   if infOrder < 0:  infValue is undefined (caller must avoid this case).*)
(*                                                                           *)
(* For normalizeAtInfinity we compute infValue on scaled entries where the *)
(* order is guaranteed to be exactly 0.                                     *)

ClearAll[infOrderRational];
infOrderRational[expr_, z_Symbol] := Module[{t, num, den},
  If[zeroQ[expr], Return[Infinity]];
  t = Together[expr];
  num = Numerator[t];
  den = Denominator[t];
  Exponent[Expand[den], z] - Exponent[Expand[num], z]
];

ClearAll[infValueRational];
infValueRational[expr_, z_Symbol] := Module[{t, num, den, degN, degD},
  If[zeroQ[expr], Return[0]];
  t = Together[expr];
  num = Expand[Numerator[t]];
  den = Expand[Denominator[t]];
  degN = Exponent[num, z];
  degD = Exponent[den, z];
  Which[
    degD > degN, 0,   (* strictly zero at infinity *)
    degD == degN,
      Cancel[Together[Coefficient[num, z, degN] / Coefficient[den, z, degD]]],
    True,
      (* pole at infinity: return leading coefficient with an x-scale. *)
      (* Only used when the caller has already normalized, so treat as *)
      (* a dominant Laurent leading coefficient.                        *)
      Cancel[Together[Coefficient[num, z, degN] / Coefficient[den, z, degD]]]
  ]
];

(* ::Section:: *)
(* AF-aware pole-free-at-infinity test                                      *)
(*                                                                           *)
(* For an AF element Σ c_j(z) w_j on a simple radical y^n = g(z) with      *)
(* basis w_j = y^j / d_j(z), the order at infinity of c_j · w_j scaled by  *)
(* n is                                                                     *)
(*                                                                           *)
(*   n · ord_∞(c_j w_j)  =  −n · rationalDegInZ(c_j)                        *)
(*                        + n · deg(d_j)                                   *)
(*                        − j · deg(g)                                     *)
(*                                                                           *)
(* The AF element is integral at infinity iff this is ≥ 0 for every j with *)
(* c_j ≠ 0.                                                                 *)

ClearAll[scaledInfOrder];
scaledInfOrder[c_, j_Integer, basis_?basisDescriptorQ] := Module[
  {n, gDeg, d, dj},
  If[zeroQ[c], Return[Infinity]];
  n    = basis["n"];
  gDeg = Exponent[basis["g"], basis["x"]];
  d    = basis["d"];
  dj   = d[[j + 1]];
  -n * rationalDegInZ[c, basis["x"]]
    + n * Exponent[dj, basis["x"]]
    - j * gDeg
];

ClearAll[noPoleAtInfinityRowQ];
noPoleAtInfinityRowQ[row_List, basis_?basisDescriptorQ] :=
  AllTrue[
    Range[0, basis["n"] - 1],
    scaledInfOrder[row[[# + 1]], #, basis] >= 0 &
  ];

noPoleAtInfinityQ[af_?afElementQ, basis_?basisDescriptorQ] :=
  noPoleAtInfinityRowQ[af["Coeffs"], basis];

(* Regular-at-infinity predicate for a differential FORM f · dx, as opposed *)
(* to the function predicate above. Phase 4/5 residue analysis only sees   *)
(* finite-place poles — a form with a pole at an infinity place needs the  *)
(* Phase 2 Möbius shift first, else RT misses residues there.              *)
(*                                                                           *)
(* On the curve y^n = g(x), ord_P(dx) = -(e_∞ + 1) at each infinity place, *)
(* with e_∞ = n / gcd(n, deg g). A form c_j · w_j · dx is regular iff      *)
(*   ord_P(c_j · w_j) ≥ e_∞ + 1                                            *)
(* at every infinity place. Multiplying by d_gcd = gcd(n, deg g) (which    *)
(* matches the denominator in the formula for scaledInfOrder) gives the    *)
(* integer inequality                                                       *)
(*   scaledInfOrder[c_j, j, basis] ≥ n + d_gcd                             *)
(* applied per basis component. The form is regular at infinity iff this   *)
(* holds for every j with c_j ≠ 0.                                         *)

ClearAll[afFormRegularAtInfinity];
afFormRegularAtInfinity[af_?afElementQ, basis_?basisDescriptorQ] := Module[
  {n, gDeg, dgcd, threshold},
  n       = basis["n"];
  gDeg    = Exponent[basis["g"], basis["x"]];
  dgcd    = GCD[n, gDeg];
  threshold = n + dgcd;
  AllTrue[
    Range[0, n - 1],
    scaledInfOrder[af["Coeffs"][[# + 1]], #, basis] >= threshold &
  ]
];

(* ::Section:: *)
(* hermiteNormalFormOverKz — genuine polynomial K[z]-HNF                    *)
(*                                                                           *)
(* Input:  m × n matrix M with entries in K[z].                             *)
(* Output: row-echelon form in K[z] whose nonzero rows form a K[z]-basis   *)
(*         of the row-module of the input.                                  *)
(*                                                                           *)
(* Algorithm: column-by-column, use polynomial extended GCD to reduce all  *)
(* entries below the pivot to zero. The pivot row is replaced by the       *)
(* Bezout-combination (u · row_pivot + v · row_i) and the eliminated row   *)
(* becomes the "complementary" combination. Above the pivot we reduce mod  *)
(* the pivot using PolynomialQuotient.                                      *)
(*                                                                           *)
(* On exit the matrix rows span the same K[z]-module as the input, and    *)
(* rank(M) nonzero rows appear first.                                       *)

ClearAll[polynomialExtendedGCD];
polynomialExtendedGCD[p_, q_, z_Symbol] := Module[{r},
  r = PolynomialExtendedGCD[p, q, z];
  (* Mathematica returns {g, {u, v}} with u p + v q = g. *)
  {r[[1]], r[[2, 1]], r[[2, 2]]}
];

(* ::Section:: *)
(* Extended Euclidean over an algebraic extension K[x] = ℚ(ext)[x]           *)
(*                                                                           *)
(* Mathematica's built-in PolynomialExtendedGCD has no Extension option and *)
(* treats generators like ∛2 or a primitive cube root of unity as formal    *)
(* symbolic parameters, which yields wrong Bezout cofactors whenever the    *)
(* true GCD drops rank in the extension. This matters for Trager Phase 5   *)
(* whenever the Phase-4 residues lie in a nontrivial ℚ(α): for example      *)
(* integrating 1/((x³-1)y) with y³ = x³+2 requires ω = exp(2πi/3) to split *)
(* x³-1 = (x-1)(x-ω)(x-ω²).                                                *)
(*                                                                           *)
(* The construction is the textbook half-Euclidean loop, coefficient-wise   *)
(* via our own polyDivideExt rather than PolynomialQuotient/Remainder,     *)
(* because those built-ins do NOT canonicalize Root/AlgebraicNumber         *)
(* coefficients, leading to expression blow-up within 3-4 steps. At each   *)
(* step we collect coefficients and apply reduceExtCoeff to keep them in a *)
(* canonical form in ℚ(ext).                                                *)

(* reduceExtCoeff: canonicalize an element of ℚ(ext).                       *)
(*                                                                           *)
(* - ext = {}  : use Together + Cancel (pure ℚ arithmetic).                *)
(* - ext != {} : use RootReduce, which performs minimal-polynomial         *)
(*               reduction over ℚ for Root[] / AlgebraicNumber[] / nested   *)
(*               radical expressions. Slightly slower but robust.           *)

ClearAll[reduceExtCoeff];
reduceExtCoeff[c_, ext_List] := Which[
  zeroQ[c], 0,
  ext =!= {}, RootReduce[Together[c]],
  True, Cancel[Together[c]]
];

(* Helpers: degree and leading coefficient of a polynomial in x.            *)
(* Expand + Coefficient is the safest way to extract these when             *)
(* coefficients are algebraic-number expressions, since PolynomialQ may    *)
(* return False on well-formed K[x] polynomials with Root[] coefficients.  *)

ClearAll[degIn, leadingCoeffIn];
degIn[p_, x_Symbol] :=
  If[zeroQ[p], -Infinity, Exponent[Expand[p], x]];

leadingCoeffIn[p_, x_Symbol] := Module[{pe = Expand[p]},
  Coefficient[pe, x, Exponent[pe, x]]
];

(* collectCoeffs: canonicalize every coefficient of a polynomial in x under *)
(* the reduceExtCoeff rule, returning the polynomial in its expanded form. *)

ClearAll[collectCoeffs];
collectCoeffs[p_, x_Symbol, ext_List] :=
  Collect[Expand[p], x, reduceExtCoeff[#, ext] &];

(* polyDivideExt[a, b, x, ext] — polynomial long division in K[x].         *)
(*                                                                           *)
(* Returns {q, r} with  a = q · b + r,  deg_x(r) < deg_x(b), coefficients  *)
(* in K = ℚ(ext). Throws DivisionByZero on b = 0.                          *)

ClearAll[polyDivideExt];
polyDivideExt[a_, b_, x_Symbol, ext_List] := Module[
  {A, B, dB, lcB, q, dA, lcA, term},
  If[zeroQ[b],
    Return[tragerFailure["InternalInconsistency",
      "Invariant" -> "PolyDivideByZero", "a" -> a, "b" -> b]]
  ];
  A = collectCoeffs[a, x, ext];
  B = collectCoeffs[b, x, ext];
  dB  = degIn[B, x];
  lcB = leadingCoeffIn[B, x];
  q = 0;
  While[True,
    dA = degIn[A, x];
    If[dA < dB, Break[]];
    lcA  = leadingCoeffIn[A, x];
    term = reduceExtCoeff[lcA / lcB, ext] * x^(dA - dB);
    q    = q + term;
    A    = collectCoeffs[A - term * B, x, ext];
  ];
  {collectCoeffs[q, x, ext], A}
];

(* polynomialExtendedGCDExt[a, b, x, ext] — half-EEA in K[x].              *)
(*                                                                           *)
(* Returns {g, u, v} with u · a + v · b = g and g monic in x. When ext={}   *)
(* this is equivalent to (but slower than) PolynomialExtendedGCD over ℚ.  *)
(* For the common case ext === {} callers should use polynomialExtendedGCD *)
(* (3-arg form) instead.                                                    *)

ClearAll[polynomialExtendedGCDExt];
polynomialExtendedGCDExt[a_, b_, x_Symbol, ext_List] := Module[
  {r0, r1, s0, s1, t0, t1, qr, q, r2, lc, inv, red},
  red[p_] := collectCoeffs[p, x, ext];
  r0 = red[a]; r1 = red[b];
  s0 = 1; s1 = 0;
  t0 = 0; t1 = 1;
  While[!zeroQ[r1],
    qr = polyDivideExt[r0, r1, x, ext];
    If[tragerFailureQ[qr], Return[qr]];
    {q, r2} = qr;
    {r0, r1} = {r1, r2};
    {s0, s1} = {s1, red[s0 - q * s1]};
    {t0, t1} = {t1, red[t0 - q * t1]};
  ];
  If[zeroQ[r0],
    Return[{0, 0, 0}]
  ];
  lc  = leadingCoeffIn[r0, x];
  inv = reduceExtCoeff[1 / lc, ext];
  {red[r0 * inv], red[s0 * inv], red[t0 * inv]}
];

(* canonicalizePolyEntry: reduce an intermediate HNF entry to keep        *)
(* expression size bounded on matrices with algebraic-number or           *)
(* parametric coefficients.                                                *)
(*                                                                           *)
(* - ext non-empty (algebraic-number extension): push coefficients         *)
(*   through reduceExtCoeff so Root/AlgebraicNumber representatives stay  *)
(*   canonical across steps.                                                *)
(* - $tragerParameters non-empty (transcendental extension): collect        *)
(*   coefficients in z over ℚ(params), each coefficient passed through    *)
(*   Cancel[Together[...]] to keep multivariate rational functions in     *)
(*   reduced form. Without this, repeated PolynomialExtendedGCD calls     *)
(*   accumulate uncancelled (a − 1)^k or (a + 1)^k factors, blowing up    *)
(*   the K[z]-HNF in seconds.                                              *)
(* - Otherwise (pure ℚ path): just Expand.                                 *)

ClearAll[paramCancelCoeff];
paramCancelCoeff[c_] := If[zeroQ[c], 0, Cancel[Together[c]]];

ClearAll[canonicalizePolyEntry];
canonicalizePolyEntry[expr_, x_Symbol, ext_List] := Which[
  zeroQ[expr], 0,
  ext =!= {}, collectCoeffs[expr, x, ext],
  $tragerParameters =!= {},
    Collect[Cancel[Together[expr]], x, paramCancelCoeff],
  True, Expand[expr]
];

(* Backward-compatible single-argument variant (pure ℚ path).              *)
canonicalizePolyEntry[expr_] :=
  If[zeroQ[expr], 0, Expand[expr]];

(* Divide two K[x] polynomials exactly (zero remainder expected), using    *)
(* the extension-aware path when ext is nonempty.                          *)

ClearAll[exactQuotient];
exactQuotient[a_, b_, x_Symbol, ext_List] :=
  Which[
    ext =!= {},
      First[polyDivideExt[a, b, x, ext]],
    $tragerParameters =!= {},
      (* PolynomialQuotient with rational-function (in params) coefficients *)
      (* leaves un-cancelled common factors; route through Cancel after    *)
      (* division so subsequent HNF steps see normalized entries.           *)
      Module[{q = PolynomialQuotient[a, b, x]},
        Collect[Cancel[Together[q]], x, paramCancelCoeff]
      ],
    True,
      PolynomialQuotient[a, b, x]
  ];

ClearAll[hermiteNormalFormOverKz];
hermiteNormalFormOverKz[mat_List, z_Symbol] :=
  hermiteNormalFormOverKz[mat, z, {}];

hermiteNormalFormOverKz[mat_List, z_Symbol, ext_List] := Module[
  {M, m, n, j, i, g, u, v, a, b, newRowJ, newRowI, lc, q, egcd},

  M = Map[canonicalizePolyEntry[#, z, ext] &, mat, {2}];
  m = Length[M];
  n = Length[First[M]];

  Do[
    (* For column j, pivot row = j (we maintain pivots on the diagonal    *)
    (* while j ≤ min(m, n)). If M[[j, j]] == 0 swap in a lower row with   *)
    (* nonzero column-j entry.                                             *)
    If[zeroQ[M[[j, j]]],
      Module[{swapRow = 0, i2},
        Do[
          If[!zeroQ[M[[i2, j]]],
            swapRow = i2; Break[]
          ],
          {i2, j + 1, m}
        ];
        If[swapRow > 0,
          {M[[j]], M[[swapRow]]} = {M[[swapRow]], M[[j]]}
        ]
      ]
    ];

    (* Eliminate column j below the pivot. Two strategies:                  *)
    (*                                                                        *)
    (*  - Pure ℚ or ℚ(α) (no transcendental params): one-step Bezout via    *)
    (*    polynomialExtendedGCD. Fast because cofactors are numeric / in a   *)
    (*    small algebraic extension.                                          *)
    (*                                                                        *)
    (*  - ℚ(params): iterative swap-and-subtract Euclidean reduction. The    *)
    (*    built-in PolynomialExtendedGCD blows up exponentially on           *)
    (*    multivariate-rational coefficients (intermediate Bezout cofactors  *)
    (*    have multivariate polynomial numerators of combinatorial size),    *)
    (*    so we avoid cofactors entirely: at each step, divide the larger-  *)
    (*    degree row by the smaller-degree row and subtract. This gives the *)
    (*    same HNF (same row-span, gcd as pivot entry) but only needs one   *)
    (*    PolynomialQuotient per step. Observed: 7.3s → 0.8s on a deg-16 /  *)
    (*    deg-34 column reduction in ℚ(a,b)[z].                            *)
    Do[
      If[!zeroQ[M[[i, j]]],
        If[ext === {} && $tragerParameters =!= {},
          (* Swap-and-subtract Euclidean on (rJ, rI) over ℚ(params)[z]:    *)
          (* at each step kill a single leading term of the higher-degree  *)
          (* col-j entry by subtracting (coefficient ratio)·z^Δ·(other row) *)
          (* and canonicalise the new col-j entry. The other column        *)
          (* entries accumulate the row operation and are canonicalised    *)
          (* once at the end. We cannot use PolynomialExtendedGCD + Bezout *)
          (* on ℚ(params)[z] — the Bezout cofactors blow up exponentially  *)
          (* (same reason tracking a 2×2 transformation matrix in this     *)
          (* loop would blow up: its cofactor entries are exactly the      *)
          (* Bezout cofactors the iterative approach avoids materialising).*)
          Module[{rJ = M[[j]], rI = M[[i]], dJ, dI, lcJ, lcI, tmul,
                  rIj, rJj},
            rJj = rJ[[j]];
            rIj = rI[[j]];
            dJ = Exponent[Expand[rJj], z];
            dI = Exponent[Expand[rIj], z];
            While[!zeroQ[rIj],
              If[dI < dJ,
                {rJ, rI} = {rI, rJ};
                {rJj, rIj} = {rIj, rJj};
                {dJ, dI} = {dI, dJ};
              ];
              lcJ  = Coefficient[rJj, z, dJ];
              lcI  = Coefficient[rIj, z, dI];
              tmul = paramCancelCoeff[lcI / lcJ] * z^(dI - dJ);
              rI   = rI - tmul * rJ;
              rIj  = canonicalizePolyEntry[rI[[j]], z, ext];
              rI[[j]] = rIj;
              dI   = If[zeroQ[rIj], -Infinity, Exponent[Expand[rIj], z]];
            ];
            M[[j]] = canonicalizePolyEntry[#, z, ext] & /@ rJ;
            M[[i]] = canonicalizePolyEntry[#, z, ext] & /@ rI;
          ]
          ,
          (* Bezout via polynomial extended GCD (fast path for ℚ / ℚ(α)) *)
          egcd = If[ext === {},
            polynomialExtendedGCD[M[[j, j]], M[[i, j]], z],
            polynomialExtendedGCDExt[M[[j, j]], M[[i, j]], z, ext]
          ];
          {g, u, v} = egcd;
          a        = exactQuotient[M[[j, j]], g, z, ext];
          b        = exactQuotient[M[[i, j]], g, z, ext];
          newRowJ  = u * M[[j]] + v * M[[i]];
          newRowI  = a * M[[i]] - b * M[[j]];
          M[[j]]   = canonicalizePolyEntry[#, z, ext] & /@ newRowJ;
          M[[i]]   = canonicalizePolyEntry[#, z, ext] & /@ newRowI
        ]
      ],
      {i, j + 1, m}
    ];

    (* Optional: ensure pivot has unit (rational) leading coefficient.    *)
    If[!zeroQ[M[[j, j]]],
      lc = leadingCoeffIn[M[[j, j]], z];
      If[!zeroQ[lc - 1],
        M[[j]] = canonicalizePolyEntry[#, z, ext] & /@
                   (M[[j]] * reduceExtCoeff[1/lc, ext])
      ]
    ];

    (* Reduce above-pivot entries modulo the pivot.                        *)
    If[!zeroQ[M[[j, j]]],
      Do[
        If[!zeroQ[M[[i, j]]],
          q       = exactQuotient[M[[i, j]], M[[j, j]], z, ext];
          M[[i]]  = canonicalizePolyEntry[#, z, ext] & /@ (M[[i]] - q * M[[j]])
        ],
        {i, 1, j - 1}
      ]
    ],
    {j, Min[m, n]}
  ];

  M
];

(* ::Section:: *)
(* polynomialHNFOverKz — legacy wrapper used by the existing TestPrincipalGen *)
(* suite. Delegates to the new HNF after clearing row-wise denominators.    *)

ClearAll[polynomialHNFOverKz];
polynomialHNFOverKz[mat_List, z_Symbol] :=
  polynomialHNFOverKz[mat, z, {}];

polynomialHNFOverKz[mat_List, z_Symbol, ext_List] := Module[{cleared},
  cleared = Map[
    Function[row,
      Module[{den = PolynomialLCM @@ (Denominator[Together[#]] & /@ row)},
        canonicalizePolyEntry[#, z, ext] & /@ (row * den)
      ]
    ],
    mat
  ];
  hermiteNormalFormOverKz[cleared, z, ext]
];

(* ::Section:: *)
(* normalizeAtInfinity                                                      *)
(*                                                                           *)
(* "Normalize at infinity" reduction (Trager 1984 Ch 2 §3): repeatedly      *)
(* replace one column of M with a Q-linear combination of columns scaled by *)
(* z^(k[i]−k[i0]) until the leading-at-infinity matrix N has nonzero        *)
(* determinant, i.e. rows are Q-linearly independent at infinity.           *)
(*                                                                           *)
(* We use the SCALED order (n × ord_∞) so integers fit naturally with the  *)
(* simple-radical basis {w_j = y^j / d_j}. The per-column k[j] is the      *)
(* minimum scaledInfOrder across rows in column j.                           *)
(*                                                                           *)
(* Input:  n × n matrix M (rows = candidate generators; cols = w_j         *)
(*         coefficients), basis descriptor, z.                               *)
(* Output: Association with "matrix" (the normalized matrix) and            *)
(*         "ks" (the per-column scaled min orders).                         *)

ClearAll[scaledInfLeadValue];
(* "Leading Q value" of a column-j entry c at its scaled min order k. We   *)
(* represent the entry's behavior at infinity as                             *)
(*   c · w_j  ∼  (Q-valued leading term) · x^(−k/n)    as x → ∞.            *)
(* The Q-valued leading term is what we store in N.                          *)
(* For c = p(z)/q(z), the leading coefficient at infinity is lc(p)/lc(q)   *)
(* when scaledInfOrder(c, j) == k; the w_j contribution has leading        *)
(* coefficient 1 relative to an implicit x^(−(j m − n deg d_j)/n) factor   *)
(* that cancels in the ratios we form for N.                                *)

scaledInfLeadValue[c_, j_Integer, basis_?basisDescriptorQ] := Module[
  {z, t, num, den, degN, degD, lcN, lcD},
  If[zeroQ[c], Return[0]];
  z   = basis["x"];
  t   = Together[c];
  num = Expand[Numerator[t]];
  den = Expand[Denominator[t]];
  degN = Exponent[num, z];
  degD = Exponent[den, z];
  lcN  = Coefficient[num, z, degN];
  lcD  = Coefficient[den, z, degD];
  (* Together + Cancel is enough to canonicalise a ratio of two polynomials *)
  (* in the parameters; Simplify is too aggressive (and can hang) on        *)
  (* parametric expressions.                                                 *)
  Cancel[Together[lcN / lcD]]
];

(* Per-ROW scaled min order at infinity: for row i, the min over j of      *)
(* scaledInfOrder(M[i, j+1], j, basis). This is the "infinity order" of   *)
(* the AF element represented by row i (in scaled convention).             *)

ClearAll[rowScaledMinOrder];
rowScaledMinOrder[row_List, basis_?basisDescriptorQ] := Module[{orders},
  orders = Table[
    scaledInfOrder[row[[j + 1]], j, basis],
    {j, 0, Length[row] - 1}
  ];
  orders = DeleteCases[orders, Infinity];
  If[orders === {}, Infinity, Min[orders]]
];

ClearAll[buildInfLeadMatrix];
(* Build the Q-matrix N of leading-at-infinity values for the current M.   *)
(* Entry N[[i, j+1]] is the Q-scalar coefficient of the leading term of   *)
(* M[[i, j+1]] · w_j at infinity when row i is normalized to have minimum *)
(* order 0 (i.e. after scaling by z^(k[i]/n)).                             *)
(*                                                                           *)
(* If an entry's scaledInfOrder exceeds the row's min order k[i], the     *)
(* entry contributes 0 to N; entries AT the min order contribute their    *)
(* leading-coefficient-at-infinity value.                                   *)

buildInfLeadMatrix[M_List, ks_List, basis_?basisDescriptorQ] := Module[
  {nrows, ncols},
  nrows = Length[M];
  ncols = Length[First[M]];
  Table[
    Module[{entry = M[[i, j + 1]], ord},
      ord = scaledInfOrder[entry, j, basis];
      If[ord === Infinity || ord > ks[[i]],
        0,
        scaledInfLeadValue[entry, j, basis]
      ]
    ],
    {i, nrows}, {j, 0, ncols - 1}
  ]
];

ClearAll[normalizeAtInfinity];
(* ROW-based iteration. We view the matrix M as a list of rows (each row  *)
(* an AF element's basis coefficients). The algorithm kills Q-linear      *)
(* dependencies among leading-at-infinity terms of ROWS by combining      *)
(* rows with z-power weights.                                               *)
(*                                                                           *)
(* The Trager 1984 §2.3 algorithm is presented in column-operation form;   *)
(* this implementation works on rows directly, swapping the roles of rows  *)
(* and columns throughout (mathematically equivalent under transpose).     *)
(*                                                                           *)
(* Per-row scaled min order k[i] is an integer n·(ord at infinity of the  *)
(* row's AF element). Combining row i0 ← Σ ℓ[i] · z^((k[i]−k[i0])/n) · row_i *)
(* for a left-nullspace vector ℓ of N strictly raises k[i0].                *)

normalizeAtInfinity[mat_List, basis_?basisDescriptorQ] := Module[
  {M, n, z, ks, N, iter, maxIter, nullVec, nonZeroIdx, i0, k0, i,
   combined, detN},

  M  = mat;
  n  = Length[M];
  z  = basis["x"];
  maxIter = 4 * n + 8;

  ks = Table[rowScaledMinOrder[M[[i]], basis], {i, n}];
  ks = ks /. Infinity -> 0;

  iter = 0;
  While[iter < maxIter,
    iter++;
    N = buildInfLeadMatrix[M, ks, basis];
    (* Together + Cancel canonicalises ratios over ℚ(params) without the    *)
    (* combinatorial blow-up that Simplify can trigger on parametric input. *)
    detN = Cancel[Together[Det[N]]];
    If[!zeroQ[detN], Break[]];

    (* Left-nullspace of N: vectors ℓ with ℓ · N = 0. NullSpace[Transpose[N]] *)
    (* returns these as a list of vectors.                                   *)
    nullVec = NullSpace[Transpose[N]];
    If[nullVec === {}, Break[]];
    nullVec = First[nullVec];

    nonZeroIdx = Flatten @ Position[nullVec, _?(!zeroQ[#] &), {1}, Heads -> False];
    If[nonZeroIdx === {}, Break[]];

    (* Pick i0 = row index with minimum k[i0] among nonzero positions of ℓ. *)
    i0 = First[nonZeroIdx];
    k0 = ks[[i0]];
    Do[
      If[ks[[idx]] < k0, i0 = idx; k0 = ks[[idx]]],
      {idx, Rest[nonZeroIdx]}
    ];

    (* Combine rows: row i0 ← Σ_i ℓ[i] · z^((k[i] − k[i0])/n) · row_i.      *)
    (* All k[i] − k[i0] ≥ 0 among nonzero ℓ positions. For this combination *)
    (* to be a K[z]-combination of the original rows (i.e. to preserve the *)
    (* row-module over K[z]), we require the z-power exponents to be non-  *)
    (* negative integers.                                                    *)
    combined = ConstantArray[0, Length[First[M]]];
    Do[
      If[!zeroQ[nullVec[[i]]],
        Module[{shift = (ks[[i]] - k0) / basis["n"]},
          combined = combined + nullVec[[i]] * Expand[z^shift * M[[i]]]
        ]
      ],
      {i, 1, n}
    ];

    (* Together + Cancel is the parameter-safe canonical-form pass.         *)
    combined = Cancel[Together[#]] & /@ combined;
    M[[i0]] = combined;
    ks[[i0]] = rowScaledMinOrder[M[[i0]], basis];
    If[ks[[i0]] === Infinity, ks[[i0]] = 0];
  ];

  <|"matrix" -> M, "ks" -> ks, "iterations" -> iter|>
];

(* ::Section:: *)
(* Legacy helpers retained for tests                                        *)

ClearAll[zAdicRowReduce];
zAdicRowReduce[mat_List, z_Symbol] := Module[
  {M, r, c, j, i, pivRow, pivOrd, ord, factor},

  M = mat;
  r = Length[M];
  c = Length[First[M]];

  Do[
    pivRow = -1; pivOrd = Infinity;
    Do[
      If[!zeroQ[M[[i, j]]],
        ord = zAdicOrderAtZero[M[[i, j]], z];
        If[ord < pivOrd, pivOrd = ord; pivRow = i]
      ],
      {i, j, r}
    ];
    If[pivRow === -1, Continue[]];

    If[pivRow =!= j,
      {M[[j]], M[[pivRow]]} = {M[[pivRow]], M[[j]]}
    ];

    Do[
      If[i =!= j && !zeroQ[M[[i, j]]],
        factor = Together[M[[i, j]] / M[[j, j]]];
        M[[i]] = MapThread[Together[#1 - factor * #2] &, {M[[i]], M[[j]]}]
      ],
      {i, r}
    ],
    {j, Min[r, c]}
  ];

  M
];

ClearAll[noPoleAtZeroQ];
noPoleAtZeroQ[af_?afElementQ, z_Symbol] :=
  AllTrue[af["Coeffs"], zAdicOrderAtZero[#, z] >= 0 &];

ClearAll[noPoleAtZeroRowQ];
noPoleAtZeroRowQ[row_List, z_Symbol] :=
  AllTrue[row, zAdicOrderAtZero[#, z] >= 0 &];
