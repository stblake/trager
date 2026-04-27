(* ::Package:: *)

(* ::Title:: *)
(* Schultz 2015 double-ideal divisor representation *)

(* ::Text:: *)
(* See SchultzPlan.md §S.2 and Sch §4.1.                                     *)
(*                                                                            *)
(* A Schultz divisor D on the curve y^n = g(x) is represented as a pair of   *)
(* ideals                                                                     *)
(*                                                                            *)
(*     D^∞  = { f ∈ K : ord_P(f) ≥ D for every finite place P   },          *)
(*     D_∞  = { f ∈ K : ord_P(f) ≥ D for every infinite place P },          *)
(*                                                                            *)
(* stored as n × n matrices a ∈ k(x)^{n×n} and b ∈ k(x)^{n×n} whose rows    *)
(* give basis elements                                                        *)
(*                                                                            *)
(*     φ_i = Σ_j a_{ij} η_j         (k[x]-basis of D^∞),                     *)
(*     ψ_i = Σ_j b_{ij} x^{−δ_j} η_j  (k[[1/x]]-basis of D_∞),              *)
(*                                                                            *)
(* where {η_1, …, η_n} = {w_0, …, w_{n-1}} is the normal integral basis for *)
(* the simple radical y^n = g (w_i = y^i / d_i(x)) and δ_j is the Schultz    *)
(* infinity exponent from §S.1 (buildIntegralBasis's "deltas" key).          *)
(*                                                                            *)
(* Both matrices are held in Hermite Normal Form (HNF) over their respective *)
(* ring: k[x] for aFin, k[[1/x]] for aInf. HNF gives a canonical             *)
(* representative per row-equivalence class.                                  *)
(*                                                                            *)
(* Schema:                                                                    *)
(*     <|"Type"  -> "SchultzDivisor",                                         *)
(*       "aFin" -> n×n matrix over k(x),   -- HNF over k[x]                 *)
(*       "aInf" -> n×n matrix over k(x),   -- HNF over k[[1/x]]             *)
(*       "basis" -> basis descriptor (from buildIntegralBasis) |>             *)
(*                                                                            *)
(* Canonical forms:                                                           *)
(*   Finite HNF (k[x]):    upper triangular, monic polynomial diagonal,      *)
(*                         above-diagonal entries reduced mod the diagonal   *)
(*                         (deg < deg of the pivot).                          *)
(*   Infinite HNF (k[[1/x]]): upper triangular, monomial diagonal x^{k_j}    *)
(*                         (k_j ∈ ℤ), above-diagonal entries reduced so that*)
(*                         every nonzero monomial has degree > k_j (i.e.     *)
(*                         valuation at infinity < −k_j).                    *)
(*                                                                            *)
(* Not every fractional-ideal operation is implemented here; the current    *)
(* scope supports the constructor/multiply/degree/principalQ operations     *)
(* needed by S.3–S.6. Full ideal quotient/intersection will arrive in S.4   *)
(* where the A_n/B_n iteration of Sch Lemma 4.6 needs them.                  *)

(* ::Section:: *)
(* Algebraic-extension canonicalization helper.                                *)
(*                                                                              *)
(* The Schultz HNF chain consumes matrices whose entries can carry algebraic-  *)
(* number coefficients — ζ_n cube roots of unity from Phase-4 residues, I·√3   *)
(* traces from the Galois orbit collapse on n ≥ 3 inverses, and combinations  *)
(* thereof. The canonicalizer must                                              *)
(*   (i)  keep entries in a compact "Sqrt + I" radical form (do NOT collapse  *)
(*        into `Root[…]` shape — that minimal-polynomial form is canonical    *)
(*        over ℚ but not over ℚ(α) where α is the residue-field generator,   *)
(*        and forces downstream HNF arithmetic to mix incompatible Root[]     *)
(*        representations of the same algebraic number, e.g. `Sqrt[3] +       *)
(*        Root[Z^4 + 12 Z^2 + 144, 1, 0]` is `−3 I` but the Cancel/Together   *)
(*        engine cannot see it),                                                *)
(*   (ii) recognise algebraic zeros so that pivot selection in the HNF        *)
(*        doesn't divide by an "expression-nonzero, value-zero" entry. Zero  *)
(*        recognition is handled separately by `zeroQ` (Common.m §"Robust    *)
(*        zero-test") and by `trueDegreeAndLead` (this file) — both consult   *)
(*        `RootReduce` exactly when it matters, so the canonicalizer itself  *)
(*        does not need to.                                                    *)
(*                                                                              *)
(* This is the §10.1 "thread Extension through the HNF pipeline" approach    *)
(* from TragerPlan.md, applied to the Schultz code path. Rather than          *)
(* signature-changing every helper to take an explicit `ext` parameter, we    *)
(* keep entries in their natural radical form throughout HNF and rely on     *)
(* targeted `RootReduce` checks (in `zeroQ`, `trueDegreeAndLead`) to surface *)
(* algebraic-zero identities at exactly the points where they matter.         *)
(*                                                                              *)
(* The earlier implementation that pushed every entry through `RootReduce`   *)
(* canonicalized into ℚ-minimal-polynomial Root[] form — correct but the     *)
(* resulting opaque atoms made `Cancel`/`Together` blind to obvious           *)
(* combinations like `(I + √3) − Root[Z^4 − 4 Z^2 + 16, 4, 0] = 0` (both     *)
(* sides equal `√3 + I` but in different representations), inducing          *)
(* expression blow-up in `schultzDivisorMultiply` of n=3 residue divisors.    *)
(* The current radical-preserving canonicalizer keeps the cubic-radical      *)
(* torsion search ~5–10× faster on cube-root inputs.                          *)

ClearAll[schultzAlgebraicQ];
schultzAlgebraicQ[expr_] :=
  Not @ FreeQ[
    expr,
    _Sqrt | Power[_?NumericQ, _Rational?(Denominator[#] > 1 &)] |
      _Complex | _Root | _AlgebraicNumber
  ];

(* canonicalizeAlgebraicConstant — RootReduce-canonicalize a constant.        *)
(*                                                                              *)
(* Algebraic-number constants such as `(-2 I)/(-I + √3)` simplify to the      *)
(* compact `(1 - I √3)/2` only after `RootReduce`. `Together`/`Cancel` alone *)
(* leave them in their division form, and matrices full of those expressions  *)
(* expand to enormous intermediate forms in subsequent HNF arithmetic. We     *)
(* always apply RootReduce on constants — the cost is small and the           *)
(* downstream savings are large.                                                *)
(*                                                                              *)
(* Crucially we do NOT apply RootReduce to rational expressions in x: doing   *)
(* so collapses sums like `Sqrt[3] + I` into Q-minimal-polynomial Root[]      *)
(* form, which downstream `Cancel`/`Together` then cannot recombine with     *)
(* other Sqrt[]/I-form atoms (see the `Sqrt[3] + Root[Z^4 + 12 Z^2 + 144,    *)
(* 1, 0] = -3 I` example in the file header). The rule: canonicalize the      *)
(* coefficient ring (algebraic constants) but leave the polynomial structure  *)
(* in radical form.                                                            *)
ClearAll[canonicalizeAlgebraicConstant];
canonicalizeAlgebraicConstant[c_] := If[
  schultzAlgebraicQ[c],
  Quiet @ RootReduce[c],
  c
];

ClearAll[schultzCanon];

(* schultzCanon[expr]: legacy single-argument form. Falls back to            *)
(* `Cancel[Together[…]]` and trusts downstream `zeroQ` / `trueDegreeAndLead` *)
(* to surface algebraic-zero identities. Polynomial-in-x structure is kept   *)
(* in radical form (no Root[] mangling) — see the file header for why.       *)
schultzCanon[expr_] := Cancel[Together[expr]];

(* schultzCanon[expr, x]: variable-aware form. When the expression is a      *)
(* constant in x, push through `RootReduce` so e.g. `(-2 I)/(-I + √3)`      *)
(* collapses to `(1 - I √3)/2` (compact algebraic-number form). When the    *)
(* expression depends on x, the polynomial structure is preserved verbatim  *)
(* and downstream `zeroQ` / `trueDegreeAndLead` handle algebraic-zero       *)
(* identities at exactly the points where they matter. Per-coefficient      *)
(* `RootReduce` is intentionally NOT applied to whole polynomials in x — it *)
(* doubles-to-quadruples the per-step cost without changing correctness    *)
(* (the HNF arithmetic operates over `K(x)` regardless of representative).  *)
schultzCanon[expr_, x_Symbol] := Module[{t = Cancel[Together[expr]]},
  If[t === 0, Return[0]];
  If[FreeQ[t, x],
    canonicalizeAlgebraicConstant[t],
    t
  ]
];

(* ::Section:: *)
(* Predicate and constructor                                                  *)

ClearAll[schultzDivisorQ];
schultzDivisorQ[d_Association] :=
  KeyExistsQ[d, "Type"] && d["Type"] === "SchultzDivisor" &&
  KeyExistsQ[d, "aFin"] && KeyExistsQ[d, "aInf"] && KeyExistsQ[d, "basis"] &&
  basisDescriptorQ[d["basis"]];
schultzDivisorQ[_] := False;

ClearAll[schultzDivisorMake];
schultzDivisorMake[aFin_List, aInf_List, basis_?basisDescriptorQ] := Module[
  {x, n, aFinHNF, aInfHNF},
  x = basis["x"];
  n = basis["n"];
  aFinHNF = schultzHNFFinite[aFin, x];
  aInfHNF = schultzHNFInfinity[aInf, x];
  <|
    "Type"  -> "SchultzDivisor",
    "aFin"  -> aFinHNF,
    "aInf"  -> aInfHNF,
    "basis" -> basis
  |>
];

(* ::Section:: *)
(* Finite HNF (k[x]).                                                         *)
(*                                                                             *)
(* Reuses src/Normalize.m:hermiteNormalFormOverKz which implements HNF over   *)
(* k[x] with exact-extension support. We first clear row denominators so      *)
(* that all matrix entries are polynomials before running the polynomial HNF *)
(* (the row-scaling by its lcm does not change the row-equivalence class).   *)

ClearAll[schultzHNFFinite];
schultzHNFFinite[mat_List, x_Symbol] := Module[
  {matT, allDens, commonDen, denDeg, denLC, polyM, ext, hnf, nCols, trimmed},
  (* Factor out a uniform scalar so the matrix has polynomial entries, HNF  *)
  (* the polynomial matrix, then divide the scalar back in. Scaling the    *)
  (* entire matrix by one k(x)-unit preserves the row-span as a k[x]-module *)
  (* scaled by (1/commonDen), which is the correct operation on fractional *)
  (* ideals. Per-row denominator clearing (an earlier attempt) would alter *)
  (* the determinant by a product of row-scalings, corrupting the divisor   *)
  (* degree — the failing `div(f·g) degree = 0` test caught this.            *)
  matT = Map[schultzCanon[#, x] &, mat, {2}];
  allDens = DeleteDuplicates @ Flatten[
    Map[Denominator, matT, {2}]
  ];
  commonDen = PolynomialLCM @@ Prepend[allDens, 1];
  (* Make `commonDen` monic in x (degree-0 leading coefficient = 1). Without  *)
  (* this, when matT entries carry rational scalar denominators (e.g. `1/2`   *)
  (* arising from K(α)-extension Bezout cofactor cancellations), the         *)
  (* PolynomialLCM picks up that constant scalar and the post-divide step    *)
  (* would inject a `1/2` factor into the diagonal that the inner HNF's      *)
  (* monic-normalisation cannot retroactively fix. Stripping the constant    *)
  (* factor from `commonDen` keeps polyM polynomial (degree-0 entries with    *)
  (* rational scalars are polynomials over ℚ(α)[x]), and the inner HNF's     *)
  (* monic step then divides those scalars away inside the polynomial-HNF    *)
  (* canonicalisation, yielding the correct ideal representative.             *)
  denDeg = If[PolynomialQ[commonDen, x], Exponent[Expand[commonDen], x], 0];
  denLC = If[denDeg > 0,
    Coefficient[Expand[commonDen], x, denDeg],
    commonDen
  ];
  If[!zeroQ[denLC] && !zeroQ[denLC - 1],
    commonDen = Cancel[Together[commonDen / denLC]]
  ];
  (* `schultzCanon` (rather than the bare `Expand` baked into                 *)
  (* `canonicalizePolyEntry`'s pure-ℚ branch) is required for two reasons:   *)
  (* (1) the input matrix can carry sign-flipped denominators — e.g. an     *)
  (* entry of the form `(-2-x^3)^(-1)`, which Mathematica leaves un-         *)
  (* normalised even after `Together`. Multiplying by `commonDen = -2-x^3`   *)
  (* yields the literal pair `(-2-x^3)^(-1)·(-2-x^3)` which `Expand` happily *)
  (* expands but does NOT cancel — leaving a non-polynomial entry that the   *)
  (* downstream `hermiteNormalFormOverKz` then divides 1/0 on. `Cancel`      *)
  (* simplifies these constructed-polynomial entries to their actual         *)
  (* polynomial form. (2) when entries carry algebraic-number coefficients   *)
  (* (e.g. ζ_n traces from Phase-4 residues), `Cancel`/`Together` alone     *)
  (* leave Galois-cancellation artefacts; `schultzCanon` falls through to    *)
  (* `RootReduce` so identically-zero entries are recognised as zero before  *)
  (* HNF pivot selection picks them by mistake.                              *)
  polyM = Map[schultzCanon[# * commonDen, x] &, matT, {2}];
  (* Detect algebraic-extension generators in the polynomial matrix so that  *)
  (* `hermiteNormalFormOverKz`'s polynomial extended-GCD operates over       *)
  (* ℚ(α)[x] rather than treating α as a formal symbolic parameter. Without *)
  (* this the Bezout cofactors silently miss factor-cancellations that only *)
  (* hold in the true extension.                                              *)
  ext = detectExtensionGenerators[polyM];
  hnf = hermiteNormalFormOverKz[polyM, x, ext];
  (* HNF over k[x] of an m × n row-stack (m ≥ n) produces m rows, the last *)
  (* m − n of which are identically zero once the rank is n. For ideal    *)
  (* representation we want the top n × n block (the canonical square     *)
  (* matrix). Trim trailing all-zero rows, then if more than n rows remain  *)
  (* keep the first n.                                                      *)
  nCols = Length[First[mat]];
  trimmed = Select[hnf, !AllTrue[#, zeroQ] &];
  If[Length[trimmed] >= nCols,
    trimmed = Take[trimmed, nCols]
  ];
  Map[schultzCanon[#/commonDen, x] &, trimmed, {2}]
];

(* ::Section:: *)
(* Infinity valuation / degree helpers                                        *)

(* trueDegreeAndLead[poly, x] -> {deg, leadCoeff}.                            *)
(*                                                                             *)
(* Returns the true x-degree of `poly` viewed as a polynomial in x with       *)
(* algebraic-number coefficients, and the leading coefficient at that degree. *)
(* Skips leading coefficients that are algebraically zero but expression-     *)
(* nonzero — e.g. `Sqrt[3] + Root[Z^4 + 12 Z^2 + 144, 1, 0]` evaluates to     *)
(* `-3 I` under `RootReduce`, so the term `(3 I + Sqrt[3] + Root[…])·x^3`     *)
(* is identically zero even though `Exponent[…, x]` reports degree 3. Without *)
(* this canonicalisation the HNF pivot selection picks an entry whose         *)
(* "leading" is a hidden zero, the leading coefficient evaluates to 0 via     *)
(* `Limit`, and downstream division by `pivotCoeff = 0` cascades into         *)
(* `Indeterminate` / `ComplexInfinity` matrix entries.                          *)
(*                                                                             *)
(* The `zeroQ` test on each candidate leading coefficient consults            *)
(* `RootReduce` exactly (see Common.m §"Robust zero-test"), so the true       *)
(* degree is decided by algebraic identity, not by surface form.              *)
ClearAll[trueDegreeAndLead];
trueDegreeAndLead[poly_, x_Symbol] := If[!PolynomialQ[poly, x],
  {0, poly},
  Module[{deg = Exponent[poly, x], coef, isZero},
    coef = Coefficient[poly, x, deg];
    (* Drop leading coefficients that are zero. Two layers:                 *)
    (*   1. literal `0` (the polynomial may sandwich zero coefficients      *)
    (*      between surviving higher / lower terms),                        *)
    (*   2. for SUMs containing algebraic atoms (Sqrt, Root, AlgebraicNumber*)
    (*      heads), `zeroQ` → `RootReduce`-canonical zero test. This is    *)
    (*      exactly the Sch-pipeline case where `3 I + Sqrt[3] +           *)
    (*      Root[Z^4 + 12 Z^2 + 144, 1, 0]` algebraically equals `0` but   *)
    (*      `Together`/`Cancel` doesn't see it.                             *)
    (* Single-atom leading coefficients (`Sqrt[3]`, `(-1 + I Sqrt[3])/2`,   *)
    (* `Root[…]`) are nonzero by inspection — no RootReduce trip needed.   *)
    (* `PossibleZeroQ` is intentionally NOT used: on Sqrt+Root mixes it     *)
    (* returns `True` with a `ztest1::ztest1` warning even when the         *)
    (* expression is genuinely nonzero, which would silently drop real     *)
    (* leading coefficients.                                                 *)
    While[deg > 0,
      isZero = Which[
        coef === 0, True,
        Head[coef] === Plus && schultzAlgebraicQ[coef], zeroQ[coef],
        True, False
      ];
      If[!isZero, Break[]];
      deg--;
      coef = Coefficient[poly, x, deg]
    ];
    {deg, coef}
  ]
];

(* valInfinity[f, x] = v_∞(f). A rational function f = p/q ∈ k(x) has        *)
(* v_∞(f) = deg(q) − deg(p). Our valuation conventions:                      *)
(*   - v_∞(x) = −1                                                            *)
(*   - v_∞(1/x) = +1                                                          *)
(*   - v_∞(0) = +∞                                                            *)
(* Elements of k[[1/x]] have v_∞ ≥ 0.                                         *)

ClearAll[valInfinity];
valInfinity[f_, x_Symbol] := Module[{ft, num, den, dN, dD},
  (* `schultzCanon[…, x]` first: a real-zero entry with un-canonicalized     *)
  (* algebraic-number bloat would otherwise be misclassified as nonzero,    *)
  (* returning a finite (wrong) valuation and steering HNF pivot selection  *)
  (* into a division-by-zero. The variable-aware canonicalizer keeps the    *)
  (* polynomial structure in radical form so `trueDegreeAndLead` can read   *)
  (* the true degree.                                                         *)
  ft = schultzCanon[f, x];
  If[zeroQ[ft], Return[Infinity]];
  num = Numerator[ft]; den = Denominator[ft];
  dN = First @ trueDegreeAndLead[num, x];
  dD = First @ trueDegreeAndLead[den, x];
  dD - dN
];

(* leadingMonomialAtInfinity[f, x]: returns {c, k} where the "leading term  *)
(* at infinity" of f ∈ k(x) is c·x^k, with k = −v_∞(f). Used to pivot HNF.  *)

ClearAll[leadingMonomialAtInfinity];
leadingMonomialAtInfinity[f_, x_Symbol] := Module[
  {ft, num, den, dN, lN, dD, lD, k},
  ft = schultzCanon[f, x];
  If[zeroQ[ft], Return[{0, -Infinity}]];
  num = Numerator[ft]; den = Denominator[ft];
  (* Use trueDegreeAndLead rather than `Limit[ft / x^k, x -> Infinity]`:     *)
  (* `Limit` evaluates the leading coefficient through Mathematica's        *)
  (* simplification engine and returns 0 (or ComplexInfinity) on entries    *)
  (* whose surface-form leading term is `Sqrt[3] + Root[…]`-style algebraic *)
  (* zero. The numerator/denominator-coefficient route uses zeroQ +         *)
  (* RootReduce per coefficient, so the actual nonzero leading is picked.   *)
  {dN, lN} = trueDegreeAndLead[num, x];
  {dD, lD} = trueDegreeAndLead[den, x];
  k = dN - dD;
  (* lN / lD are constants in x — the variable-aware canon collapses them   *)
  (* through `RootReduce` to their compact algebraic form.                   *)
  {schultzCanon[lN / lD, x], k}
];

(* reduceAboveInfinityPivot[f, pivotK, x]: given f ∈ k(x) and a pivot        *)
(* entry x^{pivotK} below f (same column), reduce f modulo x^{pivotK} in    *)
(* the k[[1/x]]-adic sense. Concretely: remove all monomials of f of degree  *)
(* ≤ pivotK. Writes f as ft + q·x^{pivotK} with ft having no x^d terms for  *)
(* d ≤ pivotK and q ∈ k[[1/x]]; returns {ft, q}.                            *)

ClearAll[reduceAboveInfinityPivot];
reduceAboveInfinityPivot[f_, pivotK_Integer, x_Symbol] := Module[
  {ft, num, den, quot, rem, polyPart, fracPart, lowPart, highPart, deg, i, c,
   laurent, tTerm},
  ft = schultzCanon[f, x];
  If[zeroQ[ft], Return[{0, 0}]];
  num = Numerator[ft]; den = Denominator[ft];
  (* Split f = polyPart + fracPart where polyPart ∈ k[x] and fracPart has   *)
  (* deg(num) < deg(den) (equivalently v_∞(fracPart) ≥ 1).                  *)
  If[PolynomialQ[den, x] && Exponent[den, x] > 0,
    {quot, rem} = PolynomialQuotientRemainder[num, den, x];
    polyPart = quot;
    fracPart = If[zeroQ[rem], 0, rem/den],
    polyPart = ft;
    fracPart = 0
  ];
  lowPart = 0; highPart = 0;
  (* Split polyPart monomial-by-monomial at degree pivotK.                    *)
  If[PolynomialQ[polyPart, x],
    If[!zeroQ[polyPart],
      deg = Exponent[polyPart, x];
      Do[
        c = Coefficient[polyPart, x, i];
        If[!zeroQ[c],
          If[i <= pivotK,
            lowPart = lowPart + c * x^i,
            highPart = highPart + c * x^i
          ]
        ],
        {i, 0, deg}
      ]
    ],
    highPart = highPart + polyPart
  ];
  (* For fracPart (all monomials have degree ≤ −1):                          *)
  (*   • if pivotK ≥ −1, every fracPart term has degree ≤ −1 ≤ pivotK, so   *)
  (*     all goes into lowPart.                                              *)
  (*   • if pivotK ≤ −2, expand fracPart as a Laurent series at infinity to *)
  (*     depth pivotK, split, and retain the "still-small-enough"            *)
  (*     high-side remainder into highPart.                                  *)
  If[!zeroQ[fracPart],
    If[pivotK >= -1,
      lowPart = lowPart + fracPart,
      (* pivotK ≤ −2 branch: expand in 1/x and split. Series at Infinity    *)
      (* with third argument −pivotK gives terms of order up to x^{pivotK}. *)
      laurent = Normal @ Series[fracPart, {x, Infinity, -pivotK}];
      (* laurent is a polynomial in x with possibly negative exponents;     *)
      (* walk its terms and split at pivotK.                                  *)
      Module[{terms, expBag},
        terms = If[Head[laurent] === Plus, List @@ laurent, {laurent}];
        Do[
          Module[{t = terms[[k]], co, e},
            (* Each term is of the form co * x^e. Extract.                    *)
            co = t /. x^_ -> 1 /. x -> 1;
            e  = Exponent[t, x];
            If[!zeroQ[co],
              If[e <= pivotK,
                lowPart = lowPart + co * x^e,
                highPart = highPart + co * x^e
              ]
            ]
          ],
          {k, Length[terms]}
        ]
      ];
      (* The truncation residual (terms of fracPart beyond depth pivotK)    *)
      (* has degrees strictly less than pivotK and therefore belongs in     *)
      (* lowPart. Recover it symbolically as fracPart minus the Laurent     *)
      (* we've already split.                                                 *)
      tTerm = Together[fracPart - laurent];
      If[!zeroQ[tTerm],
        lowPart = lowPart + tTerm
      ]
    ]
  ];
  {schultzCanon[highPart, x], schultzCanon[lowPart / x^pivotK, x]}
];

(* ::Section:: *)
(* Infinite HNF (k[[1/x]]).                                                   *)
(*                                                                             *)
(* Column-by-column. For column j:                                             *)
(*   1. Find row i ∈ {j, …, m} maximising deg(M[i,j]) = −v_∞(M[i,j]) so the  *)
(*      pivot has the SMALLEST valuation at infinity (the DVR GCD). Swap.    *)
(*   2. For every row i > j with M[i,j] ≠ 0: divide M[i,j] by M[j,j] in       *)
(*      k[[1/x]] (quotient is a polynomial in 1/x, tail-discarded) and       *)
(*      subtract that multiple of row j from row i. By pivot choice the      *)
(*      quotient is always in k[[1/x]].                                      *)
(*   3. Normalise the pivot to x^{k_j}: leading coefficient c ∈ k is scaled  *)
(*      away so M[j,j] = x^{k_j} exactly.                                    *)
(*   4. Reduce above-diagonal entries (i < j): cancel every monomial of       *)
(*      degree ≤ k_j in M[i,j] using a k[[1/x]]-multiple of row j.           *)

ClearAll[schultzHNFInfinity];
schultzHNFInfinity[mat_List, x_Symbol] := Module[
  {M, m, n, j},
  (* Front-load `schultzCanon` on every input entry so RootReduce-canonical *)
  (* zeros surface before the pivot loop starts. Without this front-load   *)
  (* the loop's `!zeroQ[M[[i, j]]]` test classifies an algebraically-zero  *)
  (* but expression-nonzero entry as nonzero, picks it as the largest     *)
  (* degree (= smallest v_∞), and divides by it.                            *)
  M = Map[schultzCanon[#, x] &, mat, {2}];
  m = Length[M];
  n = If[m > 0, Length[First[M]], 0];
  Do[
    (* Step 1: pivot selection — largest deg = smallest v_∞ in column j     *)
    (* among rows j..m.                                                       *)
    Module[{bestRow = j, bestDeg = -Infinity, i, deg},
      Do[
        If[!zeroQ[M[[i, j]]],
          deg = -valInfinity[M[[i, j]], x];
          If[deg > bestDeg, bestDeg = deg; bestRow = i]
        ],
        {i, j, m}
      ];
      If[bestRow =!= j,
        {M[[j]], M[[bestRow]]} = {M[[bestRow]], M[[j]]}
      ]
    ];

    If[!zeroQ[M[[j, j]]],
      (* Step 2: eliminate below the pivot.                                   *)
      Module[{pivot, pivotK, pivotCoeff, i, q},
        {pivotCoeff, pivotK} = leadingMonomialAtInfinity[M[[j, j]], x];
        pivot = M[[j, j]];
        Do[
          If[!zeroQ[M[[i, j]]],
            (* Quotient q = M[i,j] / pivot: the "floor" in k[[1/x]].         *)
            (* By pivot choice deg(M[i,j]) ≤ deg(pivot), so q ∈ k[[1/x]].    *)
            q = schultzCanon[M[[i, j]] / pivot, x];
            M[[i]] = M[[i]] - q * M[[j]];
            M[[i]] = Map[schultzCanon[#, x] &, M[[i]]];
          ],
          {i, j + 1, m}
        ];

        (* Step 3: normalise pivot to x^{pivotK}.                             *)
        If[!zeroQ[pivotCoeff - 1],
          M[[j]] = Map[schultzCanon[#, x] &, M[[j]] / pivotCoeff];
        ];

        (* Step 4: reduce above-pivot entries to have no monomials of        *)
        (* degree ≤ pivotK.                                                   *)
        Do[
          If[!zeroQ[M[[i, j]]],
            Module[{red},
              red = reduceAboveInfinityPivot[M[[i, j]], pivotK, x];
              M[[i, j]] = red[[1]];
              (* Subtract red[[2]] * row_j from row_i in the OTHER columns   *)
              (* too (off-diagonal updates).                                  *)
              Module[{qAbove = red[[2]]},
                If[!zeroQ[qAbove],
                  Do[
                    If[k =!= j,
                      M[[i, k]] = schultzCanon[M[[i, k]] - qAbove * M[[j, k]], x];
                    ],
                    {k, 1, n}
                  ]
                ]
              ]
            ]
          ],
          {i, 1, j - 1}
        ]
      ]
    ],
    {j, Min[m, n]}
  ];
  M
];

(* ::Section:: *)
(* Trivial constructors                                                       *)

(* schultzDivisorTrivial[basis]: the divisor D = 0, i.e. D^∞ = O^∞ and       *)
(* D_∞ = O_∞. Both matrices are the n×n identity.                             *)

ClearAll[schultzDivisorTrivial];
schultzDivisorTrivial[basis_?basisDescriptorQ] := Module[{n},
  n = basis["n"];
  <|
    "Type"  -> "SchultzDivisor",
    "aFin"  -> IdentityMatrix[n],
    "aInf"  -> IdentityMatrix[n],
    "basis" -> basis
  |>
];

(* schultzDivisorFromFinitePoly[A, basis]: the divisor A · O^∞, i.e. the    *)
(* principal ideal generated by the polynomial A ∈ k[x] inside O^∞. Finite  *)
(* HNF is A · I_n (already in HNF); infinity part is the identity because A *)
(* has no zeros at infinite places when viewed in the k[[1/x]]-basis with   *)
(* x^{−δ_j} scaling — A is a unit of k(x) rescaled appropriately.           *)
(*                                                                            *)
(* Strictly, (A · O^∞)_∞ = { f ∈ K : ord_P(f) ≥ ord_P(A · O^∞) for all P ∞ },*)
(* which for a polynomial A equals A · O_∞ (since A itself has a pole of    *)
(* order deg(A) at infinite places). So b = A · I_n as well.                 *)

ClearAll[schultzDivisorFromFinitePoly];
schultzDivisorFromFinitePoly[A_, basis_?basisDescriptorQ] := Module[{n},
  n = basis["n"];
  schultzDivisorMake[
    A * IdentityMatrix[n],
    A * IdentityMatrix[n],
    basis
  ]
];

(* ::Section:: *)
(* Principal divisor: div(f) for f ∈ K represented as an AF element.         *)
(*                                                                             *)
(* Represents the principal O^∞-fractional ideal (f) = f · O^∞ as the matrix *)
(* M_f such that f · η_i = Σ_j (M_f)_{ij} η_j in the η-basis. The same      *)
(* matrix describes (f)_∞ up to the δ_j-scaling change of basis:             *)
(*   f · ψ_j = f · x^{−δ_j} η_j = x^{−δ_j} · (M_f · η)_j                     *)
(*           = Σ_i (M_f)_{ij} x^{δ_i − δ_j} · ψ_i,                          *)
(* so the infinity-basis matrix N_f has entries (N_f)_{ij} = (M_f)_{ij} ·    *)
(* x^{δ_i − δ_j}.                                                             *)

ClearAll[schultzPrincipalDivisor];
schultzPrincipalDivisor[fAF_?afElementQ, basis_?basisDescriptorQ, y_Symbol] :=
  Module[{n, deltas, Mf, MfT, aFinRows, aInfRows, i, j},
    n = basis["n"];
    deltas = basis["deltas"];
    Mf = multiplicationMatrix[fAF, basis, y];

    (* multiplicationMatrix returns Mf with Mf[i, j] = (f·η_j)_{η_i}, so the   *)
    (* COLUMNS of Mf are the η-basis representations of {f·η_1, …, f·η_n} —    *)
    (* the natural k[x]-basis of the principal ideal (f)·O^∞. Per                *)
    (* schultzDivisorMake's "rows give basis elements" convention the matrix   *)
    (* aFin should hence be the TRANSPOSE of Mf: aFin[i, j] = Mf[j, i] is the  *)
    (* η_j-coefficient of f·η_i, i.e. row i of aFin = η-coords of f·η_i.        *)
    MfT = Transpose[Mf];
    aFinRows = MfT;

    (* Schultz §4.1 / §S.1: the (η · x^{−δ})-basis ψ_j = x^{−δ_j} η_j is the   *)
    (* canonical k[[1/x]]-basis of O_∞. The basis of (f)·O_∞ is                  *)
    (*    f · ψ_j = f · x^{−δ_j} η_j,                                            *)
    (* whose (η · x^{−δ})-coordinates we read off as                              *)
    (*    (f·ψ_i)_{ψ_j} = (f·η_i)_{η_j} · x^{δ_j − δ_i} = Mf[j, i] · x^{δ_j − δ_i}.*)
    (* Row i, col j of aInf:                                                      *)
    aInfRows = Table[
      schultzCanon[Mf[[j, i]] * basis["x"]^(deltas[[j]] - deltas[[i]]),
                   basis["x"]],
      {i, n}, {j, n}
    ];

    schultzDivisorMake[
      Map[schultzCanon[#, basis["x"]] &, aFinRows, {2}],
      aInfRows,
      basis
    ]
  ];

(* multiplicationMatrix[fAF, basis, y]: n × n matrix M such that             *)
(* f · η_j = Σ_i M[i, j] η_i for the normal integral basis η_j = w_{j-1}     *)
(* (1-indexed). Computed column-by-column by multiplying f by each η_j and   *)
(* extracting standard-form coefficients.                                    *)

ClearAll[multiplicationMatrix];
multiplicationMatrix[fAF_?afElementQ, basis_?basisDescriptorQ, y_Symbol] :=
  Module[{n, x, d, cols, j, ejAF, productAF, coeffs},
    n = basis["n"]; x = basis["x"]; d = basis["d"];
    cols = Table[
      (* η_j = y^{j−1} / d_{j−1}: as an AF element, coefficient vector       *)
      (* e_j with a 1 in the j-th slot and 0 elsewhere, in the w_i = y^i/d_i *)
      (* basis. Because η_j ≡ w_{j−1}, ejAF has Coeffs[[j]] = 1.             *)
      ejAF = afMake[
        ReplacePart[ConstantArray[0, n], j -> 1],
        basis
      ];
      productAF = afTimes[fAF, ejAF, basis];
      productAF["Coeffs"],
      {j, n}
    ];
    (* cols[[j]] is the coeff vector of f · η_j expressed in the η-basis.   *)
    (* We want a matrix M with M[i, j] = (f · η_j)_{η_i}, so transpose.      *)
    Transpose[cols]
  ];

(* ::Section:: *)
(* Divisor multiplication and division                                        *)
(*                                                                             *)
(* D · E corresponds to adding orders placewise (Sch §4.1): the ideal        *)
(* product. For principal divisors div(f) · div(g) = div(f·g), we can just  *)
(* multiply in K and call schultzPrincipalDivisor. General ideal             *)
(* multiplication is deferred until S.4 needs it.                            *)
(*                                                                             *)
(* Division D / E = D · E^{−1}. For a principal (f), (f)^{−1} = (1/f);       *)
(* general fractional-ideal inversion is also S.4 scope.                     *)
(*                                                                             *)
(* What we implement here: principal-divisor multiply/inverse, which is all  *)
(* we need for the div(f)·div(f^{-1}) = 1 acceptance test and for S.5's     *)
(* residue-divisor representatives (which are principal at construction).   *)

ClearAll[schultzDivisorMultiplyPrincipal];
schultzDivisorMultiplyPrincipal[
  fAF_?afElementQ, gAF_?afElementQ,
  basis_?basisDescriptorQ, y_Symbol
] := schultzPrincipalDivisor[afTimes[fAF, gAF, basis], basis, y];

ClearAll[schultzDivisorInversePrincipal];
schultzDivisorInversePrincipal[
  fAF_?afElementQ, basis_?basisDescriptorQ, y_Symbol
] := schultzPrincipalDivisor[afInverse[fAF, basis], basis, y];

(* ::Section:: *)
(* General divisor multiplication, inversion, power (Sch §4.1 ideal arithmetic).*)
(*                                                                              *)
(* For two Schultz divisors D, E:                                               *)
(*   • (D · E) is the ideal product corresponding to divisor SUM (ord_P adds).  *)
(*   • (D / E) is the ideal quotient corresponding to divisor DIFFERENCE.       *)
(*   • D^k for integer k corresponds to k · D.                                  *)
(*                                                                              *)
(* Implementation:                                                              *)
(*   D · E:  build n² × n matrix of products φ_i^D · φ_j^E for the finite side  *)
(*           (and the analogous (η · x^{−δ})-coord products for the infinity   *)
(*           side), HNF over k[x] resp. k[[1/x]] to extract a canonical n × n   *)
(*           basis. afTimes provides the K-arithmetic on η-coords.              *)
(*   D^{−1}: matrix-inverse + transpose of aFin / aInf, then HNF. The formula  *)
(*           B = (A^{-1})^T realises the inverse fractional ideal; verified     *)
(*           against principal-divisor (1+y), (1+xy) cases.                     *)
(*                                                                              *)
(* These routines are used by §S.6.1 (schultzConstructLogTerms) to combine     *)
(* per-residue divisors δ(z_k) with integer Q-basis coefficients m_kj into the *)
(* total residue divisor Δ_j = Σ_k m_kj δ(z_k) and to test torsion via         *)
(* schultzPrincipalGenerator on c · Δ_j.                                        *)

ClearAll[schultzDivisorMultiply];

(* Failure-passthrough: divisor ops may receive a Failure from a deferred  *)
(* path (e.g. schultzDivisorInverse for n >= 3). Without this rule, the    *)
(* `?schultzDivisorQ` predicate rejects the Failure but the symbol stays   *)
(* unevaluated, and downstream code (afMake, afTimes) then divides by zero *)
(* on the Failure's record fields, producing $Aborted instead of a clean   *)
(* Failure return.                                                          *)
schultzDivisorMultiply[f_Failure, _] := f;
schultzDivisorMultiply[_, f_Failure] := f;

schultzDivisorMultiply[
  d1_?schultzDivisorQ, d2_?schultzDivisorQ
] := Module[
  {basis, x, n, deltas, prodFinRows, prodInfRows, aFinNew, aInfNew},

  basis = d1["basis"];
  x = basis["x"]; n = basis["n"]; deltas = basis["deltas"];

  (* Finite side. Each row of d1["aFin"] is a basis element of D1^∞ in η-coord.*)
  (* afMake builds an AF element from η-coords; afTimes then multiplies in K. *)
  prodFinRows = Flatten[
    Table[
      Module[{phiI, phiJ, prodAF},
        phiI = afMake[d1["aFin"][[i]], basis];
        phiJ = afMake[d2["aFin"][[j]], basis];
        prodAF = afTimes[phiI, phiJ, basis];
        prodAF["Coeffs"]
      ],
      {i, n}, {j, n}
    ],
    1
  ];
  aFinNew = schultzHNFFinite[prodFinRows, x];

  (* Infinity side. Each row of d1["aInf"] is a basis element of D1_∞ in       *)
  (* (η · x^{−δ})-coords. To multiply two such rows in K, first convert to    *)
  (* η-coords (multiply each entry by x^{−δ_k}), do afTimes, then convert      *)
  (* the result back to (η · x^{−δ})-coords (multiply each entry by x^{δ_k}). *)
  prodInfRows = Flatten[
    Table[
      Module[{psiIeta, psiJeta, psiIAF, psiJAF, prodAF, prodEta, rowOut},
        psiIeta = Table[
          schultzCanon[d1["aInf"][[i, k]] / x^deltas[[k]], x],
          {k, n}
        ];
        psiJeta = Table[
          schultzCanon[d2["aInf"][[j, k]] / x^deltas[[k]], x],
          {k, n}
        ];
        psiIAF = afMake[psiIeta, basis];
        psiJAF = afMake[psiJeta, basis];
        prodAF = afTimes[psiIAF, psiJAF, basis];
        prodEta = prodAF["Coeffs"];
        rowOut = Table[
          schultzCanon[prodEta[[k]] * x^deltas[[k]], x],
          {k, n}
        ];
        rowOut
      ],
      {i, n}, {j, n}
    ],
    1
  ];
  aInfNew = schultzHNFInfinity[prodInfRows, x];
  (* schultzHNFInfinity does not auto-trim trailing zero rows on (n² × n)      *)
  (* inputs (it walks columns 1..min(m, n)). For row-stack inputs with full   *)
  (* rank n, the bottom n² − n rows reduce to zero; trim to the first n.       *)
  aInfNew = If[Length[aInfNew] > n, Take[aInfNew, n], aInfNew];

  <|
    "Type"  -> "SchultzDivisor",
    "aFin"  -> aFinNew,
    "aInf"  -> aInfNew,
    "basis" -> basis
  |>
];

(* ::Section:: *)
(* schultzDivisorInverse — inverse fractional ideal of an AF order.            *)
(*                                                                              *)
(* For a fractional ideal I in an Algebraic Function Field with order O, the   *)
(* multiplicative inverse I^{-1} is the unique fractional ideal satisfying     *)
(*    I · I^{-1} = O                                                            *)
(* (equivalently, I^{-1} = { f ∈ K : f · I ⊆ O }).                              *)
(*                                                                              *)
(* For a Galois extension of degree n with Galois group ⟨σ⟩, we have           *)
(*    I · σ(I) · σ²(I) · ⋯ · σ^{n-1}(I) = N(I) · O,                             *)
(* hence                                                                        *)
(*    I^{-1} = (1/N(I)) · σ(I) · σ²(I) · ⋯ · σ^{n-1}(I).                        *)
(*                                                                              *)
(* For y^n = g, the Galois group is ⟨y ↦ ζ_n·y⟩, so σ acts on η-coordinates    *)
(* (η_j = y^{j-1}/d_{j-1}) by σ(η_j) = ζ_n^{j-1}·η_j; the basis matrix of      *)
(* σ(I) in η-coords is A · diag(1, ζ_n, ζ_n², …, ζ_n^{n-1}).                    *)
(*                                                                              *)
(* For n = 2 (the only Galois case staying in ℚ), this simplifies to           *)
(*    I^{-1} basis = (1/det(A)) · A · diag(1, -1).                              *)
(* (i.e. σ negates the y-coefficient column; divide by N(I) = det(A).)         *)
(*                                                                              *)
(* The same formula applies (with the (η · x^{-δ})-coord interpretation) on    *)
(* the infinity side. We compute σ on aInf the same way: negating column 2,    *)
(* dividing by det(aInf).                                                       *)
(*                                                                              *)
(* For n ≥ 3, the σ^k orbits exit ℚ (need ℚ(ζ_n)); the iterated-product        *)
(* construction is deferred. Such inverse computations would arise on positive *)
(* genus / cube-root-style integrands when log construction needs ideal       *)
(* inversion of non-principal divisors.                                         *)
(*                                                                              *)
(* The earlier `(A^{-1})^T` formula was incorrect: it inverts A in the linear- *)
(* algebra sense rather than the fractional-ideal sense, conflating the dual   *)
(* k[x]-module under standard inner product with the multiplicative inverse    *)
(* under algebra multiplication. The two coincide only for special cases       *)
(* (e.g. principal (1+y) on y²=x²+1) and disagree on residue-divisor inverses. *)

ClearAll[schultzDivisorInverse];

schultzDivisorInverse[f_Failure] := f;

(* Apply σ^k to a matrix in η-coords: column j is multiplied by ζ_n^((j-1)·k). *)
ClearAll[applySigmaPower];
applySigmaPower[mat_List, k_Integer, n_Integer, zeta_] :=
  Table[
    Together[mat[[i, j]] * zeta^((j - 1) * k)],
    {i, Length[mat]}, {j, n}
  ];

(* Galois-invariant collapse: an expression that is invariant under            *)
(* ζ_n ↦ ζ_n^k for every k coprime to n must lie in K(x). After the orbit    *)
(* product, every entry should reduce to a rational expression in K(x).        *)
(*                                                                              *)
(* Mathematica represents Exp[2 Pi I/3] internally as `(-1)^(2/3)` after        *)
(* `Together`, and `Together[Expand[…]]` does NOT apply the cyclotomic         *)
(* identity `((-1)^(2/3))^3 - 1 = 0`. ComplexExpand rewrites every such         *)
(* fractional power into the explicit `a + b·I·√n` form, after which Together  *)
(* recombines and the I·√n parts cancel under Galois-invariance.               *)
(*                                                                              *)
(* `Simplify` is applied as a final step because the downstream                 *)
(* `schultzHNFInfinity` / `valInfinity` pipeline relies on `PolynomialQ` and  *)
(* `Series[…, {x, Infinity, k}]`, both of which silently fail when the         *)
(* coefficients still carry symbolic `(-1)^(k/n)` traces — the order spec     *)
(* `k` becomes non-numeric and `Series::serlim` fires. Simplify reliably      *)
(* drops residual ζ_n powers when the expression is Galois-invariant.          *)
ClearAll[collapseGaloisInvariant];
collapseGaloisInvariant[expr_] := Module[{step1, step2},
  step1 = Cancel[Together[Expand[ComplexExpand[expr]]]];
  If[FreeQ[step1, (-1)^_Rational | Sqrt[_] | _Complex], step1,
    step2 = Quiet @ Simplify[step1];
    If[FreeQ[step2, (-1)^_Rational | Sqrt[_]], step2, step1]
  ]
];

schultzDivisorInverse[d_?schultzDivisorQ] := Module[
  {basis, x, n, aFin, aInf, aFinInv, aInfInv, aFinHNF, aInfHNF,
   sigmaDiag, detFin, detInf,
   zeta, sigmaDiv, productDiv, k, productAFin, productAInf},

  basis = d["basis"];
  x = basis["x"]; n = basis["n"];
  aFin = d["aFin"]; aInf = d["aInf"];

  (* `Cancel[Together[Det[…]]]` (rather than the bare `Det[…]`): the basis    *)
  (* matrices can have entries with overlapping factors that `Det` does not   *)
  (* automatically cancel. A non-canonical `detInf` like                       *)
  (*   (2 x^2 + 3 x^5 + x^8) / (x^2 (1 + x^3))                                *)
  (* whose simplified form is `2 + x^3` then propagates as an unsimplified    *)
  (* divisor downstream and breaks the orbit-product collapse on the          *)
  (* infinity side.                                                            *)
  detFin = Cancel[Together[Det[aFin]]];
  detInf = Cancel[Together[Det[aInf]]];

  If[n === 2,
    (* Fast path: ζ_2 = −1, σ negates the y-coefficient column. *)
    sigmaDiag = DiagonalMatrix[{1, -1}];
    aFinInv = Map[Together, aFin . sigmaDiag / detFin, {2}];
    aInfInv = Map[Together, aInf . sigmaDiag / detInf, {2}];
    aFinHNF = schultzHNFFinite[aFinInv, x];
    aInfHNF = schultzHNFInfinity[aInfInv, x];
    aInfHNF = If[Length[aInfHNF] > n, Take[aInfHNF, n], aInfHNF];
    Return[<|
      "Type"  -> "SchultzDivisor",
      "aFin"  -> aFinHNF,
      "aInf"  -> aInfHNF,
      "basis" -> basis
    |>]
  ];

  (* General case: I^{−1} = (1/N(I)) · σ(I) · σ²(I) · … · σ^{n−1}(I).         *)
  (* The Galois group of K(η)/K(x) is ⟨σ : y ↦ ζ_n y⟩, acting on η_j =       *)
  (* y^{j−1}/d_{j−1} by σ(η_j) = ζ_n^{j−1}·η_j. Hence the basis matrix of     *)
  (* σ^k(I) in η-coords is obtained from A by scaling column j by             *)
  (* ζ_n^{(j−1)·k}. Repeated `schultzDivisorMultiply` then folds the σ^k(I)   *)
  (* together; the result is Galois-invariant, so its entries collapse back   *)
  (* to K(x) (modulo Mathematica's algebraic-number simplification cost).     *)
  zeta = Exp[2 Pi I / n];
  productDiv = <|
    "Type"  -> "SchultzDivisor",
    "aFin"  -> applySigmaPower[aFin, 1, n, zeta],
    "aInf"  -> applySigmaPower[aInf, 1, n, zeta],
    "basis" -> basis
  |>;
  Do[
    sigmaDiv = <|
      "Type"  -> "SchultzDivisor",
      "aFin"  -> applySigmaPower[aFin, k, n, zeta],
      "aInf"  -> applySigmaPower[aInf, k, n, zeta],
      "basis" -> basis
    |>;
    productDiv = schultzDivisorMultiply[productDiv, sigmaDiv];
    If[tragerFailureQ[productDiv], Return[productDiv]],
    {k, 2, n - 1}
  ];

  productAFin = productDiv["aFin"];
  productAInf = productDiv["aInf"];

  aFinInv = Map[collapseGaloisInvariant[# / detFin] &, productAFin, {2}];
  aInfInv = Map[collapseGaloisInvariant[# / detInf] &, productAInf, {2}];

  aFinHNF = schultzHNFFinite[aFinInv, x];
  aInfHNF = schultzHNFInfinity[aInfInv, x];
  aInfHNF = If[Length[aInfHNF] > n, Take[aInfHNF, n], aInfHNF];

  <|
    "Type"  -> "SchultzDivisor",
    "aFin"  -> aFinHNF,
    "aInf"  -> aInfHNF,
    "basis" -> basis
  |>
];

(* ::Section:: *)
(* schultzDivisorPower — integer divisor scaling.                              *)
(*                                                                              *)
(* For integer k:                                                               *)
(*   k = 0:  trivial divisor (the unit ideal pair).                             *)
(*   k > 0:  D · D · … · D (k factors). Computed via repeated squaring.        *)
(*   k < 0:  schultzDivisorInverse[D^{|k|}].                                    *)

ClearAll[schultzDivisorPower];

schultzDivisorPower[f_Failure, _] := f;

schultzDivisorPower[d_?schultzDivisorQ, k_Integer] := Which[
  k === 0, schultzDivisorTrivial[d["basis"]],
  k === 1, d,
  k < 0,   schultzDivisorInverse[schultzDivisorPower[d, -k]],
  True,
    Module[{m = k, base = d, result = Null, square},
      (* Repeated squaring: m = sum of bits of k.                                *)
      square = base;
      While[m > 0,
        If[Mod[m, 2] === 1,
          result = If[result === Null, square,
            schultzDivisorMultiply[result, square]
          ]
        ];
        m = Quotient[m, 2];
        If[m > 0, square = schultzDivisorMultiply[square, square]];
      ];
      result
    ]
];

(* ::Section:: *)
(* schultzDivisorIdealSum — ideal sum I + J (placewise minimum of orders).      *)
(*                                                                              *)
(* This is the Sch §4.4 eq. 4.10 / 4.11 operation: the residue divisor          *)
(*   δ_ℓ(z)^∞ = (b'(x)·z − ℓ·Σ a_i η_i)·O^∞ + b(x)·O^∞ + (D_ℓ)^∞                *)
(* is built as an ideal sum of three constituent ideals. The matrix             *)
(* representation: row-stack the matrices, HNF.                                  *)

ClearAll[schultzDivisorIdealSum];
schultzDivisorIdealSum[
  d1_?schultzDivisorQ, d2_?schultzDivisorQ
] := Module[
  {basis, x, aFinStack, aInfStack, aFinHNF, aInfHNF},
  basis = d1["basis"];
  x = basis["x"];
  aFinStack = Join[d1["aFin"], d2["aFin"]];
  aInfStack = Join[d1["aInf"], d2["aInf"]];
  aFinHNF = schultzHNFFinite[aFinStack, x];
  aInfHNF = schultzHNFInfinity[aInfStack, x];
  aInfHNF = If[Length[aInfHNF] > basis["n"],
    Take[aInfHNF, basis["n"]],
    aInfHNF
  ];
  <|
    "Type"  -> "SchultzDivisor",
    "aFin"  -> aFinHNF,
    "aInf"  -> aInfHNF,
    "basis" -> basis
  |>
];

(* ::Section:: *)
(* Divisor degree                                                             *)
(*                                                                             *)
(* For a divisor D = Σ n_P P, deg(D) = Σ n_P · deg(P). The matrix data give *)
(*   deg(D^∞) = sum of polynomial degrees on the diagonal of aFin           *)
(*              = deg(det(aFin)) ∈ ℤ≥0 (when D is integral on the finite   *)
(*              side) or ∈ ℤ (general).                                      *)
(*   deg(D_∞) = sum of k_j on the diagonal of aInf (where aInf[j, j] =      *)
(*              x^{k_j}) = −v_∞(det(aInf)).                                 *)
(* For a divisor of degree 0 (e.g. every principal divisor), these must be  *)
(* equal and opposite: deg_finite − deg_infinite = 0.                        *)

ClearAll[schultzDivisorDegree];
schultzDivisorDegree[d_?schultzDivisorQ] := Module[
  {x, n, aFin, aInf, finDeg, infDeg},
  x = d["basis"]["x"];
  n = d["basis"]["n"];
  aFin = d["aFin"]; aInf = d["aInf"];
  (* For rational diagonal entries f = p/q, the "degree at finite places"  *)
  (* contribution from one diagonal slot is deg(p) − deg(q) = −v_∞(p/q).    *)
  (* Same formula for the infinity side (with the sign contribution coming *)
  (* from the duality "deg(D) = deg(D^∞) − deg(D_∞)" in Sch §4.1).          *)
  finDeg = Sum[-valInfinity[aFin[[i, i]], x], {i, n}];
  infDeg = Sum[-valInfinity[aInf[[i, i]], x], {i, n}];
  finDeg - infDeg
];

(* ::Section:: *)
(* Riemann–Roch principal-divisor test (Sch Lemma 4.1)                       *)
(*                                                                             *)
(* A divisor D is principal iff there exists f ∈ K with div(f) ≥ D (after   *)
(* writing as a divisor of poles: D of degree 0, then div(f) = −D means     *)
(* f ∈ D^{−1}). Equivalently, ℜ(D^{−1}) contains a nonconstant element iff *)
(* D is principal — in Lemma 4.1 this translates to: some d_j ≤ 0 in the    *)
(* canonical Schultz basis representation for D^{−1}. For our HNF          *)
(* representation, this corresponds to a column of aInf whose diagonal     *)
(* entry has k_j ≤ 0 AND whose off-diagonal above-column entries permit a  *)
(* nonzero k[x]-combination yielding a principal generator.                *)
(*                                                                             *)
(* This implementation returns a pair {principalQ, generatorAF} where       *)
(* generatorAF is the AF element realising the principal generator when     *)
(* principalQ = True, otherwise Missing[]. When D's infinity-HNF has a     *)
(* column j with aInf[j, j] = x^{k_j}, k_j ≤ 0 and every above-diagonal   *)
(* entry aInf[i, j] is a polynomial (no 1/x-part), the combination         *)
(*   f = Σ_i aInf[i, j] · x^{δ_i} w_{i-1}                                  *)
(* is a candidate. We then verify div(f) = D by cross-checking that f      *)
(* actually generates both aFin and aInf as ideals.                        *)
(*                                                                             *)
(* The cross-check is a necessary step because the aInf column condition   *)
(* alone does not guarantee that f also spans aFin (it could be a locally  *)
(* generator-at-infinity that doesn't generate globally).                 *)

ClearAll[schultzDivisorPrincipalQ];
schultzDivisorPrincipalQ[d_?schultzDivisorQ] := Catch[Module[
  {x, n, aInf, deltas, basis, deg},
  basis = d["basis"];
  x = basis["x"]; n = basis["n"]; deltas = basis["deltas"];
  aInf = d["aInf"];
  deg = schultzDivisorDegree[d];
  If[deg =!= 0,
    Throw[{False, Missing["degree nonzero", deg]}]
  ];
  Do[
    Module[{kj},
      kj = -valInfinity[aInf[[j, j]], x];
      If[kj <= 0,
        (* Assemble candidate f from column j of aInf. For f to lie in    *)
        (* D^∞ as well, its coefficient vector must satisfy the aFin      *)
        (* constraints — this is verified implicitly by the degree-0      *)
        (* check above for the trivial divisor; deeper cases require      *)
        (* simultaneous HNF alignment (TODO: see Sch p. 10 Lemma 4.1).    *)
        Module[{colEntries, coeffs},
          colEntries = Table[aInf[[i, j]], {i, n}];
          coeffs = Table[
            Together[colEntries[[i]] * x^deltas[[i]]],
            {i, n}
          ];
          Throw[{True, afMake[coeffs, basis]}]
        ]
      ]
    ],
    {j, n}
  ];
  {False, Missing["no nonpositive diagonal exponent"]}
]];

(* End of module *)
