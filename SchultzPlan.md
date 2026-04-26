# Schultz Variant — Integration Plan

**Scope.** A parallel pipeline, selected by `"Schultz" -> True` (default `False`), that replaces Phases 2–5 of `TragerPlan.md` with the machinery of Schultz 2015, "Trager's Algorithm for Integration of Algebraic Functions Revisited" (`papers/Schultz 2015 - IntegrationOnCurves-2hhuby8.pdf`). We keep the outer I/O contract of `IntegrateTrager` identical — same options (plus `"Schultz"`), same return shape, same `Failure[...]` tags. Internally the Schultz path:

- Never does the Phase-2 Möbius shift (`shiftAwayFromInfinity`). Infinite-place poles are handled directly by a second Hermite-style reduction that operates against a `k[[1/x]]`-basis (Schultz §4.3, eq. 4.7–4.9).
- Represents divisors as a *pair* of ideals `(D^∞, D_∞)`, stored as Hermite Normal Form matrices over `k[x]` and `k[[1/x]]` respectively (§4.1, Lemma 4.1). This supersedes the current single-ideal `<|"h", "A"|>` form.
- Builds residue divisors via the norm-resultant formulas eq. 4.10 / 4.11, which already unify branch places and infinite places — we never need the branch-place value check heuristic in `src/PlaceOrder.m:afOrderAtBranchPlace`.
- Implements §5 ("Failing in Style"): decomposes `ω = df + ω_2^∞ + ω_3` using a `k`-basis `γ_1, …, γ_g` of `Ω_2^∞/(Ω_ex + Ω_1)` so that multiple-pole-at-infinity content is always absorbable, and what remains is either zero (elementary) or a first-kind differential (clean `NonElementary` certificate).

**In scope for this plan (matches the rest of the project).** Simple radical extensions `y^n = g(x)`, `g ∈ ℚ(params)[x]`, no zero-divisor pathologies (they cannot arise for an irreducible `y^n − g` once `reduceIrreducibility` has run). All genera ≥ 0.

**Deferred.** Schultz §7 (function algebras over `k(x)`: handling non-field algebras that arise from composita of radicals with zero divisors such as `(y_1^2 − x)(y_2^4 − x)`) is **not** needed for the simple-radical case and is marked out of scope for this variant — see §S.8. Integration of multiple-radical composita remains a `TragerPlan.md` deferred item.

**Reference.** Schultz 2015 (abbr. "Sch"). Section numbers below refer to Sch unless stated. For continuity with the rest of the codebase we keep the three-kind vocabulary from Rosenlicht / Trager Ch 5 where it agrees.

---

## S.0 Option and dispatch

**`Options[IntegrateTrager]`.** Add `"Schultz" -> False` immediately after `"MaxGenus"` in `src/IntegrateTrager.m:54`. Semantics: `True` routes through `SchultzPipeline[validated, reduced, basis, diagnostics, opts]` (Section S.7) instead of the current Phase 2–6 sequence. `False` preserves the existing pipeline bit-for-bit.

**Interaction with `"LogTermsMethod"`.** When `"Schultz" -> True`, the `"LogTermsMethod"` option is ignored (Schultz supplies its own log-term construction — the residue-divisor + principal-generator path of §4.4 is intrinsic to the variant) and a diagnostic line is emitted.

**Interaction with `"MaxGenus"`, `"MaxTorsionOrder"`, `"Parameters"`, `"Verify"`.** Unchanged — they gate or decorate the computation identically.

---

## S.1 Normal integral basis with infinity exponents (Sch §4, Lemma 4.1)

**Goal.** Produce, in one pass, a `k[x]`-basis `η_1, …, η_n` of `O^∞` **and** nonnegative integers `δ_1, …, δ_n` such that `{x^{−δ_i} η_i}` is a `k[[1/x]]`-basis of `O_∞`. This replaces the on-demand `scaledInfOrder` check in `src/Normalize.m:116` with a persistent attribute of the basis.

**Key identity for `y^n = g`, `deg g = m`, `gcd(n, m) = d`, `m = d · m̃`, `n = d · ñ`.** Set `w_i = y^i / d_i(x)` as today. At infinity, each of the `d` places has ramification `ñ`. With `δ_i := max(0, ⌈i m/n⌉ − deg d_i) · ñ/ñ`… actually we use the simpler identity from `TragerPlan.md` §3: the scaled order at infinity of `w_i` equals `n·deg(d_i) − i·m`, so

```
δ_i = max(0, ⌈(i·m − n·deg(d_i)) / gcd(n, m)⌉).
```

This is the unique nonnegative integer such that `x^{−δ_i} w_i` is integral at every infinity place but `x^{−(δ_i−1)} w_i` is not. Derivation: `ord_{∞_j}(w_i) = −(i·m − n·deg d_i)·(ñ/n)` at each infinity place `∞_j`, and we want the smallest `δ_i` with `δ_i · ord_{∞_j}(1/x) + ord_{∞_j}(w_i) ≥ 0`, i.e. `δ_i · ñ ≥ (i·m − n·deg d_i)·(ñ/n) · n / ñ`.

**Work item.**

- `src/Basis.m` — extend `buildIntegralBasis` to also populate the key `"deltas" -> {δ_0, …, δ_{n−1}}` and the Schultz k-invariant `"c" -> 1` (`c = [k_0 : k]` is always 1 for a simple radical over `ℚ(params)` once reduced). No change to existing keys — pure extension.
- `src/Basis.m` — new helper `infinityBasisCoefficients[basis, j]` returning the `k[[1/x]]`-column for `ψ_j = x^{−δ_j} η_j` as a truncated Laurent series in `1/x`. For now return the exact rational form and truncate lazily.
- `tests/TestBasis.m` — add five tests covering `y^2 = x^3 + 1` (genus 1), `y^3 = x + 1` (genus 0), `y^4 = x^5 + 1`, `y^2 = g(x)·(x^2 + 1)` (parametric `c` coefficient), and the worked Example 6.1 `x^3 y + x + y^3 = 0` from Sch §6 — though that last one is outside the simple-radical case, it pins down the genus and δ formulas for cross-checking.

**Acceptance.** The basis association includes `"deltas"` and the sum-formula `δ_1 + ⋯ + δ_n = n + c(g − 1)` (Sch Lemma 4.1 last display). This is a single-line assertion in a regression test.

---

## S.2 Double-ideal divisor representation (Sch §4.1)

**Goal.** Represent a divisor `D` as a pair `⟨D^∞, D_∞⟩`:

- `D^∞ = { f ∈ K | ord_P(f) ≥ D for every finite P }`: stored as an `n × n` matrix `a ∈ k(x)^{n×n}` in HNF over `k[x]` (upper triangular, monic diagonal, above-diagonal entries reduced mod the corresponding diagonal). Interpretation: `φ_i = Σ_j a_{ij} η_j` is a `k[x]`-basis of `D^∞`.
- `D_∞ = { f ∈ K | ord_P(f) ≥ D for every infinite P }`: stored as `b ∈ k(x)^{n×n}` in HNF over `k[[1/x]]` with *monomial* diagonal (powers of `1/x`). Interpretation: `ψ_i = Σ_j b_{ij} x^{−δ_j} η_j` is a `k[[1/x]]`-basis of `D_∞`.

**Operations.** Each divisor-arithmetic operation reduces to HNF after matrix combination:

| Op | Finite matrix | Infinite matrix |
|---|---|---|
| `D · E` | HNF(`a_D · a_E`) | HNF(`b_D · b_E`) |
| `D / E` | "ideal quotient" = HNF(`a_D · a_E^{-1}`) | likewise |
| `D + E` (intersection) | HNF of row stack | likewise |
| `D ∩ E` (sum) | intersection (matrix-kernel) | likewise |

Matrix operations use the project's `canonicalizePolyEntry` / `exactQuotient` helpers (`src/Normalize.m`) so parameter-rich coefficients stay canonical.

**Work item.**

- `src/SchultzDivisor.m` — new module exporting `schultzDivisorMake`, `schultzDivisorMultiply`, `schultzDivisorQuotient`, `schultzDivisorIntersect`, `schultzDivisorDegree`, `schultzDivisorPrincipalQ` (the last is the Riemann–Roch test of Lemma 4.1: check the diagonal of `b` for nonpositive exponents). Build on top of `src/Normalize.m:hermiteNormalFormOverKz` for the finite part; add a new `hermiteNormalFormOverInfinity` that works on `k[[1/x]]`-entries (treat entries as rational functions `p(x)/x^e` with `deg p ≤ e` and pivot by least `1/x`-order).
- `src/SchultzDivisor.m` — `schultzDivisorOfFunction[f, basis]`: given `f ∈ K` represented as an AF element, compute `div(f)` as a pair of matrices. Reduces to multiplying by the matrix representation of `f` acting on the normal basis and re-HNF-ing against the unit ideal.
- `tests/TestSchultzDivisor.m` — principal-divisor round-trip (`div(f)·div(f^{-1}) = 1` for a few rational `f`); `schultzDivisorDegree = 0` for principal divisors; worked examples from Sch §6.1 (`x^3 y + x + y^3 = 0`) reduced to the simple-radical analogue — plus the `y^2 = x(x+5)(x−4)(x−3)` example from Sch §6.2 whose numeric data we can pull out verbatim.

**Acceptance.** Each divisor test passes under both `$tragerParameters = {}` and a parametric setting (e.g. `a` transcendental, `y^2 = x^3 + a`).

---

## S.3 Infinite-place Hermite reduction (Sch §4.3, Lemmas 4.4–4.5, eq. 4.6–4.9)

**Goal.** Subsume `src/Shift.m:shiftAwayFromInfinity` and the existing finite-Hermite `src/Hermite.m:hermiteReduce` into one reduction that treats both kinds of place uniformly.

**Algorithm.** Write the integrand as `ω = Σ_i (a_i(x)/b(x)) η_i dx` with `gcd(b, a_1, …, a_n) = 1`.

1. **Finite multiple poles (Lemma 4.4 part 1).** If `b` is not squarefree, write `b = U V^{l+1}`, solve the Trager congruence `a_i ≡ −l U V' f_i + T Σ_j f_j M_{j,i} (mod V)` where `E T = U V`, and subtract `d(Σ_i f_i η_i / V^l)` into the algebraic part. Identical structure to the current `hermiteReduce` loop but with `M` being the `η`-basis derivation matrix (not diagonal as it is for `w_i = y^i / d_i`).
2. **Infinite multiple poles (Lemma 4.4 part 2 / eq. 4.7–4.9).** Once `b` is squarefree, check `deg(a_i) + δ_i < deg(b)` for every `i`. If not, seek `f_i, g_i ∈ k[x]` satisfying

```
a_i = E T f_i' + T Σ_j f_j M_{j,i} + g_i
deg(f_i) ≤ N − δ_i,        deg(g_i) < deg(b) − δ_i,       N := max_i(deg a_i + δ_i + 1 − deg b).
```

Subtract `Σ_i f_i η_i` into the algebraic part. The linear system is solvable over `k` (polynomial coefficients of `f_i, g_i` are the unknowns) — if solvable, done; if not, the form has a multiple pole at infinity that Hermite cannot remove and the §5 fallback in S.6 takes over.

**Work item.**

- `src/SchultzHermite.m` — new `schultzHermiteReduce[integrand, basis, y]` returning `<|"algPart", "remainder", "D", "Dinf"|>` where `"D"` is the squarefree finite denominator and `"Dinf"` is a flag/record about the degree-at-infinity margin `N`. Internally calls a new `integralBasisDerivativeMatrix[basis]` that returns `M` in the `η`-basis (for the simple-radical `w_i` basis this is diagonal and agrees with `i g'/(n g) − d_i'/d_i` in `src/Arithmetic.m:afD`).
- `src/SchultzHermite.m` — `schultzSolveFiniteCongruence`, `schultzSolveInfinityLinearSystem` helpers.
- `tests/TestSchultzHermite.m` — (a) finite-only inputs must agree with the existing `hermiteReduce` on the simple-radical `w_i` basis; (b) inputs with a pole at infinity (e.g. `∫ √(x^2 + 2x) dx`, which the existing pipeline routes through Phase 2) must finish without a Möbius shift and produce a remainder with `deg(a_i) + δ_i < deg b` for each `i`; (c) an input where the infinity system is unsolvable (`∫ x^2 dx / √(x^3 + 1)`) must return a remainder with the diagnostic flag set so §S.6 can pick it up.

**Acceptance.** On Tier 1 smoke inputs (`TragerPlan.md` §9 Tier 1), the output of `schultzHermiteReduce` differs from `hermiteReduce` only in that it never invokes `shiftAwayFromInfinity` — the final antiderivatives after S.5 reassembly match term-for-term on a Q-basis of the log terms.

---

## S.4 Divisor `D_l` of ramification-l places (Sch §4.4, Lemma 4.6)

**Goal.** Compute, without Puiseux expansions, the effective divisor `D_l = Σ_{r(P) = l} P` collecting all places with ramification index exactly `l`. These are the support data for the residue formulas in S.5.

**Algorithm (Lemma 4.6).**

1. Compute `div(dx) = Π_{P finite} P^{r(P) − 1} · Π_{P ∞} P^{−r(P) − 1}` as a Schultz divisor (Sch eq. above Lemma 4.2).
2. `E(x) = Norm_{K/k(x)}(div(dx)^∞)`; strip multiple factors: `E ← E / gcd(E, E')`.
3. Initialise `A_1^∞ = E·O^∞`, `B_1^∞ = A_1^∞ / div(dx)^∞`, and infinite parts by Sch Lemma 4.6.
4. Loop `n = 1, 2, …`: `A_{n+1} = A_n / B_n`, `B_{n+1} = B_n + A_{n+1}`, `D_n = B_n / B_{n+1}`. Terminate when `B_{n+1} = 1`.

**Work item.**

- `src/SchultzPlaces.m` — new module exporting `divisorOfDx[basis]`, `computeDlDivisors[basis]`, `ramificationIndicesAt[divisorOfA_D_l, basis]`. Uses S.2 divisor arithmetic.
- `tests/TestSchultzPlaces.m` — Sch Example 6.1 (`x^3 y + x + y^3 = 0`) which has explicit `D_1, D_2, D_3` matrices in the paper, plus several simple-radical cases (`y^2 = x^3 + 1`: all finite `D_1` places are regular, `D_1_finite = 4x^3 + 1`; `D_1_∞` is a single place with `r = 1` or absent; etc.).

**Acceptance.** For a simple radical `y^n = g` with squarefree `g`, the computed `D_n` divisor support equals the set of finite roots of `g` (branch places with ramification `n`), and `D_1` collects everything else. Cross-check against the Puiseux-derived data currently produced by `src/PlaceOrder.m`.

---

## S.5 Residue divisor via norm resultants (Sch §4.4, eq. 4.10, 4.11)

**Goal.** Given a Schultz-Hermite-reduced integrand `ω = Σ_i (a_i/b) η_i dx` with `b` squarefree and `deg(a_i) + δ_i < deg(b)`, and for each ramification index `l ≥ 1`:

**Finite residues** — place `δ_l(z)^∞`:

```
δ_l(z)^∞ = (b'(x) z − l Σ_i a_i(x) η_i) · O^∞  +  b(x) · O^∞  +  (D_l)^∞
```

**Infinite residues** — place `δ_l(z)_∞`:

```
δ_l(z)_∞ = ((b/x^{deg b}) z + l Σ_i (a_i x^{1+δ_i}/x^{deg b}) η_i/x^{δ_i}) · O_∞  +  (D_l)_∞
```

A candidate residue `z_0` is a root of

```
Res_x(Norm(b'(x) z − l Σ_i a_i η_i), Norm(b · O^∞ + (D_l)^∞)) = 0
```

for the finite side, eq. 4.11 analog at infinity.

**Work item.**

- `src/SchultzResidues.m` — new `schultzResidueDivisors[integrand, basis]` returning a list of `{z_k, δ(z_k)}` pairs (residue value + Schultz-divisor of places where it occurs). Internally computes the norm via Sch §7 `Trace`/`Norm` of the matrix of multiplication-by-`(b'·z − l·Σ a_i η_i)` on the normal basis.
- `src/SchultzResidues.m` — `schultzResidueQBasis[residues]`: ℚ-basis of the residue span (reuses `src/Residues.m:detectExtensionGenerators` for the ground-field detection, but operating on Schultz divisors).
- `tests/TestSchultzResidues.m` — every residue test from `tests/TestResidues.m` retargeted through the Schultz formula; plus the Sch §6.2 running example `∫ y dx` with `y^2 = x(x+5)(x−4)(x−3)` whose residue divisor `δ(+18)/δ(−18)` is given explicitly in the paper as a `{a, b}` matrix pair.

**Acceptance.** Every existing residue test passes (rational and algebraic residues); the Sch §6.2 example reproduces the `δ(+18)/δ(−18)` matrices verbatim up to HNF canonicalisation.

---

## S.6 Logarithmic part and "failing in style" (Sch §3.2 end, §5)

**Goal.** Given the S.5 residue divisors, produce either an elementary antiderivative or a structured non-elementary certificate.

**S.6.1 Logarithmic part (Sch §3.2 eq. 3.3–3.4).** For each ℚ-basis direction `b_j` of the residue span with collected divisor `Δ_j = Π_k δ(z_k)^{m_{kj}}`, search for the smallest `c_j ≤ MaxTorsionOrder` and a function `F_j ∈ K` with `Δ_j^{c_j} = div(F_j)`. Principal-generator search uses Schultz Lemma 4.1: `Δ_j^{c_j}` is principal iff its `k[[1/x]]`-HNF matrix has a column with every `d_i ≤ 0`, in which case that column's `k[x]`-combination of `η_j` is `F_j`.

When every `c_j` is found, `∫ ω = (algPart) + Σ_j (b_j / c_j) log F_j`.

**S.6.2 Failing in style (Sch §5).** When some `Δ_j` is not torsion inside the bound: the algorithm does **not** simply throw `NonElementary`. Instead compute a `k`-basis `γ_1, …, γ_g` of `Ω_2^∞/(Ω_ex + Ω_1)` (Sch §5.2, Lemma 5.5) and split

```
ω = df + c_1 γ_1 + … + c_g γ_g + (log-terms) + (first-kind residual)
```

so the non-elementary residue is a first-kind differential whose class in `Ω_1` is explicit. Construction (Lemma 5.5):

1. `r = max_i δ_i`.
2. Form the candidate set `S = {x^{l + ρ_i − 1} ε̄_i dx : 1 ≤ i ≤ n, 0 ≤ l ≤ r − 1}` where `{ε_i}` is the complementary infinity basis (Sch Lemma 4.2) and `ρ_i` its exponents.
3. Form the exact-differential set `T = {d(x^l ε̄_i) : 1 ≤ i ≤ n, 0 ≤ l ≤ r − δ_i}`.
4. Pick `g = dim Ω_1` representatives of `S` that are linearly independent over `k` modulo the span of `T`; these are `γ_1, …, γ_g`.
5. Solve the linear system `ω − Σ r_j γ_j ∈ Ω_2^∞ + Ω_ex` for `r_1, …, r_{m-1} ∈ k` (Sch Lemma 5.2) — this removes residues at infinite places so Hermite can proceed.

**Work item.**

- `src/SchultzLogTerms.m` — `schultzConstructLogTerms[residueDivisors, basis, y]` implementing the principal-generator search via Lemma 4.1 over Schultz divisors, with the torsion loop bounded by `"MaxTorsionOrder"`.
- `src/SchultzFailStyle.m` — new module with `complementaryInfinityBasis[basis]` (Lemma 4.2), `secondKindNormalForms[basis]` (Lemma 5.5 → `γ_j` list), `failInStyle[ω, basis, logTerms]` assembling the `df + Σ c_j γ_j + log-part + residual` decomposition.
- `tests/TestSchultzLogTerms.m` — every log-term test from `tests/TestTragerLogTerms.m`; plus the Sch §6.2 worked example which ends with the second-kind `(x^2 − x) y / …` term explicitly.
- `tests/TestSchultzFailStyle.m` — `∫ (2x^2 − x) / √(x^6 + 6(x − 1)^3) dx` (Sch §6.3): torsion order 29, the algorithm must produce the structured non-elementarity certificate.

**Acceptance.** Tier 1 inputs integrate to Trager-equivalent forms. Tier 1b elliptic inputs (`TragerPlan.md` §10.5) that are currently routed through Miller/Kauers succeed under the Schultz path *without needing the fallback*. Non-elementary inputs return a `Failure["NonElementary", <|"Certificate" -> <|"gamma" -> {γ_1, …, γ_g}, "coeffs" -> {c_1, …, c_g}, "firstKindResidual" -> …|>|>]`.

---

## S.7 Pipeline wiring

**Goal.** Assemble S.1–S.6 into a drop-in alternative to the Phase 2–6 section of `src/IntegrateTrager.m`, selected by `"Schultz" -> True`.

**Work item.**

- `src/SchultzPipeline.m` — `schultzPipeline[validated, reduced, basis, diagnostics, opts]` implementing:

```
basis ← extend buildIntegralBasis output with δ_i (S.1)
divdx ← divisorOfDx[basis]                                    (S.4)
Dls   ← computeDlDivisors[basis, divdx]                        (S.4)
integrand ← rationalizeToEtaBasis[validated.R, basis, y]
herm  ← schultzHermiteReduce[integrand, basis, y]              (S.3)
if herm.infinityResidual != 0:
    applyFailInStyle[herm, basis]                              (S.6.2)
residues ← schultzResidueDivisors[herm.remainder, basis, Dls]  (S.5)
logs    ← schultzConstructLogTerms[residues, basis, y]         (S.6.1)
result  ← reassemble[herm.algPart, logs, basis, validated.scale, reduced.yScale]
```

- `src/IntegrateTrager.m` — in the main `Module`, after the genus check (line 312) and basis build (line 320), add:

```mathematica
If[OptionValue["Schultz"],
  schultzPipeline[validated, reduced, basis, diagnostics, opts],
  (* existing Phase 2–6 sequence *)
];
```

The existing code path is not reordered — the Schultz path is a full replacement for lines 323–494 when the flag is set, and delegates to the same `reassemble` in `src/Reassemble.m`.

- `src/IntegrateTrager.m:Options` — add `"Schultz" -> False` to the list (line 54).

**Acceptance.** All existing test suites pass unchanged. A new `tests/TestSchultzPipeline.m` runs every Tier 1 test (`TragerPlan.md` §9) with `"Schultz" -> True` and cross-checks the result against the default pipeline (either exact equality after simplification or derivative-match via the `"Verify"` hook).

---

## S.8 Out of scope

Explicitly deferred for this plan, with justifications:

- **Function algebras (Sch §7).** Needed only for integrands that introduce zero divisors, e.g. `1/(x + √(x^2))`. For a simple radical `y^n = g(x)` with `g` non-constant and reduced, `y^n − g` is irreducible over `ℚ(params)(x)` so `ℚ(params)(x, y)` is a field. Composita of multiple radicals (currently deferred in `TragerPlan.md` §10) would require this machinery before they can be attempted.
- **Sch §5 third-kind integrals over transcendental extensions.** The paper is explicit that a fully-never-fail algorithm requires differentials of the third kind defined over an algebraic-closure-extended coefficient field; this plan implements §5 only for first-and-second-kind splitting and accepts "may fail in style" as the operational guarantee.

---

## S.9 Implementation order and test gates

| Phase | Modules touched | Gated by |
|---|---|---|
| S.1 | `src/Basis.m`, `tests/TestBasis.m` | Basis key `"deltas"` populated; sum rule holds |
| S.2 | `src/SchultzDivisor.m`, `tests/TestSchultzDivisor.m` | Divisor round-trip + Sch §6.2 matrices |
| S.3 | `src/SchultzHermite.m`, `tests/TestSchultzHermite.m` | Agreement with `hermiteReduce` on finite-only inputs; no-Möbius on `√(x^2+2x)` |
| S.4 | `src/SchultzPlaces.m`, `tests/TestSchultzPlaces.m` | Sch Example 6.1 `D_l` matrices reproduced |
| S.5 | `src/SchultzResidues.m`, `tests/TestSchultzResidues.m` | All residue tests pass; Sch §6.2 residues match |
| S.6 | `src/SchultzLogTerms.m`, `src/SchultzFailStyle.m`, tests | Tier 1 logs match Trager; Sch §6.3 non-elementary certificate produced |
| S.7 | `src/SchultzPipeline.m`, `src/IntegrateTrager.m` option wiring | All existing tests green; new Tier 1 Schultz pass |

Every phase ships with its own test file and must be green before the next starts. The Schultz path is a parallel track, never a replacement, until S.7 — so trunk pipeline reliability is unaffected during the port.
