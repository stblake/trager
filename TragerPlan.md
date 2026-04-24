# Trager's Algorithm for Simple Radical Extensions — Mathematica Plan

**Scope.** Indefinite integration of `R(x, y) dx` where `y^n = g(x)`, `g ∈ ℚ(p_1,…,p_k)[x]`, for all genera (0 and positive). Returns an elementary antiderivative, a Liouville non-elementarity certificate, or an out-of-scope diagnostic. The base field defaults to `ℚ`; if the integrand or relation contains free symbols other than `x` and `y` they are treated as transcendental parameters (auto-detected, or declared via `"Parameters" -> {…}`). Antiderivatives in parametric mode are valid on a Zariski-open subset of parameter values.

**Genus-zero fact.** Every genus-0 integrand has an elementary antiderivative; failure to produce one means a bug or unhandled input class, never genuine non-elementarity.

**Genus-positive fact.** On a curve of genus `g ≥ 1` an `R(x, y) dx` has an elementary antiderivative iff every degree-zero divisor `D_i` in the residue decomposition represents a torsion class in the Jacobian (Trager Ch 6 §3, Risch–Trager). The algorithm certifies elementarity by *exhibiting* a principal generator of `N·D_i` for some `N ≤` a computable torsion bound; absence of one inside the bound is the `NonElementary` verdict.

**Reference.** Trager, *Integration of Algebraic Functions* (MIT 1984): Ch 2 §5 (integral basis), Ch 4 §2 (Hermite), Ch 5 §§2–4 (residues, divisors), Ch 6 §1 (principal generator), Ch 6 §§2–3 (good reduction + torsion). Secondary: Bronstein, *Symbolic Integration I* Ch 2; Miller, *Integration of Algebraic Functions* (UBC PhD, 2012); Kauers, unpublished 2008 Mathematica implementation (`papers/kauers.m`).

---

## 0. Conventions

**AF element:** `<| "Type" -> "AF", "Coeffs" -> {c0,…,c[n-1]}, "n" -> n, "g" -> g[x] |>` with basis `w[i] = y^i / d[i][x]`.

**Divisor** (locally principal, Ch 5 §3): `<| "Type" -> "Divisor", "h" -> AF, "A" -> poly |>` with `order(h) = order(D)` at places over roots of `A`, zero elsewhere.

**Errors.** Return `Failure[tag, <|…|>]`. User-facing: `"BadInput"`, `"NotSimpleRadical"`, `"DegenerateRadical"`, `"UnsupportedBaseField"`, `"PositiveGenus"` (only when genus exceeds `"MaxGenus"`), `"NonElementary"` (genus ≥ 1, torsion bound exhausted without a principal generator). Internal: `"InfinityShiftFailed"` (retried), `"InternalInconsistency"` (bug).

**Diagnostics** (via `Verbose` / `Diagnostics`): `autoreduce`, `scale`, `extension`, `hermite`, `genus`.

---

## 1. Top-level: `TragerIntegrate[integrand, {x, y, y^n == g[x]}]`

Options (all option names are strings): `"Verbose" -> False`, `"Diagnostics" -> False`, `"Simplify" -> True`, `"Verify" -> False` (opt-in derivative-vs-integrand check; `True` inside `"Auto"` cascade so it can compare methods), `"ShiftBound" -> 32`, `"MaxGenus" -> Infinity` (positive genera are *in scope* — `MaxGenus` caps the attempt, not the algorithm), `"MaxTorsionOrder" -> 12` (bound on `N` in the principal-generator search for `N·D_i`; Mazur's theorem gives 12 for elliptic curves over ℚ, raise for higher genus), `"LogTermsMethod" -> "Auto"`, `"Parameters" -> Automatic`. Pipeline: (1) resolve `"Parameters"` (auto-detect free symbols ∉ {x, y} when `Automatic`); set `$tragerParameters` via `Block` so all field-aware predicates (`baseFieldElementQ`, `zeroQ`, `detectExtensionGenerators`) consult it; (2) `validateInput` → canonical `(R, x, y, n, g)` + phase-0 scaling; (3) `reduceIrreducibility` → auto-reduced `(n, g)`; (4) `computeGenus` — report genus, gate on `MaxGenus`; (5) `buildIntegralBasis` → `B`; (6) `shiftAwayFromInfinity` → integrand in `z` + inversion record `τ`; (7) `hermiteReduce` → `{algPart, simpleRemainder, D}`; (8) `computeResidues` → `R(Z)`, ℚ(params)-basis, extension `K'`; (9) `constructLogTerms` → `{c[j], v[j]}` via torsion search of bound `MaxTorsionOrder`; (10) `reassemble` — apply `τ^{-1}` + scalings, simplify; (10′) optional `Verify` check (differentiate + compare). `"InfinityShiftFailed"` retried with doubled bound; `"InternalInconsistency"` short-circuits.

---

## 2. Phase 0 — Validation

**`validateInput[integrand, x, y, relation]`.** Check `y^n == g[x]` shape, `n ≥ 2`, `g ∈ ℚ(x)`. Clear denominators: if `g = p/q`, set `y_new = q·y`, `g_new = q^(n-1)·p`; record `{"q" -> q, "exponent" -> n-1}`. Check integrand rational in `(x,y)`. Reduce `y`-degree mod `n`. Errors as above; `"DegenerateRadical"` if `g` becomes constant.

**`reduceIrreducibility[n, g]`.** Square-free factor `g = c·∏ p[i]^e[i]`. Absorb `p[i]^(n·floor(e[i]/n))` into `y`; reduce `e[i] < n`. Let `d = gcd(n, e[1], …, e[k])`. If `d > 1`, take principal factor: `n' = n/d`, `g' = c^(1/d)·∏ p[i]^(e[i]/d)`. If `c^(1/d) ∉ ℚ`, emit `"UnsupportedBaseField"` with reduced form — UNLESS `c` contains a parameter, in which case decline the reduction and keep `(n, g)` as-is (adjoining `c^(1/d)` would push us out of `ℚ(params)`; correctness is unaffected, efficiency degrades by at most `d`). Emit `autoreduce`.

**`computeGenus[n, g]`.** For `g = ∏ p[i]^e[i]`, `deg p[i] = m[i]`, `0 < e[i] < n`:
```
g_curve = 1 + (1/2)·( Σ_i m[i]·(n − gcd(n, e[i])) + (n − gcd(n, deg g)) − 2n )
```

---

## 3. Phase 1 — Integral basis & AF arithmetic

**`buildIntegralBasis[n, g]`.** Returns `<| "n", "g", "d" -> {d[0],…,d[n-1]}, "pFactors" |>` with `d[i] = ∏ p[j]^floor(i·e[j]/n)`, `w[i] = y^i / d[i]`. `d[n-1] = lcm(d[i])`. Basis is normal at infinity (Ch 2 §5).

**Primitives.** `afMake`, `afFromStandard` (`c[i] = d[i]·Coefficient[expr, y, i]`), `afToStandard`; `afPlus`/`afMinus` coefficient-wise via `Together`; `afTimes` via `afToStandard`→multiply→reduce `y^n → g`→`afFromStandard` (direct: `w[i]·w[j] = (d[i+j]/(d[i]·d[j]))·w[i+j]` if `i+j < n`, else `(g·d[i+j-n]/(d[i]·d[j]))·w[i+j-n]`); `afD` uses `w[i]' = w[i]·(i·g'/(n·g) − d[i]'/d[i])`; `afNorm`/`afTrace` = `Det`/`Tr` of multiplication matrix.

---

## 4. Phase 2 — Remove poles at infinity

`shiftAwayFromInfinity[integrand, x, y, n, g]`: (1) pick `a ∈ ℚ` not a root of integrand's denominator or `g`; try `{0, ±1, …, ±32}`, then grow. (2) `m = deg g`, `G(z) = z^m·g(a + 1/z) ∈ ℚ[z]`. (3) `k = ceil(m/n)`, `y_new = y·z^k`; then `y_new^n = G(z)·z^(kn−m) =: gNew(z)`. **Always `ceil`** — `floor` gives rational-function radicand. (4) `reduceIrreducibility[n, gNew]`. (5) Transform integrand `x → a+1/z`, `y → y_new/z^k`, `dx → −dz/z^2`; reduce mod new relation; rebuild basis. (6) `computeGenus[n, gNew]` must be 0 (else `"InternalInconsistency"`). Errors: `"InfinityShiftFailed"` (retried), `"InternalInconsistency"`.

---

## 5. Phase 3 — Hermite reduction

`hermiteReduce[integrand, z, y, n, g, basis]`: (1) write integrand as `Σ A[i]·w[i] / D[z]` with common `D ∈ ℚ[z]`; (2) square-free `D = ∏ D[j]^j`; (3) `E = n·g·d[n-1]` (common denominator of `{afD[w[i]]}`); (4) for `j` from max-multiplicity down to 2 let `V = D[j]`, `U = D/V^j`, `k = j − 1`, `T = U·V/E`, matrix `M[k,i]` with `E·w[k]' = Σ M[k,i]·w[i]`, solve Ch 4 §2 eqn (11) for `B[i] ∈ ℚ[z]`, `deg B[i] < deg V`:
```
A[i] ≡ −k·U·V'·B[i] + T·Σ B[l]·M[l,i]   (mod V)   for i = 0,…,n-1
```
subtract `afD[Σ B[i]·w[i] / V^k, z]` into `algPart`; (5) remainder has square-free denominator; (6) **invariant:** `algPart` has no pole at `z = 0` (each AF coefficient in lowest terms has `z ∤ den`); violation → `"InternalInconsistency"` `"PoleAtInfinityAfterHermite"`.

---

## 6. Phase 4 — Residues via Rothstein–Trager

### `computeResidues[remainder, D, x, y, n, g]`
1. Get `Gtilde[x,y]` via `afToStandard`.
2. For each ℚ-factor `D_i` of square-free `D`:
   ```
   R_i(Z) = Resultant[Resultant[Z·D'[x] − Gtilde[x,y], y^n − g[x], y], D_i[x], x]
   ```
   `R(Z) = ∏ R_i(Z)`. Factor-by-factor is ~10× faster than single-resultant.
3. Strip `Z^k` factor (branch places contribute zero residue in simple radicals, Ch 5 §4).
4. `Factor` reduced `R[Z]` over ℚ; distinct roots = residues.
5. ℚ-basis of residue span via `ToNumberField[…, GenerateConditions -> False]` + `RowReduce`; express each residue as integer combination of basis.

---

## 7. Phase 5 — Log part construction

### 7.1 Support-place construction (primary algorithm)

For each residue `r`:
1. Factor `D(x) = c·∏ p_j(x)` (square-free). For each irreducible `p_j`:
   a. Let `α` be a root of `p_j` (generator of `ℚ(α)`).
   b. Solve for `y_α` from `Gtilde(α, y_α)/D'(α) = r` and `y_α^n = g(α)`: substitute into `poly(y) = Gtilde(α, y) − r·D'(α)` over `ℚ(r, α)`.
   c. Check on-curve: `y_α^n =?= g(α)`; else skip (zero-residue place).
   d. Multiplicity `k = ord_α(g(x) − g(α))` — smallest `k` with `g^{(k)}(α) ≠ 0`.
   e. Contribution: `(y − y_α) / (x − α)^(k−1)`. (Local analysis: at non-branch `(α, y_α)`, uniformizer is `x−α`; `y − y_α = (g^{(k)}(α)/(n·y_α^{n-1}·k!))·t^k + O(t^{k+1})`.)
2. Take norm over Galois conjugates of `α` when `deg p_j > 1`.
3. Emit `{r, v_r}`.

Branch places (`y_α = 0` ⟺ `g(α) = 0`) skipped — zero residue. Multiple `y_α` for a single `(r, α)`: sum contributions.

### 7.2 Principal generator (K[z]-HNF + infinity normalization)

Fallback via Trager Ch 6 §1 — two-step reduction. Let `I_D` be the `K[z]`-module generated by `{A·w_i, h·w_i}`; `M` is the `2n × n` coordinate matrix in `{w_i}`.

**Step A — K[z]-HNF.**
1. Per column `j`: `L[j] = lcm(denominators)`; scale `M[:,j] *= L[j]`.
2. Polynomial HNF over `K[z]` (upper triangular, reduced; row factors in `K[z]`, NOT `K(z)`) via polynomial extended-GCD.
3. Take top `n × n` block.
4. Per column: `M[:,j] /= L[j]`.

When the base field is `ℚ(params)` (i.e. `$tragerParameters` non-empty) every intermediate entry must pass through `Cancel[Together[…]]` after each Bezout combination — without it, accumulated `(a − 1)^k(a + 1)^k` style factors blow expression size up exponentially within ~5 elimination steps. This is implemented in `canonicalizePolyEntry` and `exactQuotient`.

**Step B — `normalizeAtInfinity`.** Loop:
1. For each column `j`:
   - `k[j] = min_i infOrder(M[i,j]·basisAdjustment[j])`.
   - `N[i,j] = infValue(M[i,j]·z^{-k[j]}·basisAdjustment[j])` — leading coeff at infinity. `N` is `ℚ`-valued.
2. If `det(N) ≠ 0`, done.
3. Find `ℚ`-null-vector `c` of `N`. Let `i0` = index of nonzero `c[i]` with minimum `k[i0]`.
4. `M[:, i0] := Σ_{i: c[i]≠0} c[i]·z^(k[i]−k[i0])·M[:, i]` (all exponents ≥ 0).
5. Recompute and loop. Terminates: `Σ_j k[j]` strictly increases and is bounded.

**Step C — Scan.** Return row where every entry is integral at infinity: `c_j·w_j` integral iff `n·deg(c_j) + j·deg(g) − n·deg(d_j) ≤ 0`. No such row → `"InternalInconsistency"` (genus 0) or signal for torsion retry (genus ≥ 1).

### `constructLogTerms[residues, remainderAF, Dpoly, basis, y]`
Returns `{{c_j, v_j}, …}`.

---

## 8. Phase 6 — Reassembly

`reassemble[algPart, logTerms, phase0Scale, phase2Inverse, x]`: `afToStandard` on `algPart` and each `v[j]`; phase-2 reversal `z → 1/(x−a)`, `y_new → y_shifted·(x−a)^k`; phase-0 reversal `y_shifted → q·y_user` if denominator was cleared; assemble `algPart + Σ c[j]·Log[v[j]]`; `RootReduce` (skipped when `Simplify -> False`).

---

## 9. Tests & implementation order

Tiers: (1) smoke — `1/√(x²+1)`, `x/√(x²+1)`, `1/√(x²−1)`, `1/(x·√(x²+1))`, `1/√(1−x²)`, `1/x^(1/3)`, `1/x^(2/3)`, `1/x^(3/4)`, `y^4 == (x²+1)²` auto-reduce. (2) Gradshteyn–Ryzhik §2.25–2.26, §2.2 for `n = 2,3,4`. (3) Bronstein *Symbolic Integration I* Ch 2. (4) failures: `1/√(x³+1)` (`PositiveGenus`), `y²==4` (`DegenerateRadical`), `y==x+1` (`NotSimpleRadical`), irrational coeffs (`UnsupportedBaseField`), non-rational integrand (`BadInput`). (5) invariants fire `InternalInconsistency` on broken intermediate state. Cross-check: `Together[D[result,x]−integrand] /. y^n -> g → 0`.

Order: Phase 0+1 primitives → Phase 2 shift with round-trip test → Phase 3 Hermite with stubbed 4/5 → Phase 4 residues → Phase 5 support-place (§7.1), fall back to K[z]-HNF (§7.2) → Phase 6 + options → tiers 2–5.

**Deferred:** radical compositums; `ℚ(α)` algebraic base field at *input time* (adjoining a user-specified algebraic to the coefficient ring — distinct from the `ℚ(α)` extension that arises *internally* at Phase-4 residues, which §10 handles); integrand rescale on `reduceIrreducibility` when `yScale ≠ 1`.

---

## 10. Positive-genus extension

On a curve of genus `g ≥ 1`, Hermite reduction leaves a logarithmic remainder whose residue divisors `D_i` are no longer automatically principal. Liouville + Risch–Trager: `∫ R dx` is elementary iff each `D_i` is a **torsion class** in the Jacobian `Pic⁰(C)`. The algorithm's job is to certify torsion (by exhibiting a principal generator `v_i` with `(v_i) = N·D_i` for some `N ≤ MaxTorsionOrder`), or emit `NonElementary`.

Everything before Phase 5 is genus-agnostic and requires no change; Phases 0–4 already run on arbitrary-genus curves. Phases 5–6 need three upgrades.

### 10.1 Residue ground-field arithmetic (blocker for the running `x/((x³+8)√(x³−1))` example)

**Problem.** When `R(Z)` factors over ℚ as a product of irreducible polynomials of degree `≥ 2`, the residues are algebraic numbers in `ℚ(α)` for `α` a root of an irreducible factor. On genus-0 curves this rarely occurs (residues are typically rational); on genus `≥ 1` it is generic. `residueDivisor` and all downstream divisor arithmetic then work over `ℚ(α)[x]`, not `ℚ[x]`.

**Fix (surgical, already applied in `src/Divisor.m`).** Every `PolynomialGCD` in `simplifyHDenominator`, `reduceH`, `residueDivisor` takes `Extension -> Automatic`; without this the gcd over ℚ misses shared factors that only appear once ℚ is extended by the residue, and the divisor silently collapses to the trivial one (`h = 1, A = Dpoly`).

**Remaining.** `findPrincipalGenerator` and `normalizeAtInfinity` invoke polynomial HNF and null-space computations on matrices whose entries live in `ℚ(α)(z)`. Two options, in order of preference:

- **(A) Thread the residue field through.** Detect `α` (already done by `detectExtensionGenerators` in `PrincipalGen.m:111`) and pass it to every `PolynomialGCD` / `Factor` call inside the HNF. Implementation touches: `src/PrincipalGen.m:hermiteNormalFormOverKz`, `src/Normalize.m:normalizeAtInfinity`, `src/PlaceOrder.m:enumeratePlacesOverA` (factoring `A` over `ℚ(α)` may split it further). Preserves Trager's original structure; verification via `integerCombinationVerifier` already handles the place-order bookkeeping correctly.

- **(B) Reformulate Phase 5 as RootSum over ℚ-irreducible factors** (Kauers / Miller approach). Never expand residues as explicit algebraic numbers. Each irreducible `R_i(Z) | R(Z)` contributes `RootSum[R_i, γ ↦ γ · Log[v(x, y, γ)] &]` where `v(x, y, Z)` is the principal generator expressed as a polynomial in `Z` (the formal residue). Implementation follows `papers/kauers.m:561` (`LogarithmicPart`) closely; the "principal power" iterated-squaring loop (`PrincipalPower` there, `kauersPrincipalPower` in `src/KauersLogTerms.m`) is the torsion search.

  Recommendation: **(B) as default, (A) as fallback**. (B) avoids algebraic-number blow-up and matches the reference's ~0.6 s runtime on the elliptic-radical test cases; (A) preserves the clean divisor-class separation for debugging / pedagogy.

### 10.2 Torsion search inside `torsionIfCan`

**Present state.** `src/Torsion.m` already implements the loop `N = 1, 2, …, MaxOrder` with `N·D` built via iterated `divisorAdd`. At each step it calls `findPrincipalGenerator[N·D]` with the `integerCombinationVerifier`; a `True` verdict certifies that `(v) = N·D` and we emit `(1/N) · log(v)` per Z-basis direction.

**Gaps to close for the general positive-genus pipeline:**

1. **Torsion bound.** Mazur (1977) caps torsion at 12 for elliptic curves over ℚ. For `g ≥ 2` a computable bound exists via reduction mod primes of good reduction (Trager Ch 6 §2): `#J(F_p) = ∏ L_p(1)` for the local `L`-factors, and `N · D ≡ 0` in `Pic⁰(C/ℚ)` implies the same in `Pic⁰(C/F_p)` for good `p`. Pick two good primes, compute `#J(F_p)`, take `gcd`. Bound = `gcd( #J(F_p₁), #J(F_p₂) )`. Implementation note: only needed when the integrand has a "hard" residue basis — for most practical elliptic cases the torsion order is `≤ 6` and `MaxTorsionOrder -> 12` is fine.

2. **Efficient `divisorAdd`.** Current `divisorAdd` multiplies the A-polynomials and the h-AF-elements. After `k` iterations `A = A_original^k`, and the K[z]-HNF on a power of A is expensive. Replace with: canonical form representative per divisor class (unique reduced representative modulo principal divisors on the Jacobian), computed once per `N·D` via a single HNF rather than iterated multiplication. Trager Ch 6 §3 Algorithm 6.1 describes this reduction.

3. **Search order.** Try the cheap cases first: `N ∈ {1, 2, 3, 4, 6, 8, 12}` (the possible elliptic torsion orders per Mazur) in that order before linearly scanning; saves work on the common case where the divisor is in fact principal or 2-torsion.

### 10.3 Place enumeration over the residue field

**Present state.** `enumeratePlacesOverA` in `src/PlaceOrder.m` factors `A(x)` into ℚ-irreducible pieces, then for each piece `(β, y_β)` computes places on the curve. For genus `≥ 1` with algebraic residues, `A` often *further splits* once we enlarge to `ℚ(α)`; e.g. the running elliptic example has `A = x² − 2x + 4` which is irreducible over ℚ but factors over `ℚ((-1)^(1/3))` as `(x − 2(-1)^(1/3))(x − 2 − 2(-1)^(1/3))`.

**Fix.** Before iterating, factor `A` over `ℚ(α)`. This makes `integerCombinationVerifier` distinguish the two halves of the residue pair instead of treating them as one ramified place.

### 10.4 Pipeline integration

1. **Phase 4 output shape (no change).** Already emits a residue list and per-residue `(multiplicity, Q-basis, basisCoeffs)` — same shape whether residues are rational or algebraic. The only downstream change is that `residueQBasis` (already implemented in `src/Residues.m`) picks basis elements from the algebraic span.

2. **Phase 5 dispatch.** The `"Trager"` method continues to use the divisor + K[z]-HNF path with the §10.1 fixes. The `"Kauers"` / `"Miller"` methods already implement the RootSum approach (§10.1 option B) internally; for positive-genus inputs they are the path of least resistance. `"Auto"` cascades as today (Trager → Miller → Kauers) but with `Verify -> True` forced so it can actually compare correctness.

3. **Phase 6 (`reassemble`).** No structural change. Keep `RootReduce` gated behind `"Simplify" -> True` — it is the main source of algebraic-number simplification cost on positive-genus outputs.

### 10.5 Test additions

Tier 1b (elliptic smoke tests): `1/√(x³+1)` (`NonElementary` — 2-torsion divisor NOT principal), `x/√(x³−1)` (elementary, `-√(x³−1)/x` actually — test the rational part alone), `x/((x³+8)√(x³−1))` (the running example; torsion order 3 for the `(2+x)` piece, order 6 for the quadratic piece). Tier 2b (genus 2): `1/√(x⁵+1)` and cousins. Cross-check each against numerical integration at random rationals.

### 10.6 Work order

1. Verify the `src/Divisor.m:Extension -> Automatic` fix against `tests/TestDivisor.m` + add regression tests for algebraic-residue divisors (a 4-residue elliptic case is sufficient). *(divisor tests pass today — 2026-04-24)*
2. Implement §10.1 option (B): port `papers/kauers.m:LogarithmicPart` into `src/KauersLogTerms.m` in a form that accepts the Phase-4 output directly and returns the standard `{{c_j, v_j}, …}` shape. Prototype validated by the running example in ~0.6 s vs 119 s today.
3. Generalise `src/Normalize.m` and `src/PrincipalGen.m` to accept a `Extension -> α` parameter (§10.1 option A); use it when the `"LogTermsMethod" -> "Trager"` path is requested explicitly.
4. Extend `torsionIfCan` with the reduction-mod-p bound (§10.2 item 1) — needed for `g ≥ 2`; for elliptic curves the fixed 12 bound is adequate.
5. Add the Tier 1b + 2b tests (§10.5); iterate on §10.2 items 2–3 if any of them time out.
