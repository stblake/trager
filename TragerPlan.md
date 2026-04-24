# Trager's Algorithm for Simple Radical Extensions — Mathematica Plan

**Scope.** Indefinite integration of `R(x, y) dx` where `y^n = g(x)`, `g ∈ ℚ[x]`, genus-zero case. Returns an elementary antiderivative or an out-of-scope diagnostic.

**Key fact.** Every genus-0 integrand has an elementary antiderivative. Failure to produce one means a bug or unhandled input class — never genuine non-elementarity.

**Reference.** Trager, *Integration of Algebraic Functions* (MIT 1984): Ch 2 §5 (integral basis), Ch 4 §2 (Hermite), Ch 5 §§2–4 (residues, divisors), Ch 6 §1 (principal generator).

---

## 0. Conventions

**AF element:** `<| "Type" -> "AF", "Coeffs" -> {c0,…,c[n-1]}, "n" -> n, "g" -> g[x] |>` with basis `w[i] = y^i / d[i][x]`.

**Divisor** (locally principal, Ch 5 §3): `<| "Type" -> "Divisor", "h" -> AF, "A" -> poly |>` with `order(h) = order(D)` at places over roots of `A`, zero elsewhere.

**Errors.** Return `Failure[tag, <|…|>]`. User-facing: `"BadInput"`, `"NotSimpleRadical"`, `"DegenerateRadical"`, `"UnsupportedBaseField"`, `"PositiveGenus"`. Internal: `"InfinityShiftFailed"` (retried), `"InternalInconsistency"` (bug). No `"NonElementary"` — genus-0 always elementary.

**Diagnostics** (via `Verbose` / `Diagnostics`): `autoreduce`, `scale`, `extension`, `hermite`, `genus`.

---

## 1. Top-level: `TragerIntegrate[integrand, {x, y, y^n == g[x]}]`

Options (all option names are strings): `"Verbose" -> False`, `"Diagnostics" -> False`, `"Simplify" -> True`, `"ShiftBound" -> 32`, `"MaxGenus" -> Infinity`, `"LogTermsMethod" -> "Trager"`. Pipeline: (1) `validateInput` → canonical `(R, x, y, n, g)` + phase-0 scaling; (2) `reduceIrreducibility` → auto-reduced `(n, g)`; (3) `computeGenus` — gate on `g_curve == 0`; (4) `buildIntegralBasis` → `B`; (5) `shiftAwayFromInfinity` → integrand in `z` + inversion record `τ`; (6) `hermiteReduce` → `{algPart, simpleRemainder, D}`; (7) `computeResidues` → `R(Z)`, ℚ-basis, extension `K'`; (8) `constructLogTerms` → `{c[j], v[j]}`; (9) `reassemble` — apply `τ^{-1}` + scalings, simplify. `"InfinityShiftFailed"` retried with doubled bound; `"InternalInconsistency"` short-circuits.

---

## 2. Phase 0 — Validation

**`validateInput[integrand, x, y, relation]`.** Check `y^n == g[x]` shape, `n ≥ 2`, `g ∈ ℚ(x)`. Clear denominators: if `g = p/q`, set `y_new = q·y`, `g_new = q^(n-1)·p`; record `{"q" -> q, "exponent" -> n-1}`. Check integrand rational in `(x,y)`. Reduce `y`-degree mod `n`. Errors as above; `"DegenerateRadical"` if `g` becomes constant.

**`reduceIrreducibility[n, g]`.** Square-free factor `g = c·∏ p[i]^e[i]`. Absorb `p[i]^(n·floor(e[i]/n))` into `y`; reduce `e[i] < n`. Let `d = gcd(n, e[1], …, e[k])`. If `d > 1`, take principal factor: `n' = n/d`, `g' = c^(1/d)·∏ p[i]^(e[i]/d)`. If `c^(1/d) ∉ ℚ`, emit `"UnsupportedBaseField"` with reduced form. Emit `autoreduce`.

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

**Deferred:** positive genus (torsion-bound extension); radical compositums; `ℚ(α)` base field (needs `Factor[…, Extension -> α]` threaded through); transcendental extensions (Trager Appendix A); surface-syntax wrapper (`Sqrt`/`CubeRoot` auto-detection); integrand rescale on `reduceIrreducibility` when `yScale ≠ 1`.
