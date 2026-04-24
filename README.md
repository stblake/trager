# trager

A Mathematica implementation of Trager's algorithm for indefinite integration of algebraic functions on **simple radical extensions**. Given an integrand `R(x, y)` rational in `(x, y)` and a curve `y^n = g(x)` with `g ∈ ℚ[x]`, `n ≥ 2`, `IntegrateTrager` returns an elementary antiderivative or a structured `Failure[...]` object explaining why the input is out of scope.

The implementation follows Trager's 1984 MIT Ph.D. thesis, *Integration of Algebraic Functions*. Chapter/section references in source comments point back to that thesis.

---

## Quick start

```mathematica
Get["/path/to/trager/src/Trager.m"]
```

### Surface syntax: `IntegrateTrager[f, x]`

The two-argument form walks the integrand, detects a radical pattern `f^(k/n)`, synthesises `y` and `y^n == f`, and substitutes `y -> f^(1/n)` on the way out.

```mathematica
IntegrateTrager[1/Sqrt[x^2 + 1], x]
(* ==> Log[x + Sqrt[1 + x^2]] *)

IntegrateTrager[x/Sqrt[x^2 + 1], x]
(* ==> Sqrt[1 + x^2] *)

IntegrateTrager[1/(x Sqrt[x^2 + 1]), x]
(* ==> -Log[(1 + Sqrt[1 + x^2])/x] *)

IntegrateTrager[1/x^(1/3), x]
(* ==> (3/2) x^(2/3) *)
```

### Explicit curve: `IntegrateTrager[f, {x, y, y^n == g}]`

Use this form when `y` is implicit in the integrand or when you want direct control over `(n, g)`:

```mathematica
IntegrateTrager[1/y, {x, y, y^2 == x^2 + 1}]
(* ==> Log[x + y] *)

IntegrateTrager[y/(x^2 + 1), {x, y, y^2 == x^2 - 4 x - 1}]
(* elementary; residues lie in Q(Sqrt[1 + 2 I]), verified numerically *)

IntegrateTrager[1/Sqrt[x^3 + 1], x]
(* ==> Failure["NonElementary", ...]   (* genus 1, incomplete elliptic *) *)
```

### Options

All option names are strings (deliberately — avoids colliding with `System`Verbose` and `System`Simplify`):

- `"LogTermsMethod" -> "Trager" | "Miller" | "Kauers"` — pick the Phase 5 engine.
- `"MaxGenus" -> Infinity` — permissive by default; set to `0` to refuse positive-genus input up front.
- `"ShiftBound" -> 32` — search radius for the Möbius shift `x = a + 1/z`.
- `"Diagnostics" -> True` — return `<|"Result" -> ..., "Diagnostics" -> <|...|>|>` with per-phase intermediate state.
- `"Verbose"`, `"Simplify"` — diagnostic messages and final `RootReduce` pass.

---

## Mathematical overview

The pipeline is the standard Trager decomposition, Phases 0 through 6. Each phase is gated by a `Catch/Throw` `guard` that short-circuits on `Failure` without unwinding intermediate state.

### Phase 0 — Validation and canonicalisation (`Validate.m`, `Reduce.m`, `Genus.m`)

1. **Shape checks.** `y^n == g` with integer `n ≥ 2`; `g` rational in `ℚ(x)`; integrand rational in `(x, y)` over `ℚ`.
2. **Denominator clearing.** If `g = p/q`, substitute `y_new = q·y` so `y_new^n = q^(n-1)·p ∈ ℚ[x]`; the scale record is stored for Phase 6 reversal.
3. **Absolute irreducibility (Trager Ch 3 §3).** Factor `g = c·∏ p_j^{e_j}`, reduce exponents `mod n` (absorbing multiples of `n` into `y`), then extract the principal factor along `d = gcd(n, e_1, …, e_k)`. If `c^(1/d) ∉ ℚ`, raise `UnsupportedBaseField` with the reduced form as a suggestion.
4. **Genus (Trager Ch 2 §4, Riemann–Hurwitz on a Kummer cover):**
   ```
   2g − 2 = −2n + Σ_j m_j · (n − gcd(n, e_j)) + (n − gcd(n, deg g))
   ```
   Gated by `"MaxGenus"`.

### Phase 1 — Integral basis and AF arithmetic (`Basis.m`, `Arithmetic.m`)

Trager's **simple-radical integral basis** (Ch 2 §5):
```
w_i = y^i / d_i    where   d_i = ∏_j p_j^⌊i·e_j / n⌋,   i = 0, …, n-1
```
This basis is normal at infinity and has the divisibility property `d_i · d_j | d_{i+j}` (for `i+j < n`) and `d_i · d_j | g · d_{i+j−n}` (otherwise), which lets `afTimes` be implemented directly in the basis without round-tripping through `y`-polynomial form.

The other primitives exploit the diagonal structure:
- `afD`: `w_i' = (i·g'/(ng) − d_i'/d_i)·w_i` — no cross-terms between basis elements.
- `afNorm`, `afTrace`: `Det` / `Tr` of the multiplication matrix.
- `afInverse`: `LinearSolve[M, e_0]`; `K(x)[y]/(y^n − g)` is a field for irreducible `y^n − g`.

Invariants verified by tests: `y · y^(n-1) = g`, Leibniz, norm multiplicativity.

### Phase 2 — Remove poles at infinity (`Shift.m`)

Möbius substitution `x = a + 1/z` with the **critical `⌈m/n⌉` scaling**: let `k = ⌈m/n⌉` where `m = deg g`, set `y_new = y·z^k`. Then
```
y_new^n = z^(kn) · g(a + 1/z) = z^(kn−m) · G(z)
```
where `G(z) = z^m·g(a + 1/z) ∈ ℚ[z]` and `kn − m ∈ {0, …, n-1}`. `⌊m/n⌋` would give a rational-function radicand and break the pipeline; this was a subtle early bug.

A sanity check compares pre- and post-shift genus; a mismatch raises `InternalInconsistency`.

### Phase 3 — Hermite reduction (`Hermite.m`)

Classical algebraic Hermite (Ch 4 §2): square-free-factor the common denominator `D = ∏ D_j^j`, then for each multiplicity `j ≥ 2` solve
```
A_i ≡ U · B_i · (V·s_i − k·V')   (mod V)   for i = 0, …, n-1
```
where `V = D_j`, `U = D/V^j`, `k = j-1`, and `s_i = i·g'/(ng) − d_i'/d_i` is the diagonal of the derivation matrix. The `V·s_i` term is the **ramification correction** the pipeline missed in an earlier draft: when `V | g` (ramified divisor), the simplification `T·Σ ≡ 0 (mod V)` from the plan is wrong; hand-tracing `1/(x^2 y^2)` on `y^3 = x` revealed the correct coupled form.

Each `B_i` is solved via `PolynomialExtendedGCD` on the numerator of `C_i = U·(V·s_i − k·V')` against `V`.

### Phase 4 — Rothstein–Trager residues (`Residues.m`)

Factor-by-factor double resultant:
```
R_i(Z) = Res_x(Res_y(Z·B'_full − G_poly, y^n − g, y), p_i^{e_i})
R(Z)   = ∏_i R_i(Z)
```
with `B_full = B·d_{n-1}` and `G_poly = remainder·B·d_{n-1}` to clear basis denominators. The `d_{n-1}` scaling introduces zero-residue branch places — stripped as a trailing `Z^k` factor (Ch 5 §4).

A ℚ-basis of the residue span is computed via `ToNumberField` + `RowReduce`, then rescaled so residue coordinates are **integer** against a possibly-rescaled basis (keeps divisor arithmetic in Phase 5 small).

### Phase 5 — Log part (`Divisor.m`, `Normalize.m`, `PrincipalGen.m`, `Torsion.m`, `TragerLogTerms.m`)

Three interchangeable engines, selected by `"LogTermsMethod"`:

- **`"Trager"` (default).** Pure algebraic construction per Ch 5–6. For each ℚ-basis element `Zbasis[i]` of the residue span, build the degree-zero divisor `D_i = Σ_j basisCoeffs[j, i] · Q_j` (integer linear combination of per-residue divisors `Q_j`), search for the smallest `N` making `N·D_i` principal (`torsionIfCan`, default `MaxOrder = 12`, Mazur's bound), and emit `Zbasis[i]/N · log(gen_i)`.
  - Divisors are locally-principal `<|"h" -> AF, "A" -> UP|>` pairs (Ch 5 §3).
  - `findPrincipalGenerator` runs K[z]-HNF (polynomial Hermite form over `K[z]` via `PolynomialExtendedGCD`) then `normalizeAtInfinity` (iterative row-combination that kills ℚ-linear dependencies of leading-at-infinity coefficients, Ch 2 §3), then scans for a row every entry of which is integral at infinity.
  - The D2/D3 split in `residueDivisor` (Ch 5 §§3–4) separates non-branch (D2) and branch (D3) components; the branch part is raised to the `n`-th power before `reduceH` to correct for ramification.
- **`"Miller"`.** Miller 2012's Gröbner-basis refinement. Primary-decomposes `J_i = Id(F, v, u − z·v', r_i(z))` with block elimination `[x,y] > z`; the "removal condition + multiplicity search" (Miller §4.1.6) fixes a silent-wrong-multiplicity bug in the raw Kauers heuristic.
- **`"Kauers"`.** Direct port of Kauers 2008 (`papers/kauers.m`). Heuristic, faster on large inputs, but may fail silently on some `R_z` factors.

Conjugate log pairs produced by real inputs with complex-conjugate residues are folded to `ArcTan` form in Phase 6 (`LogToArcTan.m`) using `a·Log[A+iB] + ā·Log[A-iB] = 2 Im[a]·ArcTan[A/B]` (`Re[a] = 0` branch) or its dual.

### Phase 6 — Reassembly (`Reassemble.m`)

Apply the Phase 2 inverse (`z → 1/(x−a)`, scale `y_new → y·yScaleTotal(1/(x−a))`), the Phase 0 rescale inverse (`y → q·y` when a denominator was cleared), the Phase 0 reduce inverse (`y → y^d · (scaled radical)` when the gcd reduction fired), and optionally `RootReduce`.

### Verification (step 10 of `IntegrateTrager`)

The pipeline always verifies its own output. Differentiate the proposed antiderivative in the reduced frame, substitute `y → g^(1/n)`, subtract the integrand, and test `Simplify[diff] === 0`. On `Simplify` failure (common with nested algebraic numbers like `Sqrt[Sqrt[1 + 2I]]`), fall back to high-precision numerical sampling at 6 random rationals with 60-digit working precision.

- Mismatch on genus 0 → `Failure["ImplementationIncomplete", Subreason -> "Phase5PrincipalGenerator", ...]` (a genus-0 integrand is always elementary, so mismatch is a bug).
- Mismatch on genus ≥ 1 → `Failure["NonElementary", ...]`.
- Kauers method is a heuristic: on mismatch it returns the **partial** result
  ```
  attempted + IntegrateTrager[residual, x, opts]
  ```
  with the residual `IntegrateTrager` call left unevaluated (via `HoldForm`) so the caller can inspect it, differentiate it, or retry with a different method.

---

## Source tree

```
src/
  Trager.m                   package loader; only public symbol is IntegrateTrager
  Common.m                   Failure helpers, type predicates, diagnostic messages
  Validate.m                 Phase 0: validateInput + reduceYDegree
  Reduce.m                   Phase 0: reduceIrreducibility (Ch 3 §3)
  Genus.m                    Phase 0: computeGenus (Riemann–Hurwitz)
  Basis.m                    Phase 1: Trager integral basis
  Arithmetic.m               Phase 1: AF element operations on the basis
  Shift.m                    Phase 2: shiftAwayFromInfinity (Ch 4 §3)
  Hermite.m                  Phase 3: hermiteReduce (Ch 4 §2)
  Residues.m                 Phase 4: Rothstein–Trager + Z-basis (Ch 5 §2)
  Normalize.m                Ch 2 §3: K[z]-HNF, normalizeAtInfinity
  Divisor.m                  Ch 5 §3: divisor data type + arithmetic
  PlaceOrder.m               Ch 5 §§1,4: place / branch valuations
  PrincipalGen.m             Ch 6 §1: findPrincipalGenerator
  Torsion.m                  Ch 6 §3: torsionIfCan
  TragerLogTerms.m           Phase 5 via divisors (Trager, default)
  IdealDecomposition.m       zero-dim primary decomposition (Miller support)
  MillerKauersLogTerms.m     Phase 5 via Miller 2012
  KauersLogTerms.m           Phase 5 via Kauers 2008 (heuristic)
  LogToArcTan.m              Phase 6: complex-log pair -> ArcTan
  Reassemble.m               Phase 6: Möbius + scale inversions
  IntegrateTrager.m          top-level pipeline + verifier
  Surface.m                  IntegrateTrager[f, x] auto-detects radicals

tests/
  TestHarness.m              tassert / tassertEqual / tassertFailure / tSummary
  Test<Module>.m             per-module unit tests (~16 suites)
  RunAll.m                   suite runner; exit 1 on first failure
```

---

## Design decisions

- **Public surface is one symbol.** `IntegrateTrager` is the only name leaked out of ``Trager` ``; everything else is in the `Private` context.
- **No `FullSimplify`, anywhere.** `FullSimplify` is banned project-wide; it's slow, non-terminating on some algebraic inputs, and obscures which transformations a result depends on. Verification uses `Simplify` + `zeroQ` then numerical sampling at high precision.
- **String option names.** Avoids collision with `System`Verbose` and `System`Simplify`, and keeps the option surface uniform.
- **Hermite before shift.** If the integrand is already regular at infinity, Phase 2 is skipped — running it anyway introduces a spurious `z` factor in both basis `d_{n-1}` and the Hermite denominator, driving the Rothstein–Trager resultant to identically zero. The pipeline builds an AF representation, tests regularity at infinity with `afFormRegularAtInfinity`, and shifts only when necessary.
- **Integer Z-basis.** Residue coordinates are rescaled to integers against a scaled basis so divisor arithmetic (especially K[z]-HNF) works over a small coefficient ring. A Galois orbit `{r_1, r_2, r_3}` satisfying `r_1 + r_2 + r_3 = 0` yields `basisCoeffs = {{1,0},{0,1},{-1,-1}}` instead of power-basis coordinates with hundreds-range numerators.
- **Three log engines, one verifier.** `"Trager"`, `"Miller"`, `"Kauers"` are drop-in replacements downstream of the Z-basis residue data. All three go through the unconditional step-10 differentiation check, so a wrong answer from any engine becomes an explicit Failure or a partial result — never a silently accepted bogus antiderivative.
- **Partial results, not opaque failures.** When the Kauers heuristic only integrates part of the input, the return value is `integrated + IntegrateTrager[residual, x, opts]` with the residual call held unevaluated. This mirrors Mathematica's own convention for unresolved `Integrate[...]` expressions and preserves composability.
- **AF element is the lingua franca.** Every phase operates on `<|"Type" -> "AF", "Coeffs" -> {c_0, …, c_{n-1}}, "n" -> n, "g" -> g|>`. Arithmetic stays in the integral basis (never round-tripping through `y^(n-1) + … + c_0` form), which is both faster and avoids reintroducing basis denominators.

---

## Status and missing features

Current state (see `trager_status.md` for the full breakdown):

- **309 assertions across 16 suites, 0 failures.** Runs via `wolframscript -file tests/RunAll.m`.
- **Tier-1 end-to-end cases all pass** and are verified by differentiation: `1/Sqrt[x²±1]`, `1/Sqrt[1−x²]`, `1/(x·Sqrt[x²+1])`, `1/(x·y)`, `y/(x²−2)`, `1/y` on `y^n = x^k` for `n ∈ {3,4,6}`, plus all rescale paths (`y^4 = (x²+1)²`, `1/y` on `y² = x²(x²+1)`, etc.).
- **Genus > 0 non-elementary cases** (`1/Sqrt[x³+1]`, `1/Sqrt[x⁴+1]`, `1/Sqrt[x⁵−x]`) correctly return `Failure["NonElementary", ...]`. Pure-algebraic integrands on positive-genus curves (`x²/Sqrt[x³+1]`, `x³/Sqrt[x⁴+1]`) integrate correctly.
- **All failure tags are exercised:** `BadInput`, `NotSimpleRadical`, `DegenerateRadical`, `UnsupportedBaseField`, `PositiveGenus`, `NonElementary`, `ImplementationIncomplete`.

### Known limitations

- **Complex Galois-orbit residues in a multi-dimensional number field** (e.g. `1/((x³−1)·y)` on `y³ = x³+2`, residue field `ℚ(ω, 3^(1/3))`) exercise `PolynomialExtendedGCD` over `ℚ(α)[z]` with `α` a symbolic algebraic power. Mathematica doesn't canonicalise `(-1)^(1/3)` as a finite-dimensional ℚ-vector, so Bezout coefficients blow up and individual pEGCD calls can take 100+ seconds. Mathematically correct, practically slow. Remedy: canonicalise divisor `h`-coefficients to `AlgebraicNumber[gen, vec]` form before HNF. **Deferred optimisation**, not an algorithmic gap.
- **Torsion orders > 1** are implemented but untested end-to-end — no tier-1 log case lands at torsion order > 1, so the search bound `MaxOrder = 12` is exercised but the `v` construction for `k > 1` is not. Genus > 0 elementary inputs with non-trivial torsion currently surface as `NonElementary` via the step-10 verifier.
- **Higher-degree `y`-polynomial remainders** (tier-1 only uses `c_0 + c_1 y` forms; `n ≥ 3` tier-1 cases are pure-algebraic).

### Deferred (by design, per `TragerPlan.md` §9)

- **Positive-genus elementary integrands** beyond pure-algebraic and torsion-order-1 — needs the full torsion-bound extension machinery.
- **Radical compositums** (multiple distinct radicals in one integrand) — Trager's thesis Appendix A. Currently rejected with `NotSimpleRadical`.
- **`ℚ(α)` base fields** — needs `Factor[…, Extension -> α]` threaded through Phases 0, 3, 4.
- **Transcendental tower extensions** (exp, log of algebraic expressions) — Trager Appendix A.

---

## Extending beyond simple radical extensions

The full Trager algorithm handles arbitrary algebraic extensions `K(x)[y] / (F(x, y))` with `F` irreducible in `y` over `ℚ(x)`. This implementation fixes `F(x, y) = y^n − g(x)` and that shape is load-bearing in every phase except Phase 4. The rest of this section is a phase-by-phase account of what would need to be added or replaced.

### Integral basis (`Basis.m`)

The Trager basis `w_i = y^i / d_i` with `d_i = ∏_j p_j^⌊i·e_j / n⌋` is a closed form because `y^n − g` has discriminant `±n^n · g^(n-1)` and purely Kummer ramification. For general `F`:

1. Compute `disc_y(F) ∈ ℚ[x]` and square-free factor it — these are the ramified primes.
2. At each ramified prime, build a local maximal order via Round-2 / van Hoeij 1994 / Böhm, or Trager Ch 3 §§2–3 directly.
3. Glue the local orders into a global integral basis by CRT.
4. Emit the structure tensor `c_{i,j,k} ∈ ℚ[x]` with `w_i · w_j = Σ_k c_{i,j,k} · w_k`.

The resulting basis is no longer diagonal under multiplication, which cascades through Phase 1 arithmetic and Phase 3 Hermite.

### AF arithmetic (`Arithmetic.m`)

- `afTimes` currently uses `w_i · w_j = (g^q · d_{(i+j) mod n})/(d_i · d_j) · w_{(i+j) mod n}` — a single basis element with a rational-function multiplier. The general case is the full sum `Σ_k c_{i,j,k} · w_k` against the structure tensor from the new integral basis.
- `afD` uses `w_i' = (i · g'/(n · g) − d_i'/d_i) · w_i` — diagonal. General derivation: differentiate `F(x, y) = 0` to get `y' = −F_x / F_y`, differentiate each `w_i` in its `(x, y)`-polynomial representation, reduce modulo `F` and the basis relations. The result is a full matrix `D_{i,j}` with `w_i' = Σ_j D_{i,j} · w_j`.
- `afNorm`, `afTrace`, `afInverse` port unchanged — they work on whatever multiplication matrix exists.

### Genus (`Genus.m`)

The current formula is Riemann–Hurwitz applied to a Kummer cover, in closed form. General curves need Puiseux expansions at each singularity (affine and at infinity) to read off branch indices, then adjunction: for a plane curve of bidegree `(n, m)`, `g = (n-1)(m-1)/2 − δ` with `δ` summed from local delta-invariants at the singular places.

### Infinity shift (`Shift.m`)

The `k = ⌈deg g / n⌉` scaling and single `y_new = y · z^k` correction assume a single-place, Kummer-ramified structure at infinity. For general `F`, infinity may split into several places with different ramification indices; the correct rescale is per-place and driven by Puiseux expansions at `x = ∞`, not a single `z^k`. The `a`-search loop is unaffected; the post-shift normalisation is not.

### Hermite reduction (`Hermite.m`)

The plan's general congruence is
```
A[i] ≡ −k · U · V' · B[i] + T · Σ_l B[l] · M[l, i]   (mod V)
```
with `M[k, i]` the derivation matrix (`E · w_k' = Σ_i M[k, i] · w_i`). For a simple radical, `M` is diagonal, the `Σ` collapses to `B[i] · M[i, i]`, and the per-component solve in the current `Hermite.m` works. For general `F`, the system is coupled across `i`: a linear solve in `(B[0], …, B[n-1])` over `ℚ[x] / (V)`. The underlying machinery (`PolynomialExtendedGCD` over residue rings) is already present; only the solver wrapper changes.

### Residues (`Residues.m`) — ports unchanged

`Resultant[Resultant[Z · B'_full − G_poly, y^n − g, y], p_i, x]` becomes `Resultant[Resultant[Z · B'_full − G_poly, F, y], p_i, x]`. The `B_full = B · d_{n-1}` denominator clearing becomes "multiply by the lcm of basis denominators for the new integral basis". The Z-basis / residue-span extraction is independent of the curve shape.

### Place arithmetic (`PlaceOrder.m`, `Divisor.m`)

`PlaceOrder.m` computes `ord_P(h)` using the Kummer branch structure (non-branch places: uniformizer `x − α`; branch places: the `n`-th root local uniformizer when `g(α) = 0`). The general case: Puiseux-expand `F` around each root `(α, β)` of `F(α, y) = 0`, read the branch index off the Newton polygon, and compute `ord_P` from the Puiseux coefficients of `h`. The `D2/D3` split in `residueDivisor` is generic; the "raise D3 to the n-th power" branch correction becomes per-place `e_P`.

### Normalization at infinity (`Normalize.m`, `PrincipalGen.m`)

`scaledInfOrder` hardcodes `infOrder(c · w_j) = n · deg(c) + j · deg(g) − n · deg(d_j)` — derived from the simple-radical basis. Generally, the per-column adjustment comes from the Puiseux expansions at `x = ∞`, not from `d_j`. The K[z]-HNF and null-vector machinery in `normalizeAtInfinity` are unchanged.

### Log-part construction (`TragerLogTerms.m`, `MillerKauersLogTerms.m`, `KauersLogTerms.m`)

- **Trager engine.** The multiplicity formula `k = ord_α(g(x) − g(α))` and the support-place contribution `(y − y_α) / (x − α)^(k-1)` bake in the simple-radical local structure. The general form uses the Puiseux uniformizer at `(α, y_α)` and the local expansion of `F` there.
- **Miller engine.** `Id(F, v, u − z · v', r_i(z))` already takes `F` as a parameter; the port is largely mechanical once the integral basis is generalised.
- **Kauers engine.** Heuristic; specific to the simple radical structure in its current form.

### Orthogonal missing pieces

Not specific to the "simple radical" restriction, but required for a production implementation:

- **Radical compositums** (multiple distinct radicals in one integrand). Reduce to a single extension via primitive-element construction before entering the pipeline. Trager Appendix A.
- **`ℚ(α)` base field.** Needs `Factor[…, Extension -> α]`, algebraic-coefficient `PolynomialExtendedGCD`, and `AlgebraicNumber` canonicalisation threaded through Phases 0, 3, 4. The complex Galois-orbit slowdown noted under "Known limitations" is a symptom of missing canonicalisation at this layer.
- **Transcendental tower** (`exp`, `log` of algebraic expressions). Separate algorithm on top; full Risch on a tower of differential-field extensions.

### Effort sketch (cheapest → most involved)

1. `Residues.m`, the HNF in `Normalize.m`, divisor arithmetic in `Divisor.m` — port in place.
2. General AF arithmetic via a structure tensor — mechanical once the integral basis is available.
3. General Hermite solver — small, local change once the derivation matrix is exposed.
4. General integral basis — new module, large (van Hoeij 1994 or Trager Ch 3).
5. Puiseux-series place arithmetic — new module, large; feeds 6, 7, 8.
6. Genus, infinity shift, log-part engine generalisations — sit on top of (4) and (5).

---

## Running the tests

```
cd /path/to/trager
wolframscript -file tests/RunAll.m         # exits 0 on all-pass, 1 on failure
wolframscript -file tests/TestHermite.m    # or run one suite at a time
```

Each suite prints a summary of assertions run and failed. `RunAll.m` re-runs every suite in a fresh Mathematica process to isolate any state leakage.

---

## References

- Trager, *Integration of Algebraic Functions*, MIT Ph.D. thesis (1984). Primary reference; chapters 2, 4, 5, 6 drive the implementation.
- Trager, *Integration in simple radical extensions* (1979). Short precursor paper.
- Miller, *On the Integration of Elementary Functions: Computing the Logarithmic Part* (2012). Implements the `"Miller"` method.
- Kauers, `kauers.m` (2008). Implements the `"Kauers"` method.
- Bronstein, *Symbolic Integration I: Transcendental Functions*. Reference for the Hermite-step congruence machinery.
- Schultz, *Integration on Curves* (2015). Modern exposition of the divisor-theoretic picture.

PDFs and source references are checked into `papers/`.

---

## License

See `LICENSE`.
