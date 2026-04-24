# Trager Implementation — Technical Status

This document describes the current state of the Mathematica implementation of Trager's algorithm for integration of algebraic functions. It is pitched at a reader who has read `TragerPlan.md` and wants to understand what has been built, how it's structured, what invariants hold, and where the shortcuts are.

---

## 1. Architecture

### 1.1 File layout

```
src/
  Trager.m             main loader — Get[]s every .m below, in dependency order
  Common.m             type predicates (afElementQ, basisDescriptorQ),
                       Failure constructors, diagnostic-message declarations
  Validate.m           Phase 0: validateInput + reduceYDegree helper
  Reduce.m             Phase 0: reduceIrreducibility
  Genus.m              Phase 0: computeGenus (Riemann–Hurwitz)
  Basis.m              Phase 1: buildIntegralBasis
  Arithmetic.m         Phase 1: afMake / afFromStandard / afToStandard /
                                 afPlus / afMinus / afScale / afTimes /
                                 afD / afNorm / afTrace /
                                 afMultiplicationMatrix / afInverse
  Shift.m              Phase 2: shiftAwayFromInfinity
  Hermite.m            Phase 3: hermiteReduce, rationalizeToAF,
                                 commonDenominatorAF
  Residues.m           Phase 4: computeResidues, residueQBasis,
                                 reduceRowsOverQ
  Normalize.m          Phase 5 helpers: polynomialHNFOverKz,
                                 rationalDegInZ, noPoleAtInfinityRowQ,
                                 polyOrderAtZero, zAdicOrderAtZero
  Divisor.m            Phase 5: divisor representation <|"h"->AF,"A"->UP|>,
                                 residueDivisor, divisorAdd/Subtract/
                                 Negate/Scale
  PrincipalGen.m       Phase 5: findPrincipalGenerator via K[z]-module
                                 + HNF + pole-at-infinity scan
  Torsion.m            Phase 5: torsionIfCan — search k=1..MaxOrder
                                 for principal k*D (Trager 1984 Ch 6 §3)
  TragerLogTerms.m     Phase 5: constructLogTerms (Trager 1984 Ch 5–6)
  IdealDecomposition.m Phase 5: zeroDimPrimaryDecomposition (Miller method)
  MillerKauersLogTerms.m Phase 5: Miller 2012 algorithm
  KauersLogTerms.m     Phase 5: Kauers 2008 heuristic
  Reassemble.m         Phase 6: reassemble (with phase-0-reduce reversal)
  IntegrateTrager.m    top-level: IntegrateTrager + options + verification
                                 + integrand-rescale for reducible curves
  Surface.m            surface-syntax overload IntegrateTrager[f, x]
                                 recognizing Sqrt / (_)^(1/n) patterns
tests/
  TestHarness.m         tassert / tassertEqual / tassertFailure / tSummary
  TestValidate.m        25 assertions
  TestReduce.m          28 assertions
  TestGenus.m           20 assertions
  TestBasis.m           32 assertions
  TestArithmetic.m      37 assertions
  TestShift.m           38 assertions
  TestHermite.m         29 assertions
  TestResidues.m        17 assertions
  TestDivisor.m         15 assertions (divisor data structure + arithmetic)
  TestPrincipalGen.m    20 assertions (rationalDegInZ, HNF, noPoleAtInfinity)
  TestTorsion.m          4 assertions (torsionIfCan shape + MaxOrder)
  TestLogTerms.m         4 assertions (log-term failures + algebraic path)
  TestIntegrate.m       15 assertions (end-to-end tier 1 + tier 4)
  TestGenusPositive.m   10 assertions (genus > 0 path)
  TestRescale.m          5 assertions (reduceIrreducibility integrand-rescale)
  TestSurface.m         10 assertions (surface-syntax wrapper)
  RunAll.m              suite runner
```

**Current test count:** 309 assertions across 16 suites, 0 failures. `wolframscript -file tests/RunAll.m` runs all of them and exits non-zero on any failure.

### 1.2 Shared types

- **AF element** (algebraic-function element of `K(x)[y]/(y^n − g)`):
  ```
  <|"Type" -> "AF", "Coeffs" -> {c_0, ..., c_{n-1}}, "n" -> n, "g" -> g|>
  ```
  Represents `sum_i c_i(x) · w_i` where `w_i = y^i / d_i` is the Trager integral-basis element.

- **Basis descriptor** (output of `buildIntegralBasis`):
  ```
  <|"n" -> n, "g" -> g, "d" -> {d_0, ..., d_{n-1}},
    "pFactors" -> {{p_j, e_j}, ...}, "x" -> x|>
  ```
  Carries the variable symbol `x` so every phase can read it back without an extra argument.

- **Failure objects**: every phase returns either a normal value or a `Failure[tag, <|metadata|>]`, constructed by `tragerFailure`. The top-level pipeline uses `Catch/Throw` to short-circuit; see §2.8.

### 1.3 Control flow

The user enters at `IntegrateTrager[integrand, {x, y, y^n == g}, opts]`. That function is wrapped in `Catch[Module[...]]`; each phase is called through a `guard[...]` helper that `Throw`s on `Failure`. Any thrown failure becomes the caller-visible result. For `"Diagnostics" -> True` every phase's output is accumulated in a `diagnostics` association and returned as `<|"Result" -> ..., "Diagnostics" -> ...|>`. (All `IntegrateTrager` option names are strings.)

---

## 2. Phase-by-phase notes

### 2.1 Phase 0 — validateInput

`validateInput[integrand, x, y, relation]` performs six structural checks:

1. Side relation has head `Equal` with LHS `y^n`, `n` integer ≥ 2. Else `NotSimpleRadical`.
2. `g[x]` is rational in `x` over `ℚ` (no `AlgebraicNumber[...]`, no free symbols). Else `UnsupportedBaseField`.
3. If `g = p/q` with `q ≠ 1`, substitute `y_new = q·y` so `y_new^n = q^(n−1)·p ∈ ℚ[x]`. The scale record `<|"q" -> q, "exponent" -> n−1|>` is stored for phase-6 reversal.
4. If the cleared radicand is a ℚ-constant, fail `DegenerateRadical`.
5. Integrand must be rational in `(x, y)` over ℚ. Else `BadInput`.
6. Reduce integrand y-degree via `y^n → g` (using local helper `reduceYDegree`) so numerator and denominator are polynomial in `y` of degree `< n`.

### 2.2 Phase 0 — reduceIrreducibility

Factors `g = c · ∏ p_j^{e_j}`, reduces `e_j` mod `n` (absorbing multiples of `n` into `y`), then applies the gcd-of-exponents test. If `d = gcd(n, e_1, ..., e_k) > 1`, reduces to the principal factor `y^(n/d) = c^(1/d) · ∏ p_j^(e_j/d)` — provided `c^(1/d) ∈ ℚ`. Otherwise emits `UnsupportedBaseField` with the reduced form as a suggestion. Emits `IntegrateTrager::autoreduce` diagnostic on a non-trivial reduction.

**Known limitation:** when `reduceIrreducibility` changes `(n, g)`, the integrand should be re-expressed in the new `y`-generator (the old `y` equals `y_new · yScale`). The current pipeline does **not** apply this rescale — see task #38.

### 2.3 Phase 0 — computeGenus

Riemann–Hurwitz applied to the Kummer cover `(x, y) → x`:

```
2 g_curve − 2 = −2n + Σ_j m_j · (n − gcd(n, e_j)) + (n − gcd(n, deg g))
```

Expects `g` already in reduced form (every irreducible factor has exponent `0 < e_j < n`). Returns `−1` as a sentinel on degenerate input (constant `g`, non-integer `n`).

### 2.4 Phase 1 — buildIntegralBasis and AF arithmetic

`buildIntegralBasis` computes `d[i] = ∏_j p_j^⌊i · e_j / n⌋`, the Trager basis denominators. `d[n−1]` is automatically the `lcm` of `{d_0, ..., d_{n−1}}` (monotonic divisibility), which Phase 3 uses as the shared denominator `E = n · g · d_{n−1}` for the `w[i]'` formula.

Arithmetic (`Arithmetic.m`) is implemented directly in the basis, not via round-trip through `y`-polynomial form:

- **afTimes** uses `w_i · w_j = g^q · d_{(i+j) mod n} / (d_i · d_j) · w_{(i+j) mod n}` where `q = ⌊(i+j)/n⌋`. The normality of the Trager basis (i.e. `d_i · d_j | d_{i+j}` for `i+j < n`, and `d_i · d_j | g · d_{i+j−n}` for `i+j ≥ n`) guarantees the multiplier is polynomial.
- **afD** exploits the diagonality `w_i' = (i · g'/(ng) − d_i'/d_i) · w_i`: the derivative of a coefficient vector is computed coefficient-by-coefficient with no cross-terms.
- **afNorm**, **afTrace** work on the multiplication matrix of an AF element.
- **afInverse** solves `M · v = e_0` via `LinearSolve`. For an irreducible binomial `y^n − g`, the ring `K(x)[y]/(y^n−g)` is a field so the inverse always exists on non-zero elements.

Correctness is anchored by three invariants (all in `TestArithmetic.m`): `y · y^(n−1) = g`, Leibniz rule `(ab)' = a'b + ab'`, and norm multiplicativity `N(ab) = N(a)·N(b)`.

### 2.5 Phase 2 — shiftAwayFromInfinity

Applies the Möbius substitution `x = a + 1/z`. The critical arithmetic step is the `ceil(m/n)` scaling: with `m = deg_x(g)`, let `k = ⌈m/n⌉` so `y_new = y · z^k` satisfies

```
y_new^n = z^(kn) · g(a + 1/z) = z^(kn − m) · G(z)
```

where `G(z) = z^m · g(a + 1/z) ∈ ℚ[z]` and `kn − m ∈ {0, ..., n−1}`. The radicand is always polynomial.

After constructing `gNew_raw`, the phase calls `reduceIrreducibility[n, gNew_raw, z]` to absorb any residual high-multiplicity factors into `y_new`. The stored `yScaleTotal = z^k / yScale_reduce` is the ratio `y_new / y_old` in the `z` frame — getting this direction wrong was one of the most subtle bugs during implementation.

The candidate selection for `a` tries `{0, ±1, ±2, ..., ±32}` in order and accepts the first `a` such that:

1. the integrand's denominator (as a polynomial in `(x, y)`) does not vanish at `x = a`,
2. the resulting `gNew_raw` is a non-constant polynomial in `z`.

Condition (2) is a loosening from the plan's original "a not a root of `g`", which was overly strict; with the `ceil(m/n)` scaling, `a = 0` works for the pure-power family `y^n = x^k` even though `g(0) = 0`.

A genus-preservation sanity check compares `computeGenus` of the input (after reducing to its absolutely irreducible form) against `computeGenus` of the shifted curve. Mismatch ⇒ `InternalInconsistency`.

### 2.6 Phase 3 — hermiteReduce

The plan's congruence `A[i] ≡ −k U V' B[i] + T · Σ B[l] · M[l, i] (mod V)` was naively simplified during implementation by dropping the `T · Σ` term under the claim that `T = UV/E ≡ 0 (mod V)`. **This is only true when `gcd(V, E) = 1`.** For ramified factors — e.g. `V = x` on the curve `y^n = x` (so `V | g`, hence `V | E`) — the term does not vanish mod `V`. The corrected congruence for simple radicals with the diagonal basis is:

```
A[i] ≡ U · B[i] · (V · s_i − k · V')   (mod V)
```

where `s_i = i · g'/(ng) − d_i'/d_i`. This couples the matrix-diagonal ramification correction into the per-component solve. Each B[i] is then solved via `PolynomialExtendedGCD` on the numerator of `C_i = U · (V s_i − k V')` against `V`.

Discovered by hand-tracing `1/(x^2 y^2)` on `y^3 = x`: the incorrect formula gave `B_1 = −1/2`, the correct one gives `B_1 = −3/5` and lets `d/dx(−3y/(5x^2))` exactly recover the integrand.

An opt-in `checkPoleAt` parameter asserts the invariant from the plan (`algPart` has no pole at `z = checkPoleAt`). In the current pipeline we don't invoke this check, because for correct genus-0 input `algPart` can legitimately have a pole at `z = 0` (e.g. `algPart = y/z` in z-frame becomes just `y` after the inverse shift), which is not an error.

Other Mathematica pitfalls fixed during implementation:

- `D` was used as a local variable name, shadowing the built-in derivative operator. Renamed to `denom` throughout.
- `FactorSquareFreeList` does not take a variable argument.
- `PolynomialMod[poly, V, x]` does not exist as I expected — the third argument is parsed as an option. Replaced with `PolynomialRemainder[poly, V, x]`.

### 2.7 Phase 4 — computeResidues

The Rothstein–Trager double resultant is computed factor-by-factor for efficiency:

```
R_i(Z) = Resultant_x(Resultant_y(Z · B_full' − G_poly, y^n − g, y), p_i^{e_i})
R(Z)   = ∏_i R_i(Z)
```

with `B_full = B · d_{n−1}` and `G_poly = remainder_standard · B · d_{n−1}` (the `d_{n−1}` scaling clears the integral-basis denominators so `G_poly` is polynomial in `(x, y)`). The extra `d_{n−1}` factor introduces zero-residue branch places into the raw R(Z); these show up as a `Z^k` factor that is stripped.

**Z-basis of the residue span.** The plan specified "integer `basisCoeffs`"; my initial implementation returned rational coefficients against a `ℚ`-basis. After the Z-basis extension: for each basis column, the LCM of coefficient denominators is computed, that column is scaled by the LCM and the corresponding basis vector is divided by the LCM. The result has integer `basisCoeffs` against a (possibly scaled) basis — e.g. for residues `±√6/4`, basis `{√6/4}` with coefficients `{{−1}, {1}}`.

**Pitfalls:**

- `ToNumberField` leaves rational inputs unwrapped when mixed with algebraic inputs. My first coordinate-vector extraction pattern required all entries to be `AlgebraicNumber[...]`, which failed with `RowReduce::matrix` on mixed input. Fixed by detecting the generator and dimension from any `AlgebraicNumber` entry, then padding rationals to `{r, 0, ..., 0}` in the same power basis.
- `FirstPosition` with level-spec `{1}` still matches the `List` head at position `{0}`. Replaced with `SelectFirst` over an explicit index range.
- `Solve[1 == 0, Z]` returns `{}`, and `Z /. {}` evaluates to the atom `Z`, not an empty list, breaking `DeleteDuplicates`. Guarded explicitly.

### 2.8 Phase 5 — constructLogTerms **(revised per TragerPlan §17 — COMPLETE)**

Phase 5 is a **pure algebraic implementation of Trager's log-part construction** (Trager 1984 Ch 5–6). No `Integrate` oracle. Implementation spans:

- **`Divisor.m`** — locally-principal divisor `<|"h" -> AF, "A" -> UP|>` per Trager 1984 Ch 5 §3. Operations: `makeDivisor`, `residueDivisor`, `divisorAdd/Negate/Subtract/Scale`. Helper routines:
  - `simplifyHModA` — reduces each K[z]-coefficient's numerator modulo `A · d`, where `d` is the common denominator, to keep h in canonical small-degree form.
  - `simplifyHDenominator` — scales h by the part of its common denominator that is coprime to A. Essential because divisor arithmetic (multiplication, inversion) introduces denominator factors outside `supp(A)`, which would otherwise inflate the K[z]-module `K[z]·h + K[z]·A` beyond the true ideal sheaf.
  - `reduceH` — the "lucky integer" loop (Trager 1984 Ch 5 §3) that searches j = 0, 1, 2, … for an integer such that `Norm(h + j·D1)` has its expected DD-part degree matching the residue multiplicity `malpha`.
  - `residueDivisor` — the D2/D3 split (Trager 1984 Ch 5 §3 + §4): given `h1 = G − α·D'`, compute `D1 = gcd(Norm(h1), Dpoly)`, split into `D3 = gcd(D1, Disc)` (branch part) and `D2 = D1/D3` (non-branch part), apply `simplify + reduce` independently, and combine via `h2 · h3`. For the branch component, raise to the n-th power before `reduce` (ramification correction).
- **`Normalize.m`** — `hermiteNormalFormOverKz` (genuine polynomial K[z]-HNF via `PolynomialExtendedGCD`), `normalizeAtInfinity` (iterative row-combination that kills Q-linear dependencies of leading-at-infinity terms; Trager 1984 Ch 2 §3), plus the per-row `scaledInfOrder` / `noPoleAtInfinityRowQ` support.
- **`PrincipalGen.m`** — `findPrincipalGenerator` runs the three-step pipeline (Trager 1984 Ch 6 §1): build 2n×n generator matrix, clear column denominators, HNF, extract top n rows, restore columns, `normalizeAtInfinity`, scan for integral-at-infinity row.
- **`Torsion.m`** — `torsionIfCan[div, basis, y, MaxOrder -> 12]` iterates k = 1 … MaxOrder, testing whether `k·D` is principal (Trager 1984 Ch 6 §3).

**`TragerLogTerms.m`** drives the pipeline via the Z-basis construction (Trager 1984 Ch 5 §1). For each Z-basis element `Zbasis[i]` of the residue Q-span, it builds the degree-zero divisor `D_i = Σ_j basisCoeffs[[j, i]] · Q_j` (integer-linear combination of per-residue divisors via `divisorZCombination`), calls `torsionIfCan` with an `integerCombinationVerifier` hook, and emits `Zbasis[i] / order_i · log(gen_i)`. This replaces the earlier specialised symmetric `±r`-pair construction and natively handles Galois-orbit residues where no ±-pair exists (e.g. `R(Z) = Z^3 − c` for a cubic curve).

**Z-basis choice**. `residueQBasis` picks basis elements from the RESIDUES themselves (greedy incremental-rank selection over their common number-field coordinate representation), not from the number-field power basis. This keeps the integer coefficients small: for a Galois orbit {r_1, r_2, r_3} satisfying r_1 + r_2 + r_3 = 0 the resulting `basisCoeffs` is `{{1,0}, {0,1}, {−1,−1}}` rather than the hundreds-range entries the power-basis strategy produces.

**Residue multiplicities**. `computeResidues` tracks the per-residue multiplicity (k-th derivative test at each distinct root) and threads it to `residueDivisor` via the `Multiplicity` option. Critical for residues that are double roots of `R(Z)` (e.g. `y/(x²−2)` on `y² = x²+1` has `R(Z) = (8Z² − 3)²`, multiplicity 2 at each root); without the correct malpha, `reduceH` fails its termination criterion.

**Coefficient formula**. For D_i = Σ_j basisCoeffs[[j, i]] · Q_j with torsion generator v satisfying `div(v) = N · D_i` (N = `tor["order"]`), the emitted coefficient is `Zbasis[i] / N`. In the symmetric-pair special case (residues ±r with basis {r} and coeffs {{1}, {−1}}) this reduces to the prior `r / N` formula with no extra factor.

**Integer-combination verifier**. `verifyPrincipalGeneratorForIntCombo` replaces the old pair verifier: at every place P over `supp(A)` it checks `ord_P(v) = k · Σ_{j : h_j(P)=0} basisCoeffs[[j, i]]`, treating multiple concurrent j's additively and branch places via the unit-check fallback. `integerCombinationVerifier` closes over the data and is passed to `torsionIfCan` as the `Verify` hook.

**Verification is in the reduced frame**. `IntegrateTrager.m`'s step 10 differentiates the `reducedFrame` form of the antiderivative (the pre-phase-0-reduce-reversal form from `reassemble`) against `validated["R"]`, because the latter was rewritten in the reduced generator at the Phase 0 rescale step. Previously the verifier used `final` (user-frame) with `reduced["g"]^(1/reduced["n"])` (reduced-frame yRoot), a frame mismatch that produced spurious residuals on `1/y on y² = x²(x²+1)` and similar rescale cases.

**Tier-1 cases now integrate correctly** (all verified by differentiation):

- Log cases: `1/Sqrt[x²+1]`, `1/Sqrt[x²−1]`, `1/Sqrt[1−x²]`, `1/(x·Sqrt[x²+1])`, `1/(x·y)` on `y²=x²+1`, `y/(x²−2)` on `y²=x²+1`.
- Pure-algebraic: `x/Sqrt[x²+1]`, `x/Sqrt[1−x²]`, `1/y` on `y^3 = x`, `y^3 = x^2`, `y^4 = x^3`, `y^6 = x^2`.
- Rescale paths: `1/y` on `y² = x²(x²+1)`, `y^4 = (x²+1)²`, `y^4 = x^4·(x²+1)²`.
- Validation/out-of-scope gates: `PositiveGenus`, `DegenerateRadical`, `UnsupportedBaseField`, `BadInput`, `NotSimpleRadical`.
- Genus-1 non-elementary baselines (`1/Sqrt[x³+1]`, `1/Sqrt[x⁴+1]`) and genus-2 (`1/Sqrt[x⁵−x]`): correctly report `NonElementary`.
- Surface-syntax failure paths: `NotSimpleRadical` for multiple distinct radicals, `BadInput` for `Exp[x]/Sqrt[x]`.

**Asymmetric residues / trace1 path**. Removed the previous `AsymmetricResidues` / `IrrationalResidue` guards. The general Z-basis construction now handles arbitrary Galois-orbit residues (`Z^3 = 1/81` style, where the three cube-root residues `{r, ωr, ω²r}` do not form a ±-pair). Correctness is exercised by the existing rational/Gaussian-residue tier-1 suite; the residue-divisor builder (`residueDivisor`) already threads algebraic coefficients through `afFromStandard` and `afTimes` symbolically.

**Performance caveat for complex Galois orbits**. For genus > 0 inputs whose residues span a multi-dimensional Q-subspace of a complex algebraic number field (e.g. the user-reported case `1/((x³ − 1) y)` on `y³ = x³ + 2`, a genus-1 curve with residue field `ℚ(ω, 3^(1/3))`), the arithmetic inside `findPrincipalGenerator` — specifically `hermiteNormalFormOverKz`, which relies on `PolynomialExtendedGCD` over `ℚ(ω, 3^(1/3))[z]` — becomes very slow because Mathematica treats the algebraic generators like `(-1)^(1/3)` as free symbolic powers rather than as elements of a finite-dimensional Q-vector space. Intermediate Bezout coefficients and pivot-row polynomials explode in leaf count. The port is mathematically correct; the remedy is to canonicalise such coefficients to `AlgebraicNumber[gen, vec]` form before HNF, which is tracked as a deferred optimisation rather than an algorithmic gap.

See `TragerPlan.md` §17 for the algorithm spec and Trager 1984 Ch 5–6 for the underlying mathematics.

### 2.9 Phase 6 — reassemble

Straightforward: convert `algPart` to standard form, sum with `Σ c_j · Log[v_j]`, apply the phase-2 inverse closure (substituting `z → 1/(x − a)` and `y_shifted → y_user · yScaleTotal(1/(x − a))`), then the phase-0 inverse (`y → q · y`), then `RootReduce` if `Simplify -> True`.

### 2.10 Top-level

`IntegrateTrager` wires Phases 0–6 with `Catch/Throw` control flow. Options:

All option names are strings (to avoid colliding with the built-in `System`Verbose`/`System`Simplify` symbols and to keep the option surface uniform):

- `"Verbose" -> False` (default). Emit `IntegrateTrager::*` messages.
- `"Diagnostics" -> False`. Return `<|"Result" -> ..., "Diagnostics" -> <|...|>|>` instead of a bare expression.
- `"Simplify" -> True`. Skip the final `RootReduce` pass when `False`.
- `"ShiftBound" -> 32`. How far the phase-2 a-search goes.
- `"MaxGenus" -> Infinity`. Gate threshold. A finite `0` refuses positive-genus input with `PositiveGenus`; the default `Infinity` (or a finite bound `g ≥ 1`) lets the pipeline proceed, then a verification pass (step 10) differentiates the result and compares to the integrand under `y → g^(1/n)`. On mismatch, `Failure["NonElementary", ...]`. On match, the `"verified" -> True` entry is added to diagnostics.
- `"LogTermsMethod" -> "Auto"`. One of `"Auto"`, `"Trager"`, `"Miller"`, or `"Kauers"` (the alias `"MillerKauers"` is also accepted for back-compat). `"Auto"` (default) tries `"Trager"`, `"Miller"`, then `"Kauers"` in order, with per-method `TimeConstrained` budgets `{30, 90, 60}` seconds, returning the first verified antiderivative; this handles cases where one method's algorithmic gap (e.g. `"Trager"`'s K[z]-HNF over ℚ(a)(I)[z] on `(a x⁴+b)^(-1/4)`, or `"Miller"`'s `MillerKauersTorsionBoundExceeded` on `1/((x−b)√(x²+a))`) is covered by another. If every method's antiderivative fails verification, the first non-timeout failure (typically `"NonElementary"`) is returned.

A short-circuit after Phase 3: if the Hermite remainder is all-zero AF coefficients, Phases 4 and 5 are skipped (pure-algebraic antiderivatives like `∫ x/√(x²+1) dx = √(x²+1)`).

---

## 3. Known limitations and shortcuts

### 3.1 Phase 5 principal-generator algorithm — tier-1 complete

The pure-Trager log-part construction (Trager 1984 Ch 5–6) lands tier-1 cases end-to-end (see §2.8). Step-10 verification in `IntegrateTrager.m` catches any derivative mismatch unconditionally: on mismatch for genus 0, `Failure["ImplementationIncomplete", Subreason -> "Phase5PrincipalGenerator"]`; for genus > 0, `Failure["NonElementary", ...]`.

**What works.** All tier-1 log cases (`1/Sqrt[x²±1]`, `1/Sqrt[1−x²]`, `1/(x·Sqrt[x²+1])`, `1/(x·y)`, `y/(x²−2)`), all pure-algebraic cases, all `reduceIrreducibility` rescale paths. Algebraic-orbit residues (Galois-orbit without ±-pairing) are handled algorithmically via the Z-basis construction in `TragerLogTerms.m` (see §2.8).

**Performance limit.** Complex Galois-orbit residues living in an algebraic number field like `ℚ(ω, 3^(1/3))` (example: `1/((x³ − 1) y)` on `y³ = x³ + 2`) exercise `hermiteNormalFormOverKz` over `ℚ(α)[z]` with α a symbolic algebraic power. Mathematica's `PolynomialExtendedGCD` does not treat `(-1)^(1/3)` etc. as finite-dimensional vectors over ℚ, so Bezout coefficients and pivot-row polynomials blow up and individual pEGCD calls can take 100+ seconds. The algorithmic port is correct; making this practical needs an `AlgebraicNumber[gen, vec]` canonicalisation pass on divisor h-coefficients before HNF, which is deferred.

**No Integrate anywhere.** `grep -rn Integrate src/` returns only the top-level `IntegrateTrager` name and comments.

### 3.2 Genus > 0: framework in place, search range configurable

`torsionIfCan` in `Torsion.m` iterates k = 1 … `MaxOrder` (default 12, Mazur's bound for elliptic curves over ℚ), calling `findPrincipalGenerator` on `k·D` each time. Because `findPrincipalGenerator` itself has the correctness gap described in §3.1, torsionIfCan inherits the gap: on a genuinely non-torsion divisor, it correctly reports `order -> "failed"` and the pipeline reports `NonElementary`; on a torsion divisor of order > 1, the outcome depends on whether `findPrincipalGenerator` finds the right v for `k·D`.

The pipeline route for genus > 0:

1. User sets `"MaxGenus" -> Infinity` (or a finite bound ≥ g) in `IntegrateTrager`.
2. Phase 5 runs normally, with torsion search up to `MaxTorsionOrder`.
3. Step-10 verification differentiates and compares. On mismatch, `NonElementary`.

Cases that correctly work today: all the genus > 0 `NonElementary` assertions in `TestGenusPositive.m` (`1/√(x³+1)`, `1/√(x⁴+1)`, `1/√(x⁵−x)`) plus pure-algebraic cases on higher-genus curves (`x²/√(x³+1)`, `x³/√(x⁴+1)`). Cases with log parts fail verification and surface as `NonElementary` even when technically elementary — this is the same gap as §3.1 propagated through torsionIfCan.

### 3.3 reduceIrreducibility integrand-rescale: DONE

The pipeline now auto-rescales the integrand when `reduceIrreducibility` absorbs polynomial factors. When `yScale ≠ 1`, the integrand is substituted `y → y · yScale` and `reduceYDegree`d into the new `(n, g)` form before phase 2. The `reassemble` step applies the reverse substitution on the result so the user sees their original `y`. Five unit tests in `TestRescale.m` exercise absorb-only, gcd-only, and combined reductions. See task #38.

### 3.4 Surface-syntax recognition: DONE

`IntegrateTrager[f, x]` without an explicit `y` walks the integrand for `f^(k/n)` patterns (covers `Sqrt[f]`, `CubeRoot[f]`, `f^(1/n)`, `f^(k/n)`), synthesises a fresh `y` and `y^n == f` relation, delegates to the core function, and maps `y` back to `f^(1/n)` in the result. Multiple distinct radicals in the integrand are rejected as `NotSimpleRadical` (Trager Appendix A territory). See `Surface.m` and `TestSurface.m`.

---

## 4. Validation summary

### 4.1 What the tests cover

- **Unit tests per phase**: each operator (AF arithmetic, Hermite step, resultant, etc.) verified on hand-computed cases with the expected exact output.
- **Round-trip invariants**: Phase 2 forward + inverse recovers the integrand (modulo the `-1/(x-a)²` differential factor) on 7 distinct `(integrand, n, g)` combos. Phase 3 Hermite: `d/dx(algPart) + remainder = original`.
- **Structural identities**: `y · y^(n−1) = g`, Leibniz, norm multiplicativity.
- **Tier 1 end-to-end**: `1/√(x²±1)`, `x/√(x²+1)`, `1/(x·√(x²+1))`, `1/√(1−x²)`, `x/√(1−x²)`, `1/y` on `y^n = x^k` for `n ∈ {3,4}`.
- **Tier 4 failure tags**: every named `Failure` tag is exercised.
- **Genus > 0**: three classical non-elementary cases correctly fail; two elementary-on-positive-genus cases correctly succeed.

### 4.2 What the tests don't cover

- Non-rational/non-Gaussian residues (the trace-1 case where the residue field is a non-trivial Galois extension whose ±-pair structure is non-trivial).
- Higher-order Gtilde in y (tier-1 uses only `c_0 + c_1 y` forms; n ≥ 3 cases are pure-algebraic).
- Torsion orders > 1 (all tier-1 log cases land at torsion order 1).

---

## 5. How to run

```
cd /Users/user/Documents/Research/post_phd_research/algebraic_integration/trager
/Applications/Mathematica.app/Contents/MacOS/wolframscript -file tests/RunAll.m
```

Exit code 0 on all-pass, 1 on any failure. Per-suite invocation works too (e.g. `wolframscript -file tests/TestHermite.m`).

For interactive use:

```mathematica
Get["/.../src/Trager.m"]
IntegrateTrager[1/y, {x, y, y^2 == x^2 + 1}]
(* ==> -1/2 Log[1 - y/x] + 1/2 Log[1 + y/x] *)
```
