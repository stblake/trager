# Project: Trager's Algorithm in Mathematica

## Scope

Indefinite integration of `R(x, y) dx` where `R` is rational in `(x, y)` and `y^n = g(x)` with `g ∈ ℚ(params)[x]`, `n ≥ 2`. Covers **all genera** (0 and positive); the original "genus 0 only" target was extended early on once Phase 5 came online. Free symbols other than `x`, `y` are auto-detected as transcendental parameters (override via `"Parameters" -> {…}`).

The implementation follows Trager's 1984 MIT thesis (`papers/Trager 1984 - Integration of algebraic functions.pdf`); a parallel Schultz 2015 pipeline lives behind `"Schultz" -> True`.

## Reference docs

- `TragerPlan.md` — the implementation plan; phase-by-phase spec, conventions, and §10 the positive-genus extension.
- `SchultzPlan.md` — the Schultz 2015 alternative pipeline (S.1–S.9), gated by `"Schultz" -> True`.
- `trager_status.md` — technical status: file layout, per-phase notes, known limitations.
- `README.md` — user-facing overview, examples, public surface.
- `papers/` — Trager 1984 (primary), Miller 2012, Kauers 2008 (`papers/kauers.m`), Schultz 2015, Bronstein.

Read the relevant Trager 1984 chapter before editing a phase. Source comments cite the chapter/section; new code must too.

## Conventions

- **Never `FullSimplify`.** Banned project-wide — slow, non-terminating on algebraic inputs, opaque. Use `Simplify`, `Together`, `Cancel`, `RootReduce`, or `zeroQ` instead.
- **Modular code, extensive comments.** One module per phase or pipeline component. Comments describe the underlying mathematics (with chapter/section citations to Trager 1984). Do **not** annotate code with references to third-party implementations (Kauers' file, Maple's `algrisch`, etc.).
- **Unit tests for every function.** `tests/Test<Module>.m` per source module; `tests/RunAll.m` runs the lot, exits non-zero on failure. Currently ~30 suites, ≈900 assertions.
- **String option names.** All `IntegrateTrager` options are strings (`"Verbose"`, `"Simplify"`, `"LogTermsMethod"`, …) to avoid colliding with `System`Verbose` / `System`Simplify`.
- **Verification is opt-in, except inside `"Auto"`.** Step 10 differentiates the antiderivative and compares; `"Verify" -> True` enables it on a single-method run, `"Auto"` always uses it to compare engines.
- **Partial results, not opaque failures.** When an engine integrates only part of the input, return `integrated + IntegrateTrager[residual, x, opts]` with the residual call held unevaluated.
- **Run tests with the full Mathematica path:** `/Applications/Mathematica.app/Contents/MacOS/wolframscript -file tests/RunAll.m`.

## Current state (2026-04-27)

- **Public surface:** `IntegrateTrager` (one symbol). Two-arg surface form `IntegrateTrager[f, x]` auto-detects radicals.
- **Pipeline:** Phases 0–6 (validate → reduce → genus → basis → shift → Hermite → residues → log terms → reassemble → verify).
- **Log-term engines** (selected by `"LogTermsMethod" -> "Auto" | "Trager" | "Miller" | "Kauers"`):
  - `"Trager"` — Ch 5–6 divisor / K[z]-HNF / `findPrincipalGenerator` / `torsionIfCan`.
  - `"Miller"` — Miller 2012 Gröbner-basis refinement, with Kauers iterated-squaring fallback per factor.
  - `"Kauers"` — direct port of Kauers 2008 (`papers/kauers.m`), heuristic.
  - `"Auto"` (default) cascades Trager → Miller → Kauers with per-method `TimeConstrained` budgets, returning the first verified result.
- **Schultz parallel pipeline** (`"Schultz" -> True`): per `SchultzPlan.md`. S.1–S.5 implemented (`SchultzDivisor.m`, `SchultzHermite.m`, `SchultzPlaces.m`, `SchultzResidueDivisor.m`, `SchultzResidues.m`, `SchultzLogTerms.m`, `SchultzPipeline.m`). S.6.2 ("failing in style", `SchultzFailStyle.m`) is stubbed: emits structured `NonElementary` without the `γ_j` certificate.
- **Parametric base fields** (transcendental parameters in `g` or the integrand) are supported across the pipeline. Algebraic parameters at *input time* are deferred (see below).
- **Tier 1 / 2 / 4 end-to-end cases pass** via differentiation. Tier 1b elliptic / hyperelliptic non-elementary baselines (`1/√(x³+1)`, `1/√(x⁴+1)`, `1/√(x⁵−x)`) correctly return `Failure["NonElementary", …]`. Pure-algebraic positive-genus inputs integrate.
- **Test suite:** ≈900 assertions, currently **1 failure** in `TestMillerKauersLogTerms.m` (partial-result shape on a Kauers-fallback case). Don't ship green-washing fixes — investigate and fix the underlying issue.

## Outstanding gaps

### Algorithmic

- **Torsion orders > 1, end-to-end.** `torsionIfCan` searches `k ≤ MaxTorsionOrder = 12` (Mazur's bound) and the framework is in place, but no Tier 1 log case lands at order > 1 — the `v` construction for `k > 1` is exercised by genus-positive elementary inputs but not under unit-test coverage. Genus > 0 elementary cases with non-trivial torsion currently surface as `NonElementary` via the verifier.
- **Higher-degree `y`-polynomial remainders.** Tier-1 log cases use only `c_0 + c_1 y` forms; for `n ≥ 3` only pure-algebraic remainders are tested.
- **Schultz §S.6.2 fail-in-style certificate.** Lemma 5.5 construction (`complementaryInfinityBasis`, `secondKindNormalForms`) is stubbed; non-elementary inputs under `"Schultz" -> True` get a structured failure without the `{γ_j, c_j}` data.
- **Schultz §S.4 D₁ refinement.** `SchultzPlaces.m` sets the finite ideal of `D_1` to trivial in some configurations (deferred Lemma 4.6 work).
- **Schultz divisor inversion for general `n`.** `schultzDivisorInverse` covers `n ≥ 3` per a recent commit; check before relying on it for `n = 2` corner cases.

### Performance

- **Complex Galois-orbit residues in multi-dim number fields** (e.g. `1/((x³−1)·y)` on `y³ = x³+2`, residue field `ℚ(ω, 3^(1/3))`). `PolynomialExtendedGCD` over `ℚ(α)[z]` with `α` a symbolic algebraic power blows up because Mathematica doesn't canonicalise `(-1)^(1/3)` as a finite-dim ℚ-vector. Mathematically correct, practically slow (100+ s per pEGCD). Remedy: canonicalise to `AlgebraicNumber[gen, vec]` before HNF. Deferred optimisation.
- **HNF arithmetic over `ℚ(params)`** needs `Cancel[Together[…]]` after every Bezout step to avoid `(a−1)^k(a+1)^k`-style blow-up — implemented in `canonicalizePolyEntry` / `exactQuotient`. The Schultz path uses a variable-aware `schultzCanon[expr, x]` that preserves polynomial-in-x structure in radical form (do not collapse `Sqrt`+`I` sums into `Root[…]` form — see `SchultzDivisor.m` header).

### Deferred by design (`TragerPlan.md` §9)

- **Radical compositums** (multiple distinct radicals in one integrand) — Trager Appendix A; currently rejected with `NotSimpleRadical`.
- **`ℚ(α)` algebraic base field at input time** — needs `Factor[…, Extension -> α]` threaded through Phases 0, 3, 4. Distinct from the `ℚ(α)` extension that arises *internally* from Phase-4 residues, which §10 already handles.
- **Transcendental tower extensions** (exp/log of algebraic expressions) — Risch on a tower of differential-field extensions; separate algorithm.
- **General algebraic extensions** `K(x)[y]/(F(x, y))` beyond simple radicals — needs Round-2 / van Hoeij integral basis, structure-tensor AF arithmetic, Puiseux place arithmetic. See `README.md` "Extending beyond simple radical extensions".
