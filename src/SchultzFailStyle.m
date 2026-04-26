(* ::Package:: *)

(* ::Title:: *)
(* Schultz §S.6.2 -- "failing in style" decomposition (Sch §5)                *)

(* ::Text:: *)
(* See SchultzPlan.md §S.6.2 and Sch §5 (Lemmas 5.2, 5.5).                    *)
(*                                                                             *)
(* When the residue divisor has no torsion order ≤ MaxTorsionOrder, the       *)
(* integrand is non-elementary. Sch §5 prescribes that, instead of returning *)
(* a bare `NonElementary` verdict, the algorithm should produce a structured *)
(* certificate decomposing the integrand into                                   *)
(*    ω = df + c_1 γ_1 + ⋯ + c_g γ_g + (log terms) + (first-kind residual)   *)
(* where {γ_1, …, γ_g} is a k-basis of Ω_2^∞ / (Ω_ex + Ω_1) (Sch Lemma 5.5)   *)
(* (the "second-kind differentials of pole order at infinity") and the       *)
(* first-kind residual lies in Ω_1 (the holomorphic differentials of the    *)
(* first kind).                                                                *)
(*                                                                             *)
(* Construction outline (Sch Lemma 5.5, deferred details below):               *)
(*   r = max_i δ_i                                                              *)
(*   {ε_1, …, ε_n} = complementary infinity basis (Sch Lemma 4.2)              *)
(*   ρ_i  = infinity exponents of {ε_i}                                          *)
(*   S = {x^{l + ρ_i − 1} ε̄_i dx : 1 ≤ i ≤ n, 0 ≤ l ≤ r − 1}                    *)
(*   T = {d(x^l ε̄_i)            : 1 ≤ i ≤ n, 0 ≤ l ≤ r − δ_i}                 *)
(*   γ_1, …, γ_g = g representatives of S linearly independent (mod span T)    *)
(*                  over k, where g = genus.                                    *)
(*                                                                             *)
(* Status. The full Lemma 5.5 implementation requires (a) the Sch Lemma 4.2  *)
(* complementary infinity basis (currently not implemented) and (b) the      *)
(* "Lemma 5.2 linear system" to solve for the c_j coefficients. This module *)
(* exposes the public entry point `schultzFailInStyle` and a structured       *)
(* certificate format; the actual γ_j construction is left as a stub that    *)
(* emits an `ImplementationIncomplete` failure flagging the deferred work.   *)
(* Once Lemma 5.5 is implemented, only the body of `secondKindNormalForms`   *)
(* needs replacing — the certificate shape and call sites stay unchanged.    *)

(* ::Section:: *)
(* complementaryInfinityBasis (Sch Lemma 4.2) -- DEFERRED                      *)
(*                                                                             *)
(* Returns {ε_1, …, ε_n} dual to {η_1, …, η_n} with respect to the            *)
(* "trace pairing" at infinity, i.e. Tr_{K/k(x)}(η_i ε_j) ∈ k[[1/x]] with     *)
(* prescribed leading-1/x-order. Concretely, for the simple-radical normal   *)
(* basis η_i = w_{i-1} = y^{i-1}/d_{i-1}, the complementary basis is          *)
(*    ε_i = y^{n-i+1} / (n · g · d_{n-i})                                       *)
(* (modulo a global scaling). The infinity exponents ρ_i are computable in   *)
(* closed form from δ and the curve data.                                     *)
(*                                                                             *)
(* This stub returns a Missing[] descriptor; callers should treat its         *)
(* presence as a signal that Lemma 5.5 cannot proceed yet. A full            *)
(* implementation will populate this once we revisit S.6.2.                  *)

ClearAll[complementaryInfinityBasis];
complementaryInfinityBasis[basis_?basisDescriptorQ] :=
  Missing["NotImplemented", "complementaryInfinityBasis (Sch Lemma 4.2) is \
deferred; required by S.6.2 fail-in-style decomposition."];

(* ::Section:: *)
(* secondKindNormalForms (Sch Lemma 5.5) -- DEFERRED                           *)
(*                                                                             *)
(* Returns a k-basis {γ_1, …, γ_g} of Ω_2^∞ / (Ω_ex + Ω_1) where g is the     *)
(* genus. Each γ_j is represented as an AF-element-times-dx differential.     *)

ClearAll[secondKindNormalForms];
secondKindNormalForms[basis_?basisDescriptorQ] :=
  Missing["NotImplemented", "secondKindNormalForms (Sch Lemma 5.5) is \
deferred; required by S.6.2 fail-in-style decomposition."];

(* ::Section:: *)
(* schultzFailInStyle                                                          *)
(*                                                                             *)
(* Top-level entry: assemble the structured non-elementary certificate.       *)
(* Currently emits `Failure["NonElementary", ...]` with the deferred          *)
(* certificate placeholder. Once secondKindNormalForms is implemented, this   *)
(* function will compute the actual γ_j basis and the c_j coefficients via   *)
(* the Sch Lemma 5.2 linear system.                                            *)
(*                                                                             *)
(* Inputs:                                                                      *)
(*   integrandAF  - post-Hermite AF element                                    *)
(*   b            - squarefree denominator                                      *)
(*   basis        - basis descriptor                                            *)
(*   diagnostic   - association of upstream context (residue data, partial    *)
(*                  log term info, etc.) used to enrich the certificate.       *)
(*                                                                             *)
(* Output: Failure["NonElementary", ...] with keys                             *)
(*    "Certificate" -> <|                                                       *)
(*        "gamma"             -> {γ_1, ..., γ_g} or Missing[],                 *)
(*        "coeffs"            -> {c_1, ..., c_g} or Missing[],                 *)
(*        "firstKindResidual" -> ω_first or Missing[],                          *)
(*        "logTerms"          -> partial log terms (if any)                    *)
(*    |>                                                                         *)

ClearAll[schultzFailInStyle];
schultzFailInStyle[integrandAF_?afElementQ, b_,
                   basis_?basisDescriptorQ, y_Symbol,
                   diagnostic_Association: <||>] := Module[
  {gammas, coeffs, residual, certificate},
  gammas   = secondKindNormalForms[basis];
  coeffs   = Missing["NotImplemented", "Sch Lemma 5.2 linear system not yet \
implemented; awaiting secondKindNormalForms."];
  residual = Missing["NotImplemented", "First-kind residual extraction is \
gated on Lemma 5.5 + Lemma 5.2 above."];
  certificate = <|
    "gamma"             -> gammas,
    "coeffs"            -> coeffs,
    "firstKindResidual" -> residual,
    "logTerms"          -> Lookup[diagnostic, "logTerms", {}]
  |>;
  tragerFailure["NonElementary",
    "Method"          -> "Schultz",
    "Certificate"     -> certificate,
    "Reason"          -> "No principal c·Δ_j found within MaxTorsionOrder, \
and the §S.6.2 fail-in-style decomposition is not yet implemented. \
Returning a structured Failure with the certificate placeholder.",
    "Diagnostic"      -> diagnostic
  ]
];

(* End of module *)
