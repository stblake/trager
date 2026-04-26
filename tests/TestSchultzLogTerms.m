(* ::Package:: *)

(* ::Title:: *)
(* Tests for the Schultz §S.6.1 logarithmic-part construction. *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

(* schultzConstructLogTerms operates on Hermite-reduced integrands per Sch    *)
(* Lemma 4.4: the post-Hermite remainder satisfies deg(a_i) + δ_i < deg(b)   *)
(* AND has at-most simple poles at infinity (with the eq. 4.11 residues       *)
(* zero, since otherwise the §5 fail-in-style decomposition is required).    *)
(* All tests below first invoke schultzHermiteReduce.                         *)

(* ::Section:: *)
(* Algebraic-only antiderivative: Hermite absorbs everything; remainder is    *)
(* zero; log-term construction returns {}.                                     *)

tsection["schultzConstructLogTerms: algebraic-only post-Hermite returns {}"];

Module[{basis, integrand, hRes, result},
  (* x dx / sqrt(x²+1): antideriv is sqrt(x²+1). Schultz Hermite absorbs     *)
  (* the whole integrand into algPart via the Lemma 4.4 part-2 linear        *)
  (* system; remainder = 0, so log-term construction returns {}.              *)
  basis = buildIntegralBasis[2, x^2 + 1, x];
  integrand = x / y;
  hRes = schultzHermiteReduce[integrand, basis, y];
  tassert["Hermite produces remainder with all-zero AF coefficients",
    AllTrue[hRes["remainder"]["Coeffs"], zeroQ]];
  result = schultzConstructLogTerms[hRes["remainder"], hRes["D"], basis, y];
  tassertEqual["log terms are empty (algebraic-only antideriv)",
    {}, result];
];

(* ::Section:: *)
(* Genus-0 finite-residue log antiderivative.                                   *)

tsection["schultzConstructLogTerms: 1/(x sqrt(x²-1)) -- finite residues only"];

Module[{basis, integrand, hRes, result, sumOfLogs, zCheck},
  (* y² = x²-1, integrand = 1/(x·y) dx. Antideriv = -arcsec(x) = i·log(...).  *)
  (* Genus 0; residues at the two finite places (0, ±i) are non-zero;       *)
  (* infinity residues vanish (1/(x·y) ~ 1/x² at infinity).                   *)
  basis = buildIntegralBasis[2, x^2 - 1, x];
  integrand = 1 / (x * y);
  hRes = schultzHermiteReduce[integrand, basis, y];
  result = schultzConstructLogTerms[hRes["remainder"], hRes["D"], basis, y];
  tassert["log-term construction returns a list (not a Failure)",
    !MatchQ[result, _Failure] && ListQ[result]];
  tassert["produces at least one log term",
    Length[result] >= 1];
  tassert["each entry is a {coefficient, F} pair",
    AllTrue[result, MatchQ[#, {_, _}] &]];

  (* Cross-check: differentiate the algPart via afD (which knows y' = g'/2y),  *)
  (* differentiate each log argument F_j (treating y' similarly), and check    *)
  (* that the sum equals the integrand modulo y² = x² - 1. We use Reduce      *)
  (* on Cancel[Together[diff]] over the curve relation as the comparison.     *)
  Module[{algDeriv, logDeriv, totalDeriv, diff},
    algDeriv = afToStandard[afD[hRes["algPart"], basis], basis, y];
    (* Σ c_j · F_j'/F_j computed with the chain rule treating y as a function *)
    (* of x via y' = g'/(2y). For genus-0 simple radicals the {coeff, F}      *)
    (* pairs encode log arguments F that may contain y; differentiate by      *)
    (* substituting y' on the way out.                                          *)
    logDeriv = Total[Map[
      Function[{pair},
        Module[{c = pair[[1]], F = pair[[2]]},
          c * (D[F, x] + D[F, y] * x/y) / F
            (* y' = g'/(2y) = 2x/(2y) = x/y for y² = x²-1. *)
        ]
      ],
      result
    ]];
    totalDeriv = Together[algDeriv + logDeriv];
    diff = Together[(totalDeriv - integrand) /. y -> Sqrt[x^2 - 1]];
    tassert["algPart' + Σ c_j · F_j'/F_j matches the integrand on the curve",
      zeroQ[Numerator[diff]]]
  ];
];

(* ::Section:: *)
(* Infinity residues handled by the unified Lemma 4.1 path.                    *)
(*                                                                              *)
(* The refactored schultzConstructLogTerms (S.6.1) merges finite + infinity    *)
(* residues into a single per-residue Schultz divisor and tests torsion via    *)
(* Lemma 4.1. Inputs whose only residues are at infinity (e.g. 1/sqrt(x²+1))   *)
(* therefore produce log antiderivatives directly rather than deferring to the *)
(* §S.6.2 fail-in-style certificate path. The fail-in-style stub is reserved   *)
(* for genuinely non-elementary inputs (positive-genus, divisor not torsion    *)
(* within MaxTorsionOrder).                                                     *)

tsection["schultzConstructLogTerms: 1/sqrt(x²+1) handled via Lemma 4.1"];

Module[{basis, integrandAF, b, result},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  integrandAF = afMake[{0, 1/(x^2 + 1)}, basis];
  b = x^2 + 1;
  result = schultzConstructLogTerms[integrandAF, b, basis, y];
  tassert["log-term construction returns a list (not a Failure)",
    !MatchQ[result, _Failure] && ListQ[result]];
  tassert["produces at least one log term",
    Length[result] >= 1];
  (* Differentiate Σ c_j · F_j'/F_j on the curve y² = x²+1 (y' = x/y) and    *)
  (* check the result equals the integrand 1/y after y -> sqrt(x²+1).         *)
  Module[{logDeriv, diff, integrand},
    integrand = 1/y;
    logDeriv = Total[Map[
      Function[{pair},
        Module[{c = pair[[1]], F = pair[[2]]},
          c * (D[F, x] + D[F, y] * x/y) / F
        ]
      ],
      result
    ]];
    diff = Together[(logDeriv - integrand) /. y -> Sqrt[x^2 + 1]];
    tassert["Σ c_j · F_j'/F_j matches 1/sqrt(x²+1) on the curve",
      zeroQ[Numerator[diff]]]
  ];
];

(* ::Section:: *)
(* Cubic-radical (n = 3) integrand with K(ζ_3)-valued residues.                 *)
(*                                                                               *)
(* ∫dx/(x·(x³+1)^(1/3)) is genus 1 with three finite residues {1, ζ_3, ζ_3²} at *)
(* the three places over x = 0. Computing the per-residue Schultz divisor       *)
(* requires the HNF / divisor-multiplication chain to canonicalize K(ζ_3)        *)
(* coefficients — without RootReduce-aware canonicalisation these matrices      *)
(* carry expressions whose textual form is nonzero but whose true value is 0/0, *)
(* producing cascading 1/0 errors during HNF pivot selection. Regression for   *)
(* the §10.1 / TragerPlan extension-aware HNF chain.                             *)

tsection["schultzConstructLogTerms: cubic radical with ζ_3 residues"];

Module[{integrand, expected},
  integrand = 1/(x*(x^3 + 1)^(1/3));
  expected = Trager`IntegrateTrager[integrand, x, "Schultz" -> True];
  tassert["Schultz returns a non-Failure on the running cubic-radical case",
    !MatchQ[expected, _Failure]];
  tassert["Result contains Log terms",
    !FreeQ[expected, Log]];
  Module[{diff},
    diff = Simplify @ Together[D[expected, x] - integrand];
    tassertEqual["differentiating the result returns the integrand",
      0, diff]
  ]
];

tSummary[];
