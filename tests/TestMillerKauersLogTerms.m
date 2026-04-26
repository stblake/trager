(* ::Package:: *)

(* ::Title:: *)
(* Tests for MillerKauersLogTerms *)

(* ::Text:: *)
(* Drop-in cross-check: every input that TragerLogTerms handles must also  *)
(* work via MillerKauersLogTerms. Additionally, we verify the headline      *)
(* examples from Miller 2012 Ch V — the ones where Kauers' original        *)
(* algorithm fails but Miller's refinement succeeds.                        *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

Off[IntegrateTrager::autoreduce];

(* ::Section:: *)
(* Utility: end-to-end verification via "LogTermsMethod" -> "MillerKauers".*)
(*                                                                          *)
(* We differentiate the returned antiderivative and check it equals the    *)
(* integrand modulo y^n = g. Numerical fallback catches cases where        *)
(* Simplify can't collapse nested Root objects symbolically.               *)

verifyMK[label_, integrand_, rel_] := Module[
  {r, n, g, yRoot, diff, simplified, samples, tol = 10^-25, prec = 50,
   numericZero},
  r = IntegrateTrager[integrand, {x, y, rel},
        "LogTermsMethod" -> "MillerKauers"];
  If[MatchQ[r, _Failure],
    tassert[label, False];
    Print["        Failure: ", r];
    Return[]
  ];
  n = Exponent[rel[[1]], y];
  g = rel[[2]];
  yRoot = g^(1/n);
  diff = D[r /. y -> yRoot, x] - (integrand /. y -> yRoot);
  simplified = Quiet @ Simplify[diff];
  If[TrueQ[simplified === 0],
    tassert[label, True]; Return[]
  ];
  (* Numerical fallback: sample at rationals with high working precision. *)
  SeedRandom[20260424];
  samples = Table[
    N[diff /. x -> RandomReal[{-3, 3}, WorkingPrecision -> prec], prec],
    {5}
  ];
  numericZero = AllTrue[samples,
    NumericQ[#] && Abs[Re[#]] < tol && Abs[Im[#]] < tol &];
  tassert[label, numericZero];
  If[!numericZero,
    Print["        symbolic residual: ", simplified];
    Print["        numerical samples: ", samples]
  ]
];

(* ::Section:: *)
(* Tier 1: sanity — every TragerLogTerms tier-1 case works via MK         *)

tsection["MillerKauersLogTerms: tier-1 log cases"];

verifyMK["1/(xy), y^2 = x^2+1",
  1/(x*y), y^2 == x^2 + 1];

verifyMK["y/(x^2-2), y^2 = x^2+1",
  y/(x^2 - 2), y^2 == x^2 + 1];

(* ::Section:: *)
(* Tier 2: Miller's headline examples                                      *)
(*                                                                          *)
(* Ex 10 of Miller 2012 (= Ex 9 of Kauers 2008): the integral where Kauers *)
(* finds a correct logand but with the wrong multiplicity, and Mathematica/*)
(* major systems all fail. MillerKauers should succeed.                    *)

tsection["MillerKauersLogTerms: Miller 2012 Ex 10 (Kauers-fails case)"];

verifyMK["(y+1)/((x^2+1)(x+1)), y^2 = x^2+1  [Miller Ex 10]",
  (y + 1)/((x^2 + 1)(x + 1)), y^2 == x^2 + 1];

(* ::Section:: *)
(* Tier 2b: positive-genus cases that exhaust Miller's strict pseudocode   *)
(* but succeed via Kauers' iterated-squaring fallback. Regression for     *)
(* "Miller is flimsy compared to Kauers" — every integrand handled by    *)
(* Kauers must also work via the Miller method.                           *)

tsection["MillerKauersLogTerms: Kauers-fallback positive-genus cases"];

(* User-reported case: 1/(x · (x²−3x+2)^(1/3)) on the genus-1 curve       *)
(* y³ = (x−1)(x−2). Principal generator at μ = 6 (elliptic torsion); the *)
(* h^μ candidate enumeration alone never finds it. Kauers' iterated      *)
(* squaring of the full block-elim GB picks it up.                        *)
verifyMK["1/(x (x^2-3x+2)^(1/3)), y^3 = x^2-3x+2  [Miller-stalls case]",
  1/(x*y), y^3 == x^2 - 3 x + 2];

(* ::Section:: *)
(* Tier 3: algebraic-only integrals (log part empty) still work            *)

tsection["MillerKauersLogTerms: algebraic-only cases"];

verifyMK["x/Sqrt[x^2+1] (pure algebraic)",
  x/y, y^2 == x^2 + 1];

(* ::Section:: *)
(* Tier 4: cross-check Trager and MillerKauers give equivalent answers.   *)
(*                                                                          *)
(* Equivalent ≠ syntactically identical: log-part representatives can differ*)
(* by constants, alternate branches, or syntactically different logands    *)
(* whose difference is a constant. Compare via derivative.                 *)

tsection["MillerKauersLogTerms: cross-check vs Trager"];

Module[{cases, xVal = 7/5},
  cases = {
    {"1/Sqrt[x^2+1]",    1/Sqrt[x^2+1]},
    {"x/Sqrt[x^2+1]",    x/Sqrt[x^2+1]},
    {"1/Sqrt[x^2-1]",    1/Sqrt[x^2-1]},
    {"1/Sqrt[1-x^2]",    1/Sqrt[1-x^2]},
    {"1/(x Sqrt[x^2+1])", 1/(x*Sqrt[x^2+1])}
  };
  Do[
    Module[{label = pair[[1]], f = pair[[2]], rT, rMK, dT, dMK, residual},
      rT  = IntegrateTrager[f, x, "LogTermsMethod" -> "Trager"];
      rMK = IntegrateTrager[f, x, "LogTermsMethod" -> "MillerKauers"];
      If[MatchQ[rT, _Failure] || MatchQ[rMK, _Failure],
        tassert["  both methods succeed on " <> label, False];
        Continue[]
      ];
      dT  = D[rT, x];
      dMK = D[rMK, x];
      residual = Quiet @ Simplify[dT - dMK];
      tassert["  Trager and MK derivatives match on " <> label,
        TrueQ[residual === 0] ||
          TrueQ[Abs[N[residual /. x -> xVal, 40]] < 10^-30]]
    ],
    {pair, cases}
  ]
];

(* ::Section:: *)
(* Tier 5: structural invariants on the low-level entry point              *)

tsection["MillerKauersLogTerms: structural invariants"];

Module[{b, r, terms},
  b = buildIntegralBasis[2, x^2 + 1, x];
  r = hermiteReduce[1/(x*y), b, y];
  terms = MillerKauersLogTerms[{}, r["remainder"], r["D"], b, y];
  tassert["MillerKauersLogTerms returns list of {coeff, vArg} pairs",
    ListQ[terms] && AllTrue[terms, MatchQ[#, {_, _}] &]]
];

(* Empty remainder → empty log-term list. *)
Module[{b, r, terms},
  b = buildIntegralBasis[2, x^2 + 1, x];
  r = hermiteReduce[x/y, b, y];   (* purely algebraic; remainder zero *)
  terms = MillerKauersLogTerms[{}, r["remainder"], r["D"], b, y];
  tassertEqual["zero remainder → empty log-term list", {}, terms]
];

(* ::Section:: *)
(* Tier 6: KauersLogTerms — verify the heuristic method is wired in       *)
(* and successfully handles cases where Miller's strict pseudocode fails  *)
(* (returning a partial result if necessary).                              *)

tsection["KauersLogTerms: heuristic method"];

(* Smoke test: tier-1 integrand should pass through Kauers as well. *)
Module[{r, yRoot, diff},
  r = IntegrateTrager[1/(x*y), {x, y, y^2 == x^2 + 1},
        "LogTermsMethod" -> "Kauers"];
  If[MatchQ[r, _Failure],
    tassert["Kauers integrates 1/(xy)", False],
    yRoot = Sqrt[x^2 + 1];
    diff = Simplify[D[r /. y -> yRoot, x] - (1/(x*yRoot))];
    tassert["Kauers integrates 1/(xy)", TrueQ[diff === 0]]
  ]
];

(* Hard case: Kauers' partial-result path. The integrand is the canonical *)
(* example where Miller's strict pseudocode times out / exhausts μ but    *)
(* Kauers' iterated-square approach finds a partial answer. Since the    *)
(* partial path now returns                                               *)
(*   attempted + IntegrateTrager[residual, x, opts]                       *)
(* (with the inner call held inert via HoldForm[IntegrateTrager][...]), *)
(* we verify: (a) the return is not a Failure, (b) it contains a held    *)
(* IntegrateTrager subterm in the residual variable x, and (c) the       *)
(* derivative of the returned sum — treating the held term as ∫residual  *)
(* dx — reproduces the original integrand. (c) is checked by             *)
(* differentiating the attempted part and confirming the residual inside *)
(* the held call equals integrand − attempted'.                           *)
Module[{r, attempted, heldPart, residual, integrandX, yRoot, diff},
  r = IntegrateTrager[x^2/((x^2 - 1)*y), {x, y, y^4 == x^8 + 1},
        "LogTermsMethod" -> "Kauers"];
  tassert["Kauers partial result is not a Failure on x^2/((x^2-1)y), y^4=x^8+1",
    !MatchQ[r, _Failure]];
  (* Extract the held inner IntegrateTrager[residual, x, opts] subterm.  *)
  heldPart = Cases[r,
    HoldPattern[HoldForm[IntegrateTrager][res_, x, ___]] :> res,
    {0, Infinity}];
  tassert["partial result contains exactly one held IntegrateTrager[...]",
    Length[heldPart] === 1];
  If[Length[heldPart] === 1,
    residual = First[heldPart];
    attempted = r - HoldForm[IntegrateTrager][residual, x,
                                               "LogTermsMethod" -> "Kauers"];
    yRoot = (x^8 + 1)^(1/4);
    integrandX = x^2/((x^2 - 1)*yRoot);
    diff = Simplify[
      (D[attempted /. y -> yRoot, x] + residual) - integrandX];
    tassert["attempted' + residual reproduces the integrand",
      TrueQ[diff === 0] || TrueQ[zeroQ[diff]]]
  ]
];

tSummary[]
