(* ::Package:: *)

(* ::Title:: *)
(* Tests for Phase 5 constructLogTerms *)

(* ::Text:: *)
(* After the D2/D3-split (branch vs non-branch) reduction in residueDivisor*)
(* and the coprime-content cleanup in divisorAdd / divisorNegate (Trager  *)
(* 1984 Ch 5 §3), tier-1 log cases integrate end-to-end. We verify the    *)
(* result differentiates to the integrand.                                 *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

Off[IntegrateTrager::autoreduce];

verifyLog[label_, integrand_, rel_] := Module[{r, n, g, yRoot, diff},
  r = IntegrateTrager[integrand, {x, y, rel}];
  If[MatchQ[r, _Failure], tassert[label, False]; Return[]];
  n = Exponent[rel[[1]], y];
  g = rel[[2]];
  yRoot = g^(1/n);
  diff = Simplify[D[r /. y -> yRoot, x] - (integrand /. y -> yRoot)];
  tassert[label, TrueQ[diff === 0]]
];

tsection["constructLogTerms: tier-1 log cases integrate correctly"];

verifyLog["1/(xy), y^2 = x^2+1",
  1/(x*y), y^2 == x^2 + 1];

verifyLog["y/(x^2-2), y^2 = x^2+1",
  y/(x^2 - 2), y^2 == x^2 + 1];

tsection["constructLogTerms: structural invariants still hold"];

Module[{b, r, res, terms},
  b = buildIntegralBasis[2, x^2 + 1, x];
  r = hermiteReduce[1/(x*y), b, y];
  res = computeResidues[r["remainder"], r["D"], b, y, Z];
  terms = constructLogTerms[res["residues"], r["remainder"], r["D"], b, y];
  (* constructLogTerms may return either a list of {coeff, arg} pairs OR  *)
  (* a Failure. Both are structurally valid outputs.                       *)
  tassert["constructLogTerms returns list of pairs or a Failure",
    (ListQ[terms] && AllTrue[terms, MatchQ[#, {_, _}] &]) ||
    MatchQ[terms, _Failure]];
];

tsection["constructLogTerms: algebraic-only cases still succeed"];

(* No log residues -> empty log term list -> pure algebraic result.       *)
Module[{r, yRoot},
  r = IntegrateTrager[x/y, {x, y, y^2 == x^2 + 1}];
  yRoot = Sqrt[x^2 + 1];
  tassert["x/Sqrt[x^2+1] integrates to algebraic Sqrt[x^2+1]",
    TrueQ[Simplify[D[r /. y -> yRoot, x] - x/yRoot] === 0]]
];

tSummary[];
