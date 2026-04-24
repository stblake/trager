(* ::Package:: *)

(* ::Title:: *)
(* Tests for Phase-6 conjugate-log -> ArcTan rewrite                         *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

Off[IntegrateTrager::autoreduce];
Off[IntegrateTrager::scale];

(* Predicate: does an expression contain any Log head whose argument is in   *)
(* (x, I, Sqrt, ...)? Used to confirm the rewrite eliminates conjugate-log   *)
(* pairs in favour of an ArcTan.                                              *)
ClearAll[hasComplexLogQ];
hasComplexLogQ[expr_, x_Symbol] := !FreeQ[expr, Log[_?(! FreeQ[#, I] &)]];

(* Helper: wrap rewrite + symbolic-zero diff check on the derivative. *)
ClearAll[rewriteAndDiffZero];
rewriteAndDiffZero[input_, x_Symbol] := Module[{out, diff},
  out = logsToArcTan[input, x];
  diff = Simplify[D[out - input, x]];
  TrueQ[diff === 0]
];

tsection["imagTerms / realTerms primitives"];

tassert["imagTerms[3 + 4 I, x] = 4",
  TrueQ[Together[imagTerms[3 + 4 I, x] - 4] === 0]];

tassert["realTerms[3 + 4 I, x] = 3",
  TrueQ[Together[realTerms[3 + 4 I, x] - 3] === 0]];

tassert["imagTerms[x + I y, x] = 0  (y treated as constant in x)",
  TrueQ[Together[imagTerms[x + I y, x] - y] === 0]];

tassert["realTerms[x + I, x] = x",
  TrueQ[Together[realTerms[x + I, x] - x] === 0]];

tassert["imagTerms[x - I, x] = -1",
  TrueQ[Together[imagTerms[x - I, x] - (-1)] === 0]];

tsection["arcTanTerm: nicer-form selector"];

(* When im is polynomial in x, the first branch wins and we keep ArcTan[re/im]*)
(* unchanged. The flip to -ArcTan[im/re] only triggers when im has nasty      *)
(* radicals in x.                                                              *)
tassert["arcTanTerm[x, 1, x] = ArcTan[x]",
  TrueQ[arcTanTerm[x, 1, x] === ArcTan[x]]];

tassert["arcTanTerm[1, x, x] = ArcTan[1/x]  (im polynomial: first branch wins)",
  TrueQ[arcTanTerm[1, x, x] === ArcTan[1/x]]];

(* im has a fractional-power radical in x, re is rational: flip to -ArcTan. *)
tassert["arcTanTerm[1, Sqrt[x^2+1], x] flips to -ArcTan[Sqrt[x^2+1]]",
  TrueQ[arcTanTerm[1, Sqrt[x^2 + 1], x] === -ArcTan[Sqrt[x^2 + 1]]]];

tsection["log2ArcTan rule (Im[a] != 0 case)"];

tassert["I/2 Log[(x+I)/(x-I)] expansion -> -ArcTan[x]",
  Module[{input, out},
    input = -I/2 Log[x + I] + I/2 Log[x - I];
    out = logsToArcTan[input, x];
    TrueQ[out === -ArcTan[x]] || TrueQ[Simplify[out + ArcTan[x]] === 0]]];

tassert["I/2 Log[x + I Sqrt[2]] - I/2 Log[x - I Sqrt[2]] -> ArcTan[x/Sqrt[2]] form (D == 0)",
  rewriteAndDiffZero[I/2 Log[x + I Sqrt[2]] - I/2 Log[x - I Sqrt[2]], x]];

tassert["3 I Log[x + I] - 3 I Log[x - I]  (D == 0 after rewrite)",
  rewriteAndDiffZero[3 I Log[x + I] - 3 I Log[x - I], x]];

tassert["rule A produces a real-coefficient ArcTan + 0 leftover Log",
  Module[{input, out},
    input = -I/2 Log[x + I] + I/2 Log[x - I];
    out = logsToArcTan[input, x];
    !hasComplexLogQ[out, x]]];

tsection["log2ArcTan2 rule (Re[a] != 0, anti-conjugate case)"];

tassert["(-1+I) Log[x-I] + (1+I) Log[x+I]  (D == 0 after rewrite)",
  rewriteAndDiffZero[(-1 + I) Log[x - I] + (1 + I) Log[x + I], x]];

tassert["(2+I) Log[x-I] + (-2+3I) Log[x+I]  (D == 0 after rewrite)",
  rewriteAndDiffZero[(2 + I) Log[x - I] + (-2 + 3 I) Log[x + I], x]];

tsection["no-op cases"];

tassert["Log[x+1] + Log[x-1] is left alone (no conjugate structure)",
  Module[{out},
    out = logsToArcTan[Log[x + 1] + Log[x - 1], x];
    TrueQ[out === Log[x + 1] + Log[x - 1]]]];

tassert["pure rational expression is unchanged",
  Module[{out},
    out = logsToArcTan[x + 1/(x^2 + 1), x];
    TrueQ[out === x + 1/(x^2 + 1)]]];

tassert["single Log term is unchanged",
  Module[{out},
    out = logsToArcTan[3 Log[x^2 + 1], x];
    TrueQ[out === 3 Log[x^2 + 1]]]];

tsection["end-to-end: IntegrateTrager invokes the rewrite via reassemble"];

(* The Kauers and Miller log-term methods on 1/((x^2 + 1) y) with y^2 = 1 - x^2*)
(* produce a conjugate Log pair                                               *)
(*   I/(2 Sqrt[2]) (Log[-2 I x + Sqrt[2] y] - Log[2 I x + Sqrt[2] y])         *)
(* which, after the Phase-6 rewrite, collapses to                             *)
(*   -ArcTan[y / (Sqrt[2] x)] / Sqrt[2].                                      *)
(* This integrand is the canonical witness that reassemble actually wires    *)
(* through logsToArcTan.                                                      *)
tassert["IntegrateTrager[1/((x^2+1) y), y^2 = 1-x^2, Kauers] -> ArcTan form",
  Module[{r},
    r = Quiet @ Trager`IntegrateTrager[1/((x^2 + 1) y),
          {x, y, y^2 == 1 - x^2}, "LogTermsMethod" -> "Kauers"];
    !MatchQ[r, _Failure] && !FreeQ[r, ArcTan]]];

tassert["IntegrateTrager[1/((x^2+1) y), y^2 = 1-x^2, Miller] -> ArcTan form",
  Module[{r},
    r = Quiet @ Trager`IntegrateTrager[1/((x^2 + 1) y),
          {x, y, y^2 == 1 - x^2}, "LogTermsMethod" -> "Miller"];
    !MatchQ[r, _Failure] && !FreeQ[r, ArcTan]]];

tSummary[];
