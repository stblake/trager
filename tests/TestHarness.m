(* ::Package:: *)

(* ::Title:: *)
(* Minimal test harness *)

(* Expose Trager`Private` internals to test files. The package presents     *)
(* only IntegrateTrager publicly, but white-box tests need access to       *)
(* helpers like validateInput, hermiteReduce, MillerKauersLogTerms, etc.  *)
(* This Prepend is a test-only convenience and does NOT pollute end-user   *)
(* sessions, which load the package without this harness.                  *)
$ContextPath = DeleteDuplicates[Prepend[$ContextPath, "Trager`Private`"]];

(* Single-purpose assert function. Tracks a pass/fail count in two globals   *)
(* and prints a one-line result per assertion. Callers end with a call to    *)
(* tSummary[] which reports totals and exits non-zero on any failure, so     *)
(* `wolframscript -file tests/RunTests.m; echo $?` works in CI.              *)

$tPassCount = 0;
$tFailCount = 0;
$tFailedNames = {};

(* tassert[name, condition]                                                  *)
(* Records one assertion. The condition is evaluated eagerly; we only look   *)
(* at its truthiness with TrueQ.                                             *)

ClearAll[tassert];
SetAttributes[tassert, HoldRest];
tassert[name_String, condition_] := Module[{c},
  c = condition;
  If[TrueQ[c],
    $tPassCount++;
    Print["  pass  ", name],
    $tFailCount++;
    AppendTo[$tFailedNames, name];
    Print["  FAIL  ", name];
    Print["        got: ", c];
  ];
];

(* tassertEqual[name, expected, actual]                                      *)
(* Sugar for equality tests, which dominate. Uses SameQ after a Together     *)
(* pass so rational expressions compare after normalization.                 *)

ClearAll[tassertEqual];
tassertEqual[name_String, expected_, actual_] := Module[{lhs, rhs, same},
  lhs = Together[expected];
  rhs = Together[actual];
  same = TrueQ[lhs === rhs] || TrueQ[Simplify[lhs - rhs] === 0];
  If[same,
    $tPassCount++;
    Print["  pass  ", name],
    $tFailCount++;
    AppendTo[$tFailedNames, name];
    Print["  FAIL  ", name];
    Print["        expected: ", expected];
    Print["        actual:   ", actual];
  ];
];

(* tassertFailure[name, tag, result]                                         *)
(* Asserts that `result` is a Failure object with the named tag.             *)

ClearAll[tassertFailure];
tassertFailure[name_String, tag_String, result_] := Module[{ok},
  ok = MatchQ[result, _Failure] && (result[[1]] === tag);
  If[ok,
    $tPassCount++;
    Print["  pass  ", name],
    $tFailCount++;
    AppendTo[$tFailedNames, name];
    Print["  FAIL  ", name];
    Print["        expected Failure[", tag, "], got: ", result];
  ];
];

(* tsection[title] prints a visual delimiter for the running output. *)
ClearAll[tsection];
tsection[title_String] := Print["\n=== ", title, " ==="];

(* tSummary[] prints the final tally and Exits non-zero on any failure. *)
ClearAll[tSummary];
tSummary[] := Module[{total},
  total = $tPassCount + $tFailCount;
  Print["\n----"];
  Print["Ran ", total, " assertions: ", $tPassCount, " passed, ", $tFailCount, " failed."];
  If[$tFailCount > 0,
    Print["Failed:"];
    Scan[Print["  - ", #] &, $tFailedNames];
    Exit[1]
  ];
  Exit[0]
];
