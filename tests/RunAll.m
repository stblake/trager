(* ::Package:: *)

(* ::Title:: *)
(* Run every test file. Exits non-zero on the first failed suite.           *)
(*                                                                           *)
(* Usage:  wolframscript -file tests/RunAll.m                                *)

$testsDir = FileNameJoin[{Directory[], "tests"}];
$testFiles = {
  "TestValidate.m",
  "TestReduce.m",
  "TestGenus.m",
  "TestBasis.m",
  "TestArithmetic.m",
  "TestShift.m",
  "TestHermite.m",
  "TestResidues.m",
  "TestDivisor.m",
  "TestPrincipalGen.m",
  "TestTorsion.m",
  "TestIdealDecomposition.m",
  "TestTragerLogTerms.m",
  "TestMillerKauersLogTerms.m",
  "TestLogToArcTan.m",
  "TestIntegrate.m",
  "TestGenusPositive.m",
  "TestRescale.m",
  "TestSurface.m",
  "TestParameters.m"
};

$overallExit = 0;

Scan[
  Function[{file},
    Print["\n########################################"];
    Print["# Running ", file];
    Print["########################################"];
    Module[{code, path},
      path = FileNameJoin[{$testsDir, file}];
      code = RunProcess[
        {"/Applications/Mathematica.app/Contents/MacOS/wolframscript",
         "-file", path}
      ];
      Print[code["StandardOutput"]];
      If[code["ExitCode"] =!= 0,
        Print["!! suite failed: ", file];
        $overallExit = 1;
      ];
    ];
  ],
  $testFiles
];

If[$overallExit === 0,
  Print["\n=== ALL SUITES PASSED ==="];
  Exit[0],
  Print["\n=== SOME SUITES FAILED ==="];
  Exit[1]
];
