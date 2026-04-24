(* ::Package:: *)

(* ::Title:: *)
(* Tests for hermiteReduce *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

(* Round-trip: if `r` = hermiteReduce[f], then                               *)
(*   d/dz (algPart) + remainder  ==  f     (as AF elements)                 *)
(* holds identically. This is the fundamental correctness invariant.        *)

hermiteRoundTripOK[integrand_, basis_?basisDescriptorQ, y_Symbol,
                   r_Association] := Module[
  {dAlg, sum, origAF, diff},
  dAlg = afD[r["algPart"], basis];
  sum = afPlus[dAlg, r["remainder"], basis];
  origAF = rationalizeToAF[integrand, basis, y];
  diff = afMinus[sum, origAF, basis];
  AllTrue[diff["Coeffs"], TrueQ[Together[#] === 0] &]
];

tsection["hermiteReduce: plan phase-3 test 1 (double pole)"];

Module[{b, r, expected},
  b = buildIntegralBasis[2, 1 + x^2, x];
  r = hermiteReduce[1/(x^2*y), b, y];
  tassert["returns an Association", AssociationQ[r]];
  tassertEqual["algPart = -y/x",
    -(y/x), Together[afToStandard[r["algPart"], b, y]]];
  tassertEqual["remainder coefficients all zero",
    {0, 0}, r["remainder"]["Coeffs"]];
  tassertEqual["iterations = 1", 1, r["iterations"]];
  tassert["round-trip: d/dz(algPart) + remainder == original",
    hermiteRoundTripOK[1/(x^2*y), b, y, r]];
];

tsection["hermiteReduce: plan phase-3 test 2 (no reduction needed)"];

Module[{b, r},
  b = buildIntegralBasis[2, x^2 + 1, x];
  r = hermiteReduce[x/y, b, y];
  tassertEqual["algPart = 0", {0, 0}, r["algPart"]["Coeffs"]];
  tassertEqual["iterations = 0", 0, r["iterations"]];
  tassertEqual["remainder coeff[1] = x/(x^2+1)",
    x/(1 + x^2), Together[r["remainder"]["Coeffs"][[2]]]];
  tassert["round-trip",
    hermiteRoundTripOK[x/y, b, y, r]];
];

tsection["hermiteReduce: plan phase-3 test 3 (already simple-pole)"];

Module[{b, r},
  b = buildIntegralBasis[2, x^2 + 1, x];
  r = hermiteReduce[1/(x*y), b, y];
  tassertEqual["algPart = 0 (Hermite no-op)",
    {0, 0}, r["algPart"]["Coeffs"]];
  tassertEqual["D = x(x^2+1) (square-free)",
    Expand[x*(x^2 + 1)], Expand[r["D"]]];
  tassert["round-trip",
    hermiteRoundTripOK[1/(x*y), b, y, r]];
];

tsection["hermiteReduce: higher-order pole (x^3)"];

Module[{b, r, std},
  (* y^2 = x^2+1, integrand 1/(x^3 y). Triple pole at x=0.                *)
  (* Expected: Hermite reduces to simple pole, accumulating an algebraic *)
  (* part over 1-2 iterations.                                            *)
  b = buildIntegralBasis[2, x^2 + 1, x];
  r = hermiteReduce[1/(x^3*y), b, y];
  tassert["iterations >= 1 (non-trivial reduction)", r["iterations"] >= 1];
  tassert["round-trip",
    hermiteRoundTripOK[1/(x^3*y), b, y, r]];
  tassert["remainder has square-free denominator",
    Module[{D, fac},
      D = r["D"];
      fac = Rest[FactorSquareFreeList[D]];
      AllTrue[fac, Last[#] == 1 &]
    ]];
];

tsection["hermiteReduce: cubic radical"];

Module[{b, r},
  (* y^3 = x, integrand 1/(x^2 y^2). Compute by brute force.              *)
  b = buildIntegralBasis[3, x, x];
  r = hermiteReduce[1/(x^2*y^2), b, y];
  tassert["round-trip n=3",
    hermiteRoundTripOK[1/(x^2*y^2), b, y, r]];
  tassert["remainder square-free",
    Module[{fac = Rest[FactorSquareFreeList[r["D"]]]},
      AllTrue[fac, Last[#] == 1 &]
    ]];
];

tsection["hermiteReduce: quartic radical"];

Module[{b, r},
  b = buildIntegralBasis[4, x^3, x];
  r = hermiteReduce[1/(x*y), b, y];
  tassert["round-trip n=4",
    hermiteRoundTripOK[1/(x*y), b, y, r]];
];

tsection["hermiteReduce: no y-dependence in integrand"];

Module[{b, r},
  b = buildIntegralBasis[2, x^2 + 1, x];
  r = hermiteReduce[1/x^2, b, y];
  tassert["algPart coeff[0] = -1/x",
    TrueQ[Together[r["algPart"]["Coeffs"][[1]] - (-1/x)] === 0]];
  tassert["algPart coeff[1] = 0",
    TrueQ[r["algPart"]["Coeffs"][[2]] === 0]];
  tassert["round-trip",
    hermiteRoundTripOK[1/x^2, b, y, r]];
];

tsection["hermiteReduce: multiple pole locations"];

Module[{b, r},
  (* y^2 = x^2+1, integrand 1/((x^2)(x-1)^2 y). Two distinct double poles. *)
  b = buildIntegralBasis[2, x^2 + 1, x];
  r = hermiteReduce[1/(x^2*(x - 1)^2*y), b, y];
  tassert["round-trip, two double poles",
    hermiteRoundTripOK[1/(x^2*(x - 1)^2*y), b, y, r]];
  tassert["remainder has square-free denominator",
    Module[{fac = Rest[FactorSquareFreeList[r["D"]]]},
      AllTrue[fac, Last[#] == 1 &]
    ]];
  tassert["iterations >= 2 (both double poles processed)",
    r["iterations"] >= 2];
];

tsection["hermiteReduce: pole-at-infinity invariant (opt-in)"];

Module[{b, r},
  (* Normal call (no invariant check) -- algPart has -1/x but that's fine *)
  (* because x here is a generic finite place, not "shifted-infinity".    *)
  b = buildIntegralBasis[2, 1 + x^2, x];
  r = hermiteReduce[1/(x^2*y), b, y];
  tassert["no invariant check: Hermite succeeds",
    AssociationQ[r]];

  (* With checkPoleAt = 0, the same input fires the invariant (since      *)
  (* algPart = -y/x has a pole at x=0).                                   *)
  r = hermiteReduce[1/(x^2*y), b, y, 0];
  tassertFailure["invariant check fires when algPart has pole at x=0",
    "InternalInconsistency", r];
];

Module[{b, r},
  (* Integrand with no double pole: algPart = 0, invariant passes trivially. *)
  b = buildIntegralBasis[2, x^2 + 1, x];
  r = hermiteReduce[1/(x*y), b, y, 0];
  tassert["invariant check passes when algPart = 0",
    AssociationQ[r]];
];

tsection["hermiteReduce: pipeline integration with shiftAwayFromInfinity"];

Module[{b, shifted, bShifted, r},
  (* Full pipeline for 1/(x^2 y) on y^2 = 1+x^2:                           *)
  (*   shift (a=0) -> transformed integrand in z                           *)
  (*   hermite with checkPoleAt = 0 (z=0 is the shifted infinity)          *)
  shifted = shiftAwayFromInfinity[1/(x^2*y), x, y, 2, 1 + x^2, z];
  bShifted = buildIntegralBasis[shifted["n"], shifted["g"], shifted["z"]];
  r = hermiteReduce[shifted["integrand"], bShifted, y, 0];
  tassert["pipeline: shift + hermite with invariant check succeeds",
    AssociationQ[r]];
  tassert["pipeline: round-trip in the shifted frame",
    hermiteRoundTripOK[shifted["integrand"], bShifted, y, r]];
];

tSummary[];
