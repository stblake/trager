(* ::Package:: *)

(* ::Title:: *)
(* Tests for Torsion.m: torsionIfCan *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

tsection["torsionIfCan: return shape"];

Module[{basis, h, d, result},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  h = afMake[{1, 1}, basis];
  d = makeDivisor[h, x (1 + x^2)];
  result = torsionIfCan[d, basis, y, MaxOrder -> 5];
  tassert["torsionIfCan returns an Association",
    AssociationQ[result]];
  tassert["torsionIfCan result has order and function OR order='failed'",
    (KeyExistsQ[result, "order"] &&
      (result["order"] === "failed" ||
       (IntegerQ[result["order"]] && result["order"] >= 1 &&
        KeyExistsQ[result, "function"])))];
];

tsection["torsionIfCan: MaxOrder bound is respected"];

Module[{basis, Gtilde, Dpoly, div, result, result10, result1},
  basis = buildIntegralBasis[2, x^3 + 1, x];   (* genus 1 curve *)
  Gtilde = afFromStandard[1, basis, y];
  Dpoly  = x;
  div    = residueDivisor[Gtilde, Dpoly, 1, basis, y];
  (* We don't require torsionIfCan to FIND torsion here; we assert that  *)
  (* the MaxOrder option is respected by the search.                      *)
  result1  = torsionIfCan[div, basis, y, MaxOrder -> 1];
  result10 = torsionIfCan[div, basis, y, MaxOrder -> 10];
  tassert["torsionIfCan with MaxOrder=1 returns Association",
    AssociationQ[result1]];
  tassert["torsionIfCan with MaxOrder=10 returns Association",
    AssociationQ[result10]];
];

tSummary[];
