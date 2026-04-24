(* ::Package:: *)

(* ::Title:: *)
(* Tests for computeResidues *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

(* Helper: compare two sets as multisets via Sort. *)
sameSetQ[a_List, b_List] := Sort[a] === Sort[b];

tsection["computeResidues: y/x on y^2 = x^2+1 (rational residues \\[PlusMinus]1)"];

Module[{b, r, res},
  b = buildIntegralBasis[2, x^2 + 1, x];
  r = hermiteReduce[y/x, b, y];
  res = computeResidues[r["remainder"], r["D"], b, y, Z];
  tassertEqual["R = Z^2 - 1", -1 + Z^2, res["R"]];
  tassertEqual["Zstrip = 0 (no zero-residue places)", 0, res["Zstrip"]];
  tassert["residues are {+1, -1}",
    sameSetQ[res["residues"], {1, -1}]];
  tassertEqual["qBasis = {1} (rational span)", {1}, res["qBasis"]];
  tassert["basisCoeffs match residues in order",
    MapThread[# === {#2} &, {res["basisCoeffs"], res["residues"]}] // AllTrue[#, TrueQ] &];
];

tsection["computeResidues: 1/(x y) on y^2 = x^2+1 (Z^k strip)"];

Module[{b, r, res},
  b = buildIntegralBasis[2, x^2 + 1, x];
  r = hermiteReduce[1/(x*y), b, y];
  res = computeResidues[r["remainder"], r["D"], b, y, Z];
  tassert["Zstrip > 0 (branch places contribute zero residues)",
    res["Zstrip"] > 0];
  tassertEqual["R (stripped) = Z^2 - 1", -1 + Z^2, res["R"]];
  tassert["residues = {+1, -1}",
    sameSetQ[res["residues"], {1, -1}]];
  tassertEqual["qBasis = {1}", {1}, res["qBasis"]];
];

tsection["computeResidues: algebraic residues (Q(\\[Sqrt]6))"];

Module[{b, r, res, resSet},
  (* y/(x^2 - 2) on y^2 = x^2+1. Places at x = \\[PlusMinus]\\[Sqrt]2.    *)
  (* At each, y = \\[PlusMinus]\\[Sqrt]3. Residue = y/(2x):                *)
  (*   \\[Sqrt]3/(2\\[Sqrt]2)  =  \\[Sqrt]6/4                              *)
  (* Four places total, distinct residues \\[PlusMinus]\\[Sqrt]6/4.        *)
  b = buildIntegralBasis[2, x^2 + 1, x];
  r = hermiteReduce[y/(x^2 - 2), b, y];
  res = computeResidues[r["remainder"], r["D"], b, y, Z];

  tassertEqual["R = (8Z^2 - 3)^2 = 64 Z^4 - 48 Z^2 + 9",
    9 - 48 Z^2 + 64 Z^4, Expand[res["R"]]];
  tassertEqual["residues are 2 distinct numbers",
    2, Length[res["residues"]]];
  tassertEqual["qBasis is 1-dimensional (span is Q*Sqrt[6])",
    1, Length[res["qBasis"]]];
  (* Each residue should equal \\[PlusMinus](1/4) Sqrt[6] *)
  resSet = Simplify[res["residues"] - {-1, 1} * Sqrt[6]/4];
  tassert["residues are +/- Sqrt[6]/4 (in some order)",
    sameSetQ[Simplify[res["residues"]^2], {3/8, 3/8}]];
];

tsection["computeResidues: factor-by-factor vs single-resultant cross-check"];

Module[{b, r, res, expected, innerRes, Gpoly, Bfull, Bprime, Rmanual,
        dmax, g},
  (* Verify our factor-by-factor implementation against a plain single     *)
  (* resultant on a straightforward case.                                  *)
  b = buildIntegralBasis[2, x^2 + 1, x];
  g = b["g"]; dmax = Last[b["d"]];
  r = hermiteReduce[y/(x*(x - 3)), b, y];
  res = computeResidues[r["remainder"], r["D"], b, y, Z];

  Gpoly = Expand[afToStandard[r["remainder"], b, y] * r["D"] * dmax];
  Bfull = Expand[r["D"] * dmax];
  Bprime = D[Bfull, x];
  Rmanual = Expand[
    Resultant[Resultant[Z*Bprime - Gpoly, y^2 - g, y], Bfull, x]
  ];
  tassert["factor-by-factor R matches single-resultant R (up to constant)",
    Module[{ratio = Together[res["Rraw"] / Rmanual]},
      FreeQ[ratio, Z] && ratio =!= 0
    ]];
];

tsection["computeResidues: Q-basis spans residues with correct coefficients"];

Module[{b, r, res, reconstructed, diff},
  b = buildIntegralBasis[2, x^2 + 1, x];
  r = hermiteReduce[y/(x^2 - 2), b, y];
  res = computeResidues[r["remainder"], r["D"], b, y, Z];

  (* Reconstruct residues from basisCoeffs \\[CenterDot] qBasis. Compare    *)
  (* via RootReduce -- robust across mixed Sqrt / AlgebraicNumber forms.    *)
  reconstructed = Table[
    Total[MapThread[Times, {res["basisCoeffs"][[i]], res["qBasis"]}]],
    {i, Length[res["residues"]]}
  ];
  diff = RootReduce /@ (reconstructed - res["residues"]);
  tassert["reconstructed residues == declared residues",
    AllTrue[diff, TrueQ[# === 0] &]];
];

tsection["computeResidues: pipeline integration with phase 2 + 3"];

Module[{shift, bShifted, hermRes, res},
  (* 1/sqrt(x^2 - 1) needs the infinity shift: pre-shift R has no nontrivial*)
  (* residues (all log-residue is at infinity); post-shift residues are     *)
  (* \\[PlusMinus]1 at z = 0 (the former infinity).                         *)
  shift = shiftAwayFromInfinity[1/y, x, y, 2, x^2 - 1, z];
  bShifted = buildIntegralBasis[shift["n"], shift["g"], shift["z"]];
  hermRes = hermiteReduce[shift["integrand"], bShifted, y, 0];
  res = computeResidues[hermRes["remainder"], hermRes["D"], bShifted, y, Z];
  tassert["pipeline residues = {+1, -1}",
    sameSetQ[res["residues"], {1, -1}]];
  tassertEqual["pipeline qBasis = {1} (rational)", {1}, res["qBasis"]];
];

tSummary[];
