(* ::Package:: *)

(* ::Title:: *)
(* Tests for Schultz §4.4 residue formulas (§S.5). *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

tsection["schultzDivisorNorm: basic determinants"];

Module[{basis, triv, norms},
  basis = buildIntegralBasis[2, x^3 + 1, x];
  triv = schultzDivisorTrivial[basis];
  norms = schultzDivisorNorm[triv];
  tassertEqual["finite norm of trivial divisor = 1", 1, norms[[1]]];
  tassertEqual["infinity norm of trivial divisor = 1", 1, norms[[2]]];
];

Module[{basis, d, norms},
  basis = buildIntegralBasis[2, x^3 + 1, x];
  d = schultzDlDivisor[basis, 2];
  norms = schultzDivisorNorm[d];
  tassertEqual["finite norm of D_2 for y²=x³+1 is x³+1",
    x^3 + 1, Together[norms[[1]]]];
  tassertEqual["infinity norm of D_2 for y²=x³+1 is 1/x",
    1/x, Together[norms[[2]]]];
];

tsection["schultzResidueInfinityPoly: Sch §6.2 z² − 324 = 0 (central worked example)"];

Module[{basis, gPoly, b, Acoeffs, dLDiv, polyInf, residues},
  (* y² = x(x+5)(x-4)(x-3). Integrand: (18x+5)·y/b dx with b = g.             *)
  (* Sch page 24 shows the residue polynomial (via eq. 4.11 with r = 1) is    *)
  (* z² − 324 = 0, giving residues ±18 at the two infinity places.            *)
  gPoly = x*(x + 5)*(x - 4)*(x - 3);
  basis = buildIntegralBasis[2, gPoly, x];
  b = Expand[gPoly];
  Acoeffs = {0, 18 x + 5};
  (* The D_1 divisor here has infinity component diag(1/x, 1/x) (both ∞      *)
  (* places have ramification 1). Build it directly since schultzDlDivisor    *)
  (* is restricted to ℓ ≥ 2.                                                  *)
  dLDiv = schultzDivisorMake[
    IdentityMatrix[2],
    {{1/x, 0}, {0, 1/x}},
    basis
  ];
  polyInf = schultzResidueInfinityPoly[Acoeffs, b, 1, dLDiv, basis, zResiduzTest];
  tassertEqual["infinity residue polynomial is proportional to z² − 324",
    0, Together[PolynomialRemainder[polyInf, zResiduzTest^2 - 324, zResiduzTest]]];
  residues = residueValuesFromPoly[polyInf, zResiduzTest];
  tassertEqual["two distinct residues at infinity places",
    2, Length[residues]];
  tassertEqual["residues are ±18",
    {-18, 18}, Sort[residues]];
];

tsection["schultzResidueFinitePoly: branch-place residues vanish (simple radical)"];

Module[{basis, b, Acoeffs, dLDiv, polyFin, residues, stripped},
  (* y² = x² + 1. Integrand: 1/y dx. a_1 = 0, a_2 = 1, b = x²+1.             *)
  (* Branch places are at roots of b (= g). Per Trager Ch 5 §4, branch       *)
  (* places in simple radicals contribute zero residue — eq. 4.10 should     *)
  (* therefore give a z-polynomial with only z^k factors (no nonzero roots). *)
  basis = buildIntegralBasis[2, x^2 + 1, x];
  b = x^2 + 1;
  Acoeffs = {0, 1};
  dLDiv = schultzDlDivisor[basis, 2];
  polyFin = schultzResidueFinitePoly[Acoeffs, b, 2, dLDiv, basis, zResTest];
  residues = residueValuesFromPoly[polyFin, zResTest];
  tassertEqual["branch-place residue polynomial has only zero residues",
    {}, residues];
];

tsection["schultzResidues: driver shape on y² = x³ + 1"];

Module[{basis, result},
  (* Integrand: 1/y dx is regular at finite places (no pole since a_2 = 1,    *)
  (* b ≈ 1 after the Hermite stage — but here we pass a_2 = 1, b = x³+1 to    *)
  (* exercise the driver with a valid Lemma-4.4 input).                       *)
  basis = buildIntegralBasis[2, x^3 + 1, x];
  result = schultzResidues[{0, 1}, x^3 + 1, basis, zz];
  tassert["driver returns association with finite/infinity keys",
    AssociationQ[result] && KeyExistsQ[result, "finite"] &&
      KeyExistsQ[result, "infinity"]];
  tassert["finite residues indexed by ramification",
    AssociationQ[result["finite"]]];
  tassertEqual["only ramification 2 in the key set (y²=x³+1)",
    {2}, Keys[result["finite"]]];
];

(* When b has a root not shared with g, ramification 1 must be probed         *)
(* explicitly even if no factor of g induces a ramification-1 place. The     *)
(* user-reported pipeline failure on ∫(x−1)/((x+1)√(x³+x)) traced to this    *)
(* gap: x = −1 is a non-branch place (g(−1) = −2 ≠ 0) and its residue was   *)
(* dropped, producing a spurious NonElementary verdict.                       *)

Module[{basis, result, b},
  basis = buildIntegralBasis[2, x^3 + x, x];
  b = x*(x + 1)*(x^2 + 1);   (* roots: 0, −1, ±i; g(−1) ≠ 0, so ram-1 needed *)
  result = schultzResidues[{0, x - 1}, b, basis, zz];
  tassert["finite key set includes ramification 1 when b has a non-branch root",
    MemberQ[Keys[result["finite"]], 1]];
];

tSummary[];
