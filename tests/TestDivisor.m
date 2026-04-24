(* ::Package:: *)

(* ::Title:: *)
(* Tests for Divisor.m: data structure and arithmetic *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

Off[IntegrateTrager::autoreduce];

tsection["divisor: constructor and predicates"];

Module[{basis, h, d},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  h = afMake[{1, 2}, basis];
  d = makeDivisor[h, x];
  tassert["makeDivisor produces divisor-predicate-true",
    divisorQ[d]];
  tassert["divisor has Type=Divisor",
    d["Type"] === "Divisor"];
  tassert["divisor stores h as AF element",
    afElementQ[d["h"]] && d["h"] === h];
  tassert["divisor stores A as polynomial",
    d["A"] === x];
];

tsection["divisor: residueDivisor construction"];

Module[{basis, Gtilde, Dpoly, div, normAtPlace},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  Gtilde = afFromStandard[-y, basis, y];
  Dpoly  = x (1 + x^2);
  div    = residueDivisor[Gtilde, Dpoly, 1, basis, y];
  tassert["residueDivisor returns a divisor-predicate-true object",
    divisorQ[div]];
  tassert["residueDivisor A matches Dpoly",
    TrueQ[Together[div["A"] - Dpoly] === 0]];
  (* After simplify + lucky-integer reduce (Trager 1984 Ch 5 §3), h is a *)
  (* cleaned representative of the divisor. For this input, D1 = x       *)
  (* (x-projection of supp), and the lucky-integer j = 1 yields h =     *)
  (* (x - 1) - y, whose norm has DD-part of degree exactly malpha = 1.   *)
  tassert["residueDivisor h coefficient c_0 is x-1",
    TrueQ[Together[div["h"]["Coeffs"][[1]] - (x - 1)] === 0]];
  tassert["residueDivisor h coefficient c_1 is -1",
    TrueQ[Together[div["h"]["Coeffs"][[2]] - (-1)] === 0]];
  (* Divisor invariant: h vanishes at the expected support place (0, -1) *)
  (* where y_0 = -1 satisfies y^2 = g(0) = 1 and residue = -y_0/D'(0) = 1. *)
  normAtPlace = Together[(div["h"]["Coeffs"][[1]] + div["h"]["Coeffs"][[2]] * (-1)) /. x -> 0];
  tassert["residueDivisor h vanishes at support place (0, -1)",
    TrueQ[normAtPlace === 0]];
];

tsection["divisor: arithmetic consistency"];

Module[{basis, h1, h2, d1, d2, A, dSum, dNeg, dSub},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  h1 = afMake[{1, 1}, basis];         (* 1 + y *)
  h2 = afMake[{2, 0}, basis];         (* 2 *)
  A  = x;
  d1 = makeDivisor[h1, A];
  d2 = makeDivisor[h2, A];
  dSum = divisorAdd[d1, d2, basis];
  dNeg = divisorNegate[d1, basis];
  dSub = divisorSubtract[d1, d2, basis];
  (* Divisor addition multiplies both h AND A together, so the resulting *)
  (* A is A_1 * A_2 (since supp(D_1 + D_2) ⊆ V(A_1·A_2)). Keeping A_new  *)
  (* = A alone would give an over-large K[z]-module at positive-support  *)
  (* places and let verification-false candidates survive the HNF.       *)
  tassert["divisor addition multiplies A (A_sum = A_1 * A_2)",
    TrueQ[Together[dSum["A"] - A^2] === 0]];
  tassert["divisor negate returns divisor",
    divisorQ[dNeg]];
  tassert["divisor subtract returns divisor",
    divisorQ[dSub]];
];

Module[{basis, h, A, d, dScale},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  h = afMake[{1, 1}, basis];         (* 1 + y *)
  A = x;
  d = makeDivisor[h, A];
  dScale = divisorScale[2, d, basis];
  tassert["divisorScale[2, d] returns divisor",
    divisorQ[dScale]];
  (* divisorScale[2, d] with A_new = A^2 = x^2 triggers simplifyHModA on  *)
  (* h^2 = (2+x^2) + 2y; the canonical representative modulo A^2 = x^2    *)
  (* has c_0 = 2 (x^2 is replaced by 0 mod x^2) and c_1 = 2.              *)
  tassert["divisorScale[2, d] A equals A^2",
    TrueQ[Together[dScale["A"] - x^2] === 0]];
  tassert["divisorScale[2, d] h c_1 is 2",
    TrueQ[Together[dScale["h"]["Coeffs"][[2]] - 2] === 0]];
];

tsection["divisor: mixed support now multiplies (no more Failure)"];

Module[{basis, h1, h2, d1, d2, result},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  h1 = afMake[{1, 1}, basis];
  h2 = afMake[{1, 1}, basis];
  d1 = makeDivisor[h1, x];
  d2 = makeDivisor[h2, x + 1];
  result = divisorAdd[d1, d2, basis];
  (* Mismatched support used to fail with DivisorAddMismatchedSupport;    *)
  (* the new ideal-multiplication semantics handles it natively, with    *)
  (* A_sum = A_1 * A_2 capturing the union of supports.                   *)
  tassert["divisorAdd on mixed A multiplies the A polynomials",
    divisorQ[result] &&
    TrueQ[Together[result["A"] - x*(x + 1)] === 0]];
];

tSummary[];
