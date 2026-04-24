(* ::Package:: *)

(* ::Title:: *)
(* Phase 1 -- AF element arithmetic primitives *)

(* ::Text:: *)
(* See TragerPlan.md Section 3.                                              *)
(*                                                                           *)
(* An AF ("algebraic function") element represents an element of K(x, y)    *)
(* with y^n = g(x), stored against the Trager integral basis w[i] = y^i/d[i].*)
(* The element is an Association with keys "Type", "Coeffs", "n", "g".       *)
(* Operations that read d[i] also need the basis descriptor; we pass it      *)
(* explicitly rather than embedding it in every element.                    *)

(* ::Section:: *)
(* Constructor and conversions                                               *)

ClearAll[afMake];
afMake[coeffs_List, basis_?basisDescriptorQ] := <|
  "Type"   -> "AF",
  "Coeffs" -> coeffs,
  "n"      -> basis["n"],
  "g"      -> basis["g"]
|>;

(* afFromStandard[expr, basis, y]                                            *)
(* Convert a polynomial expression in y (of degree < n) to AF form.          *)
(* Because the basis is diagonal with w[i] = y^i/d[i], we have               *)
(*   expr = sum_i (c_i / d_i) y^i   ==>   c_i = d_i * Coefficient[expr,y,i]. *)

ClearAll[afFromStandard];
afFromStandard[expr_, basis_?basisDescriptorQ, y_Symbol] := Module[{n, d, c},
  n = basis["n"]; d = basis["d"];
  c = Table[
    Together[d[[i + 1]] * Coefficient[expr, y, i]],
    {i, 0, n - 1}
  ];
  afMake[c, basis]
];

(* afToStandard[af, basis, y]                                                *)
(* Inverse of afFromStandard. Expands an AF element back to an expression   *)
(* in x, y.                                                                  *)

ClearAll[afToStandard];
afToStandard[af_?afElementQ, basis_?basisDescriptorQ, y_Symbol] :=
  Sum[
    af["Coeffs"][[i + 1]] * y^i / basis["d"][[i + 1]],
    {i, 0, basis["n"] - 1}
  ];

(* ::Section:: *)
(* Linear operations                                                         *)

(* afPlus and afMinus are coefficient-wise in K(x). We normalize via Together*)
(* to keep rational coefficients reduced.                                    *)

ClearAll[afPlus];
afPlus[a_?afElementQ, b_?afElementQ, basis_?basisDescriptorQ] := afMake[
  MapThread[Together[#1 + #2] &, {a["Coeffs"], b["Coeffs"]}],
  basis
];

ClearAll[afMinus];
afMinus[a_?afElementQ, b_?afElementQ, basis_?basisDescriptorQ] := afMake[
  MapThread[Together[#1 - #2] &, {a["Coeffs"], b["Coeffs"]}],
  basis
];

ClearAll[afScale];
afScale[k_, a_?afElementQ, basis_?basisDescriptorQ] := afMake[
  Together[k * #] & /@ a["Coeffs"],
  basis
];

(* ::Section:: *)
(* Multiplication                                                            *)

(* afTimes uses the direct in-basis formula                                  *)
(*   w[i] * w[j] = g^q * d[k] / (d[i] d[j]) * w[k]                           *)
(* where k = (i+j) mod n and q = (i+j) div n. By the normality of the       *)
(* Trager basis, d[i] d[j] | d[k]  (when q = 0) and d[i] d[j] | g d[k]       *)
(* (when q = 1), so the multiplier is always in K[x].                        *)

ClearAll[afTimes];
afTimes[a_?afElementQ, b_?afElementQ, basis_?basisDescriptorQ] := Module[
  {n, g, d, aC, bC, outC, i, j, ij, k, q, mult},
  n = basis["n"]; g = basis["g"]; d = basis["d"];
  aC = a["Coeffs"]; bC = b["Coeffs"];
  outC = ConstantArray[0, n];
  Do[
    ij = i + j;
    q = Quotient[ij, n];
    k = Mod[ij, n];
    mult = Together[g^q * d[[k + 1]] / (d[[i + 1]] * d[[j + 1]])];
    outC[[k + 1]] = Together[outC[[k + 1]] + aC[[i + 1]] * bC[[j + 1]] * mult],
    {i, 0, n - 1},
    {j, 0, n - 1}
  ];
  afMake[outC, basis]
];

(* ::Section:: *)
(* Derivative                                                                *)

(* Using y' = g'/(ny) * g/y = g'y^(n-1)/(ng) * 1/y^(n-1) ... the short way:  *)
(*   y' = g'[x] * y / (n g)                                                  *)
(* Substituting into w[i] = y^i/d[i]:                                        *)
(*   w[i]' = w[i] * ( i g'/(n g) - d[i]'/d[i] )                              *)
(* so for an AF element sum c[i] w[i],                                       *)
(*   (sum c[i] w[i])' = sum (c[i]' + c[i] * s[i]) w[i]                       *)
(* with s[i] = i g'/(n g) - d[i]'/d[i].                                      *)

ClearAll[afD];
afD[a_?afElementQ, basis_?basisDescriptorQ] := Module[
  {n, g, d, x, gp, newC, c, di, dip, s},
  n = basis["n"]; g = basis["g"]; d = basis["d"]; x = basis["x"];
  gp = D[g, x];
  newC = Table[
    c   = a["Coeffs"][[i + 1]];
    di  = d[[i + 1]];
    dip = D[di, x];
    s   = i * gp / (n * g) - dip / di;
    Together[D[c, x] + c * s],
    {i, 0, n - 1}
  ];
  afMake[newC, basis]
];

(* ::Section:: *)
(* Norm and trace                                                            *)

(* The multiplication-by-a linear map has matrix M with                      *)
(*   M[j, i] = j-th coefficient of a*w[i] in the basis.                      *)
(* Collecting row-wise (each row = coeffs of a*w[i]) gives M^T; Det and Tr   *)
(* are invariant under transpose, so we use the row-major list directly.    *)

ClearAll[afMultiplicationMatrix];
afMultiplicationMatrix[a_?afElementQ, basis_?basisDescriptorQ] := Module[{n},
  n = basis["n"];
  Table[
    afTimes[a, afMake[UnitVector[n, i + 1], basis], basis]["Coeffs"],
    {i, 0, n - 1}
  ]
];

ClearAll[afNorm];
afNorm[a_?afElementQ, basis_?basisDescriptorQ] :=
  Together[Det[afMultiplicationMatrix[a, basis]]];

ClearAll[afTrace];
afTrace[a_?afElementQ, basis_?basisDescriptorQ] :=
  Together[Tr[afMultiplicationMatrix[a, basis]]];

(* ::Section:: *)
(* Inverse in the AF ring                                                    *)

(* For an irreducible simple-radical relation y^n = g, the ring               *)
(* K(x)[y]/(y^n - g) is a field, so every non-zero AF element has an inverse. *)
(* We compute it by solving M . r = e_0 where M is the multiplication matrix  *)
(* (afMultiplicationMatrix returns its transpose, so we transpose once here). *)

ClearAll[afInverse];
afInverse[a_?afElementQ, basis_?basisDescriptorQ] := Module[{n, M, r},
  n = basis["n"];
  M = Transpose[afMultiplicationMatrix[a, basis]];
  r = LinearSolve[M, UnitVector[n, 1]];
  afMake[Together /@ r, basis]
];
