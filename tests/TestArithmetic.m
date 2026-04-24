(* ::Package:: *)

(* ::Title:: *)
(* Tests for AF arithmetic primitives *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

(* Helper: convert two AF elements, check they agree in standard form. *)
afEqualQ[a_, b_, basis_, y_Symbol] :=
  TrueQ[Simplify[afToStandard[a, basis, y] - afToStandard[b, basis, y]] === 0];

tsection["afFromStandard / afToStandard: round-trip"];

Module[{basis, a, expr},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  (* expr polynomial in y of degree < 2 *)
  expr = (3 x^2) + (x + 1)/(x - 1) * y;
  a = afFromStandard[expr, basis, y];
  tassertEqual["n=2: AF coeffs match direct formula",
    {3 x^2, (x + 1)/(x - 1)},
    a["Coeffs"]];
  tassertEqual["n=2: round-trip via afToStandard",
    expr,
    afToStandard[a, basis, y]];
];

Module[{basis, a, expr},
  basis = buildIntegralBasis[3, x^2, x];
  (* d = {1, 1, x}. expr = 1 + 2y + 3y^2 *)
  expr = 1 + 2 y + 3 y^2;
  a = afFromStandard[expr, basis, y];
  tassertEqual["n=3 with d[2]=x: c[0]=1", 1, a["Coeffs"][[1]]];
  tassertEqual["n=3 with d[2]=x: c[1]=2", 2, a["Coeffs"][[2]]];
  tassertEqual["n=3 with d[2]=x: c[2]=3x", 3 x, a["Coeffs"][[3]]];
  tassertEqual["n=3: round-trip",
    expr, Expand[afToStandard[a, basis, y]]];
];

Module[{basis, a, expr},
  basis = buildIntegralBasis[4, x^3, x];
  (* d = {1, 1, x, x^2} *)
  expr = x + y + y^2 + y^3;
  a = afFromStandard[expr, basis, y];
  tassertEqual["n=4: c[0]", x, a["Coeffs"][[1]]];
  tassertEqual["n=4: c[1]", 1, a["Coeffs"][[2]]];
  tassertEqual["n=4: c[2] = x*1 = x", x, a["Coeffs"][[3]]];
  tassertEqual["n=4: c[3] = x^2*1 = x^2", x^2, a["Coeffs"][[4]]];
  tassertEqual["n=4: round-trip",
    expr, Expand[afToStandard[a, basis, y]]];
];

tsection["afPlus / afMinus"];

Module[{basis, a, b, s, d},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  a = afFromStandard[1 + y, basis, y];
  b = afFromStandard[x y - 1, basis, y];
  s = afPlus[a, b, basis];
  d = afMinus[a, b, basis];
  tassertEqual["afPlus: standard form",
    Expand[(1 + y) + (x y - 1)], Expand[afToStandard[s, basis, y]]];
  tassertEqual["afMinus: standard form",
    Expand[(1 + y) - (x y - 1)], Expand[afToStandard[d, basis, y]]];
];

tsection["afTimes: y * y^(n-1) = g (plan invariant)"];

Module[{basis, yEl, yn1, prod},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  yEl = afFromStandard[y, basis, y];
  yn1 = afFromStandard[y^1, basis, y];       (* n-1 = 1 here *)
  prod = afTimes[yEl, yn1, basis];
  tassertEqual["n=2: y*y = g (coeff form)",
    {x^2 + 1, 0}, prod["Coeffs"]];
  tassertEqual["n=2: y*y = g (standard form)",
    x^2 + 1, afToStandard[prod, basis, y]];
];

Module[{basis, yEl, yn1, prod},
  basis = buildIntegralBasis[3, x, x];
  yEl = afFromStandard[y, basis, y];
  yn1 = afFromStandard[y^2, basis, y];
  prod = afTimes[yEl, yn1, basis];
  tassertEqual["n=3: y*y^2 = x", {x, 0, 0}, prod["Coeffs"]];
];

Module[{basis, yEl, yn1, prod},
  basis = buildIntegralBasis[4, x^3, x];
  yEl = afFromStandard[y, basis, y];
  yn1 = afFromStandard[y^3, basis, y];
  prod = afTimes[yEl, yn1, basis];
  (* y * y^3 = y^4 = g = x^3 *)
  tassertEqual["n=4: y*y^3 = x^3",
    x^3, afToStandard[prod, basis, y]];
];

tsection["afTimes: cross-check against standard-form multiplication"];

Module[{basis, a, b, prod, expected},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  a = afFromStandard[1 + x y, basis, y];
  b = afFromStandard[x - y, basis, y];
  prod = afTimes[a, b, basis];
  expected =
    PolynomialReduce[Expand[(1 + x y)(x - y)], {y^2 - (x^2 + 1)}, {y}][[2]];
  tassertEqual["(1+xy)(x-y) n=2",
    Expand[expected], Expand[afToStandard[prod, basis, y]]];
];

Module[{basis, a, b, prod, expected},
  basis = buildIntegralBasis[3, x^2, x];
  a = afFromStandard[1 + y + y^2, basis, y];
  b = afFromStandard[1 - y, basis, y];
  prod = afTimes[a, b, basis];
  (* Expected: (1+y+y^2)(1-y) = 1 - y^3 = 1 - x^2 (since y^3 = x^2) *)
  tassertEqual["(1+y+y^2)(1-y) = 1 - x^2 on y^3=x^2",
    1 - x^2, Expand[afToStandard[prod, basis, y]]];
];

tsection["afTimes: commutativity and distributivity"];

Module[{basis, a, b, c, ab, ba, aBcPlusC, abPlusAc},
  basis = buildIntegralBasis[3, x^2, x];
  a = afFromStandard[1 + x y, basis, y];
  b = afFromStandard[x - y^2, basis, y];
  c = afFromStandard[x^2 + 3 y, basis, y];
  ab = afTimes[a, b, basis];
  ba = afTimes[b, a, basis];
  tassert["commutativity: a*b == b*a", afEqualQ[ab, ba, basis, y]];

  aBcPlusC = afTimes[a, afPlus[b, c, basis], basis];
  abPlusAc = afPlus[afTimes[a, b, basis], afTimes[a, c, basis], basis];
  tassert["distributivity: a*(b+c) == a*b + a*c",
    afEqualQ[aBcPlusC, abPlusAc, basis, y]];
];

tsection["afD: scalar-multiple formula for w[i]"];

Module[{basis, a, b, expected},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  a = afFromStandard[y, basis, y];
  b = afD[a, basis];
  (* Expected y' = g' y / (n g) = 2x * y / (2 (x^2+1)) = x y / (x^2+1)  *)
  expected = x y / (x^2 + 1);
  tassertEqual["afD[y] with y^2=x^2+1",
    expected, Together[afToStandard[b, basis, y]]];
];

Module[{basis, a, b, expected},
  basis = buildIntegralBasis[3, x, x];
  a = afFromStandard[y, basis, y];
  b = afD[a, basis];
  (* y' = g' y / (n g) = 1 * y / (3 x) = y / (3 x) *)
  expected = y / (3 x);
  tassertEqual["afD[y] with y^3=x",
    expected, Together[afToStandard[b, basis, y]]];
];

Module[{basis, a, b, expected},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  (* derivative of a constant = 0 *)
  a = afFromStandard[x + 1, basis, y];
  b = afD[a, basis];
  tassertEqual["afD[x+1] = 1",
    1, Together[afToStandard[b, basis, y]]];
];

tsection["afD: Leibniz rule"];

Module[{basis, a, b, lhs, rhs},
  basis = buildIntegralBasis[3, x^2, x];
  a = afFromStandard[1 + x y, basis, y];
  b = afFromStandard[x - y^2, basis, y];
  lhs = afD[afTimes[a, b, basis], basis];
  rhs = afPlus[
    afTimes[afD[a, basis], b, basis],
    afTimes[a, afD[b, basis], basis],
    basis
  ];
  tassert["Leibniz (a*b)' = a'b + ab' on n=3 case",
    afEqualQ[lhs, rhs, basis, y]];
];

Module[{basis, a, b, lhs, rhs},
  basis = buildIntegralBasis[4, x^3, x];
  a = afFromStandard[1 + y + y^3, basis, y];
  b = afFromStandard[x + y^2, basis, y];
  lhs = afD[afTimes[a, b, basis], basis];
  rhs = afPlus[
    afTimes[afD[a, basis], b, basis],
    afTimes[a, afD[b, basis], basis],
    basis
  ];
  tassert["Leibniz on n=4 case", afEqualQ[lhs, rhs, basis, y]];
];

tsection["afNorm, afTrace"];

Module[{basis, a, N, T},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  a = afFromStandard[y, basis, y];
  N = afNorm[a, basis]; T = afTrace[a, basis];
  (* Norm(y) for y^n = g is (-1)^(n+1) g; n=2 -> -g *)
  tassertEqual["afNorm[y] n=2 = -g", -(x^2 + 1), Expand[N]];
  tassertEqual["afTrace[y] n=2 = 0", 0, T];
];

Module[{basis, a, N, T},
  basis = buildIntegralBasis[3, x, x];
  a = afFromStandard[y, basis, y];
  N = afNorm[a, basis]; T = afTrace[a, basis];
  tassertEqual["afNorm[y] n=3 = g", x, Expand[N]];
  tassertEqual["afTrace[y] n=3 = 0", 0, T];
];

Module[{basis, a, N, T},
  basis = buildIntegralBasis[4, x^3, x];
  a = afFromStandard[y, basis, y];
  N = afNorm[a, basis]; T = afTrace[a, basis];
  (* n=4: Norm(y) = (-1)^5 g = -g = -x^3 *)
  tassertEqual["afNorm[y] n=4 = -g", -x^3, Expand[N]];
  tassertEqual["afTrace[y] n=4 = 0", 0, T];
];

Module[{basis, a, N, T},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  (* Constant element: norm of c is c^n, trace is n c *)
  a = afFromStandard[3 x, basis, y];
  tassertEqual["afNorm[3x] n=2 = 9 x^2", 9 x^2, Expand[afNorm[a, basis]]];
  tassertEqual["afTrace[3x] n=2 = 6x", 6 x, Expand[afTrace[a, basis]]];
];

Module[{basis, a},
  basis = buildIntegralBasis[3, x, x];
  a = afFromStandard[7, basis, y];
  tassertEqual["afNorm[7] n=3 = 343", 343, afNorm[a, basis]];
  tassertEqual["afTrace[7] n=3 = 21", 21, afTrace[a, basis]];
];

tsection["afNorm: multiplicativity"];

Module[{basis, a, b, na, nb, nab},
  basis = buildIntegralBasis[3, x^2, x];
  a = afFromStandard[1 + x y, basis, y];
  b = afFromStandard[x - y^2, basis, y];
  na = afNorm[a, basis];
  nb = afNorm[b, basis];
  nab = afNorm[afTimes[a, b, basis], basis];
  tassertEqual["Norm(ab) = Norm(a) Norm(b)",
    Expand[na * nb], Expand[nab]];
];

tSummary[];
