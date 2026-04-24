(* ::Package:: *)

(* ::Title:: *)
(* Tests for validateInput *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

tsection["validateInput: happy path"];

Module[{r},
  r = validateInput[1/y, x, y, y^2 == x^2 + 1];
  tassert["basic Sqrt[x^2+1]: result is an Association", AssociationQ[r]];
  tassertEqual["basic: n=2", 2, r["n"]];
  tassertEqual["basic: g=x^2+1", x^2 + 1, r["g"]];
  tassertEqual["basic: x passthrough", x, r["x"]];
  tassertEqual["basic: y passthrough", y, r["y"]];
  tassertEqual["basic: R passthrough", 1/y, r["R"]];
  tassert["basic: no scaling applied", MissingQ[r["scale"]]];
];

Module[{r},
  r = validateInput[1/y, x, y, y^3 == x^2 - 1];
  tassertEqual["n=3 case: n=3", 3, r["n"]];
  tassertEqual["n=3 case: g=x^2-1", x^2 - 1, r["g"]];
];

tsection["validateInput: y-degree reduction"];

Module[{r},
  (* y^2 appears in integrand; should be reduced via y^2 -> x^2+1 *)
  r = validateInput[y^2, x, y, y^2 == x^2 + 1];
  tassertEqual["y^2 reduced to g", x^2 + 1, r["R"]];
];

Module[{r},
  r = validateInput[y^3, x, y, y^2 == x^2 + 1];
  (* y^3 = y * y^2 = y * (x^2 + 1) *)
  tassertEqual["y^3 reduced with y^2->g", y*(x^2 + 1), r["R"]];
];

Module[{r},
  r = validateInput[(y^2 + y^4)/(1 + y^2), x, y, y^2 == x^2 + 1];
  (* num y^2 + y^4 = (x^2+1) + (x^2+1)^2 ; den 1 + (x^2+1) = x^2+2         *)
  tassertEqual["rational in y reduced",
    ((x^2 + 1) + (x^2 + 1)^2) / (x^2 + 2),
    r["R"]];
];

tsection["validateInput: rational-radicand denominator clearing"];

Module[{r},
  (* g = 1/x, n = 2  ->  y_new = x*y, g_new = x^(n-1)*num = x*1 = x        *)
  r = validateInput[1/y, x, y, y^2 == 1/x];
  tassertEqual["Sqrt[1/x]: g becomes x", x, r["g"]];
  tassertEqual["Sqrt[1/x]: scale.q = x", x, r["scale"]["q"]];
  tassertEqual["Sqrt[1/x]: scale.exponent = n-1", 1, r["scale"]["exponent"]];
  (* After substitution y -> y/x, the integrand 1/y becomes x/y *)
  tassertEqual["Sqrt[1/x]: integrand rescaled", x/y, r["R"]];
];

Module[{r},
  (* g = (x+1)/(x-1), n = 2                                                *)
  r = validateInput[1, x, y, y^2 == (x + 1)/(x - 1)];
  tassertEqual["g=(x+1)/(x-1): g_new = (x-1)*(x+1)",
    Expand[(x - 1)*(x + 1)], r["g"]];
  tassertEqual["scale.q = x-1", x - 1, r["scale"]["q"]];
];

tsection["validateInput: failure tags"];

tassertFailure["NotSimpleRadical: wrong head", "NotSimpleRadical",
  validateInput[1, x, y, 42]];

tassertFailure["NotSimpleRadical: n=1", "NotSimpleRadical",
  validateInput[1, x, y, y^1 == x + 1]];

tassertFailure["NotSimpleRadical: LHS not y^n", "NotSimpleRadical",
  validateInput[1, x, y, (2 y)^2 == x + 1]];

tassertFailure["UnsupportedBaseField: irrational coeff", "UnsupportedBaseField",
  validateInput[1, x, y, y^2 == x^2 + Sqrt[2]]];

tassertFailure["DegenerateRadical: constant radicand", "DegenerateRadical",
  validateInput[1, x, y, y^2 == 4]];

tassertFailure["DegenerateRadical: radicand = 0", "DegenerateRadical",
  validateInput[1, x, y, y^2 == 0]];

tassertFailure["BadInput: transcendental integrand", "BadInput",
  validateInput[Exp[x]/y, x, y, y^2 == x^2 + 1]];

tSummary[];
