(* ::Package:: *)

(* ::Title:: *)
(* Tests for reduceIrreducibility *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

(* Quiet the informational message during tests -- we assert on the output *)
(* record, not on whether Message[] was printed.                            *)
Off[IntegrateTrager::autoreduce];

tsection["reduceIrreducibility: already irreducible"];

Module[{r},
  r = reduceIrreducibility[2, x^2 + 1, x];
  tassertEqual["x^2+1, n=2: n unchanged", 2, r["n"]];
  tassertEqual["x^2+1, n=2: g unchanged", x^2 + 1, r["g"]];
  tassertEqual["x^2+1, n=2: yScale = 1", 1, r["yScale"]];
  tassert["x^2+1, n=2: no extension", MissingQ[r["extension"]]];
];

Module[{r},
  r = reduceIrreducibility[3, x^2 + 1, x];
  tassertEqual["x^2+1, n=3: n unchanged", 3, r["n"]];
  tassertEqual["x^2+1, n=3: g unchanged", x^2 + 1, r["g"]];
];

Module[{r},
  r = reduceIrreducibility[3, x^3 - 1, x];
  (* x^3-1 = (x-1)(x^2+x+1); gcd(3, 1, 1) = 1; absolutely irreducible *)
  tassertEqual["x^3-1, n=3: n unchanged", 3, r["n"]];
  tassertEqual["x^3-1, n=3: g unchanged", Expand[x^3 - 1], Expand[r["g"]]];
];

tsection["reduceIrreducibility: exponent reduction mod n"];

Module[{r},
  (* y^2 = x^2 -> y/x satisfies (y/x)^2 = 1; degenerate *)
  r = reduceIrreducibility[2, x^2, x];
  tassertFailure["y^2=x^2 is degenerate after reduction",
    "DegenerateRadical", r];
];

Module[{r},
  (* y^2 = x^3 = x*x^2; exponent 3 mod 2 = 1; yScale = x; g = x *)
  r = reduceIrreducibility[2, x^3, x];
  tassertEqual["y^2=x^3: n=2", 2, r["n"]];
  tassertEqual["y^2=x^3: g = x", x, r["g"]];
  tassertEqual["y^2=x^3: yScale = x", x, r["yScale"]];
];

Module[{r},
  (* y^3 = x^5; exponent 5 mod 3 = 2; yScale = x; g = x^2 *)
  r = reduceIrreducibility[3, x^5, x];
  tassertEqual["y^3=x^5: n=3", 3, r["n"]];
  tassertEqual["y^3=x^5: g = x^2", x^2, Expand[r["g"]]];
  tassertEqual["y^3=x^5: yScale = x", x, r["yScale"]];
];

Module[{r},
  (* y^2 = x^4 * (x^2+1); exponent 4 is absorbed, y_new = y/x^2, g = x^2+1 *)
  r = reduceIrreducibility[2, x^4*(x^2 + 1), x];
  tassertEqual["y^2 = x^4 (x^2+1): reduces to x^2+1", x^2 + 1, Expand[r["g"]]];
  tassertEqual["yScale = x^2", x^2, r["yScale"]];
];

tsection["reduceIrreducibility: gcd-of-exponents reduction"];

Module[{r},
  (* y^4 = (x^2+1)^2; gcd(4,2)=2; reduces to y^2 = x^2+1 *)
  r = reduceIrreducibility[4, (x^2 + 1)^2, x];
  tassertEqual["y^4 = (x^2+1)^2: n reduced to 2", 2, r["n"]];
  tassertEqual["y^4 = (x^2+1)^2: g = x^2+1", x^2 + 1, Expand[r["g"]]];
  tassertEqual["y^4 = (x^2+1)^2: yScale = 1", 1, r["yScale"]];
];

Module[{r},
  (* y^6 = x^2; gcd(6,2)=2; reduces to y^3 = x *)
  r = reduceIrreducibility[6, x^2, x];
  tassertEqual["y^6 = x^2: n reduced to 3", 3, r["n"]];
  tassertEqual["y^6 = x^2: g = x", x, Expand[r["g"]]];
];

Module[{r},
  (* y^6 = x^4; gcd(6,4)=2; reduces to y^3 = x^2 *)
  r = reduceIrreducibility[6, x^4, x];
  tassertEqual["y^6 = x^4: n reduced to 3", 3, r["n"]];
  tassertEqual["y^6 = x^4: g = x^2", x^2, Expand[r["g"]]];
];

Module[{r},
  (* y^4 = 16 (x^2-1)^2; gcd(4,2)=2; c=16 is a square (4^2);             *)
  (*   -> y^2 = 4 (x^2-1)                                                *)
  r = reduceIrreducibility[4, 16 (x^2 - 1)^2, x];
  tassertEqual["y^4 = 16(x^2-1)^2: n -> 2", 2, r["n"]];
  tassertEqual["y^4 = 16(x^2-1)^2: g = 4(x^2-1)",
    Expand[4 (x^2 - 1)], Expand[r["g"]]];
];

tsection["reduceIrreducibility: failure tags"];

Module[{r},
  (* y^4 = 2 (x^2+1)^2; gcd(4,2)=2; c = 2 is NOT a perfect square in Q.   *)
  (* Principal reduced form is y^2 = Sqrt[2] (x^2+1), which requires     *)
  (* Q(Sqrt[2]) as base field -- UnsupportedBaseField.                   *)
  r = reduceIrreducibility[4, 2*(x^2 + 1)^2, x];
  tassertFailure["y^4 = 2(x^2+1)^2: c=2 is not a perfect square",
    "UnsupportedBaseField", r];
];

tassertFailure["n=1 rejected", "NotSimpleRadical",
  reduceIrreducibility[1, x + 1, x]];

On[IntegrateTrager::autoreduce];

tSummary[];
