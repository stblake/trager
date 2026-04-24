(* ::Package:: *)

(* ::Title:: *)
(* Tests for buildIntegralBasis *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

tsection["buildIntegralBasis: quadratic cases (n=2)"];

Module[{b},
  b = buildIntegralBasis[2, x^2 + 1, x];
  tassert["is a basis descriptor", basisDescriptorQ[b]];
  tassertEqual["n = 2", 2, b["n"]];
  tassertEqual["d[0] = 1", 1, b["d"][[1]]];
  tassertEqual["d[1] = 1", 1, b["d"][[2]]];
  tassertEqual["pFactors", {{x^2 + 1, 1}}, b["pFactors"]];
];

Module[{b},
  b = buildIntegralBasis[2, x*(x - 1), x];
  (* pairs {{x, 1}, {x-1, 1}}; d[1] = x^0 (x-1)^0 = 1 *)
  tassertEqual["n=2, g=x(x-1): d[0]=1", 1, b["d"][[1]]];
  tassertEqual["n=2, g=x(x-1): d[1]=1", 1, b["d"][[2]]];
];

tsection["buildIntegralBasis: cubic cases (n=3)"];

Module[{b},
  b = buildIntegralBasis[3, x, x];
  tassertEqual["y^3=x: d[0]=1", 1, b["d"][[1]]];
  tassertEqual["y^3=x: d[1]=1", 1, b["d"][[2]]];
  tassertEqual["y^3=x: d[2]=1", 1, b["d"][[3]]];
];

Module[{b},
  b = buildIntegralBasis[3, x^2, x];
  (* d[i] = x^Floor[2i/3] = {1, 1, x} *)
  tassertEqual["y^3=x^2: d[0]=1", 1, b["d"][[1]]];
  tassertEqual["y^3=x^2: d[1]=1", 1, b["d"][[2]]];
  tassertEqual["y^3=x^2: d[2]=x", x, b["d"][[3]]];
];

Module[{b},
  b = buildIntegralBasis[3, x^2*(1 - x), x];
  (* pairs {{-1,1}? no -- -1 is in the leading; FactorList gives {{-1,1},{x,2},{x-1,1}} *)
  (* So pairs = {{x,2}, {x-1,1}}                                            *)
  (* d[0] = 1                                                               *)
  (* d[1] = x^Floor[2/3] * (x-1)^Floor[1/3] = 1                             *)
  (* d[2] = x^Floor[4/3] * (x-1)^Floor[2/3] = x * 1 = x                     *)
  tassertEqual["y^3=x^2(1-x): d[0]", 1, b["d"][[1]]];
  tassertEqual["y^3=x^2(1-x): d[1]", 1, b["d"][[2]]];
  tassertEqual["y^3=x^2(1-x): d[2]", x, b["d"][[3]]];
];

tsection["buildIntegralBasis: quartic case (n=4)"];

Module[{b},
  b = buildIntegralBasis[4, x^3, x];
  (* d[i] = x^Floor[3i/4] = {1, 1, x, x^2} *)
  tassertEqual["y^4=x^3: d[0]", 1, b["d"][[1]]];
  tassertEqual["y^4=x^3: d[1]", 1, b["d"][[2]]];
  tassertEqual["y^4=x^3: d[2]", x, b["d"][[3]]];
  tassertEqual["y^4=x^3: d[3]", x^2, b["d"][[4]]];
];

tsection["buildIntegralBasis: structural invariants"];

Module[{b, d, n},
  (* d[n-1] should be the LCM of all d[i]. Plan-critical for phase 3.     *)
  b = buildIntegralBasis[4, x^3, x];
  d = b["d"]; n = b["n"];
  tassertEqual["d[n-1] = LCM of all d[i], n=4 example",
    PolynomialLCM @@ d, d[[-1]]];
];

Module[{b, d, n},
  b = buildIntegralBasis[6, x^4 (x + 1)^5, x];
  (* pairs {{x,4}, {x+1,5}}                                                *)
  (* d[i] = x^Floor[4i/6] * (x+1)^Floor[5i/6]                              *)
  d = b["d"]; n = b["n"];
  tassertEqual["d[n-1] = LCM of all d[i], n=6 example",
    PolynomialLCM @@ d, d[[-1]]];
  (* Spot check individual d[i] *)
  tassertEqual["d[0]=1", 1, d[[1]]];
  tassertEqual["d[1]= x^0 (x+1)^0 =1", 1, d[[2]]];
  tassertEqual["d[2]= x^1 (x+1)^1 = x(x+1)",
    Expand[x*(x + 1)], Expand[d[[3]]]];
  tassertEqual["d[3]= x^2 (x+1)^2",
    Expand[x^2*(x + 1)^2], Expand[d[[4]]]];
  tassertEqual["d[4]= x^2 (x+1)^3",
    Expand[x^2*(x + 1)^3], Expand[d[[5]]]];
  tassertEqual["d[5]= x^3 (x+1)^4",
    Expand[x^3*(x + 1)^4], Expand[d[[6]]]];
];

Module[{b, d, n, i},
  (* Monotonic divisibility: d[i] | d[i+1] for all i. *)
  b = buildIntegralBasis[5, x^2 (x - 1)^3 (x + 2)^4, x];
  d = b["d"]; n = b["n"];
  Do[
    tassert["d[" <> ToString[i] <> "] divides d[" <> ToString[i + 1] <> "]",
      PolynomialQ[Cancel[d[[i + 2]] / d[[i + 1]]], x]
    ],
    {i, 0, n - 2}
  ];
];

tSummary[];
