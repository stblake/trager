(* ::Package:: *)

(* ::Title:: *)
(* Phase 0 -- Input validation (validateInput) *)

(* ::Text:: *)
(* See TragerPlan.md Section 2 for the specification. *)

(* ::Section:: *)
(* validateInput *)

(* validateInput[integrand, x, y, relation]                                  *)
(*                                                                           *)
(* Checks that (integrand, relation) is within the simple-radical scope,     *)
(* clears any rational-function denominator from the radicand, and returns   *)
(* a canonicalised record. On malformed input returns a typed Failure.       *)
(*                                                                           *)
(* Return association keys:                                                  *)
(*   "R"     : integrand, y-degree reduced mod the new relation.             *)
(*   "x"     : integration variable (pass-through).                          *)
(*   "y"     : algebraic symbol (pass-through).                              *)
(*   "n"     : integer exponent from the relation.                           *)
(*   "g"     : radicand, now an element of Q[x].                             *)
(*   "scale" : Missing[] when the radicand was already polynomial, or        *)
(*             <|"q" -> q, "exponent" -> n-1|> when we substituted           *)
(*             y_new = q*y to clear a denominator q of g.                    *)

ClearAll[validateInput];

validateInput[integrand_, x_Symbol, y_Symbol, relation_] := Module[
  {n, lhs, rhs, gUser, p, q, gPoly, scale, integrandNew, nonRat, reduced},

  (* --- Step 1: shape of the side relation --- *)
  If[Head[relation] =!= Equal,
    Return[tragerFailure["NotSimpleRadical",
      "Reason" -> "relation is not an Equal expression",
      "Relation" -> relation
    ]]
  ];
  {lhs, rhs} = List @@ relation;
  If[Head[lhs] =!= Power || lhs[[1]] =!= y || !IntegerQ[lhs[[2]]] || lhs[[2]] < 2,
    Return[tragerFailure["NotSimpleRadical",
      "Reason" -> "LHS must be y^n with n an integer >= 2",
      "Relation" -> relation
    ]]
  ];
  n = lhs[[2]];
  gUser = rhs;

  (* --- Step 2: coefficient field check --- *)
  (* g must be a rational function in x with rational coefficients. If the   *)
  (* user supplied AlgebraicNumber[...] or a free symbol, reject.            *)
  If[!rationalFunctionQ[gUser, x],
    nonRat = Cases[{gUser}, s_Symbol /; s =!= x, {0, Infinity}] // Union;
    Return[tragerFailure["UnsupportedBaseField",
      "Reason" -> "radicand is not a rational function over Q in x",
      "g" -> gUser,
      "NonRationalSymbols" -> nonRat
    ]]
  ];

  (* --- Step 3: denominator clearing --- *)
  (* Write g = p/q with q monic. Substitute y -> y_new / q so that           *)
  (* y_new^n = q^n * (p/q) = q^(n-1) * p in Q[x].                            *)
  {p, q} = Through[{Numerator, Denominator}[Together[gUser]]];
  If[zeroQ[q - 1],
    gPoly = p;
    scale = Missing[];
    integrandNew = integrand,
    (* else: clear denominator *)
    gPoly = Expand[q^(n - 1) * p];
    scale = <|"q" -> q, "exponent" -> n - 1|>;
    (* substitute y -> y / q in the integrand so the same symbol y now      *)
    (* satisfies y^n = gPoly. The user's "y" becomes the cleared y_new.     *)
    integrandNew = integrand /. y -> y/q;
    Message[IntegrateTrager::scale, q];
  ];

  (* --- Step 4: degeneracy --- *)
  If[FreeQ[gPoly, x] && PolynomialQ[gPoly, x],
    Return[tragerFailure["DegenerateRadical",
      "Reason" -> "radicand is constant; y^n = c is not a curve",
      "g" -> gPoly,
      "n" -> n
    ]]
  ];

  (* --- Step 5: integrand shape --- *)
  If[!rationalInXYQ[integrandNew, x, y],
    Return[tragerFailure["BadInput",
      "Reason" -> "integrand is not rational in (x, y) over Q",
      "Integrand" -> integrand
    ]]
  ];

  (* --- Step 6: y-degree reduction via y^n -> g --- *)
  (* Repeatedly rewrite y^k with k >= n as y^(k-n) * g. Work on the         *)
  (* numerator and denominator separately so we don't multiply both by the  *)
  (* reduction.                                                              *)
  reduced = reduceYDegree[integrandNew, x, y, n, gPoly];

  <|
    "R" -> reduced,
    "x" -> x,
    "y" -> y,
    "n" -> n,
    "g" -> Expand[gPoly],
    "scale" -> scale
  |>
];

(* reduceYDegree: substitute y^n -> g repeatedly until every y-power is < n. *)
(* The expression is a rational function in x and y; we reduce the numerator *)
(* and denominator (expanded as polynomials in y) separately.                *)

ClearAll[reduceYDegree];
reduceYDegree[expr_, x_Symbol, y_Symbol, n_Integer, g_] := Module[
  {together, num, den, reduceP},
  together = Together[expr];
  num = Numerator[together];
  den = Denominator[together];
  reduceP[poly_] := Module[{p = Expand[poly], changed = True, coeffs, k, maxK},
    While[changed,
      changed = False;
      p = Expand[p];
      coeffs = CoefficientList[p, y];
      maxK = Length[coeffs] - 1;
      If[maxK >= n,
        Do[
          If[coeffs[[k + 1]] =!= 0 && k >= n,
            p = p - coeffs[[k + 1]]*y^k + coeffs[[k + 1]]*y^(k - n)*g;
            changed = True;
          ],
          {k, maxK, n, -1}
        ];
        p = Expand[p];
      ];
    ];
    p
  ];
  Together[reduceP[num] / reduceP[den]]
];
