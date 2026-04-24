(* ::Package:: *)

(* ::Title:: *)
(* Phase 0 -- reduceIrreducibility *)

(* ::Text:: *)
(* See TragerPlan.md Section 2 for the specification.                        *)
(*                                                                           *)
(* Auto-reduces a reducible binomial y^n - g(x) over its algebraic closure   *)
(* to the absolutely irreducible principal factor. The gcd-of-exponents test *)
(* (Capelli-style, simplified because the algebraic closure contains all     *)
(* roots of unity) drives both the mod-n reduction of individual exponents  *)
(* and the overall index reduction.                                          *)

(* ::Section:: *)
(* reduceIrreducibility[n, g, x]                                             *)
(*                                                                           *)
(* Returns an Association with keys "n", "g", "yScale", "extension", or a   *)
(* Failure object on input outside the Q base field.                         *)

ClearAll[reduceIrreducibility];

reduceIrreducibility[n_Integer /; n >= 2, g_, x_Symbol] := Module[
  {factors, c, pairs, yScale, reducedPairs,
   dGcd, cDthRoot, nNew, gNew},

  (* --- Step 1: factor into constant times irreducibles over Q --- *)
  (* FactorList[poly] returns {{content, 1}, {p_1, e_1}, ..., {p_k, e_k}}. *)
  factors = FactorList[g];
  c = factors[[1, 1]];
  pairs = Rest[factors];

  (* --- Step 2: reduce exponents mod n, absorbing into yScale --- *)
  (* For each irreducible factor p^e, write e = n*q + r with 0 <= r < n.    *)
  (* The factor p^(n*q) can be pulled outside the radical as p^q, so the    *)
  (* substitution y_new = y / p^q is applied; yScale accumulates.           *)
  yScale = 1;
  reducedPairs = Reap[
    Do[
      Module[{p = pair[[1]], e = pair[[2]], q, eNew},
        q = Quotient[e, n];
        If[q > 0, yScale = yScale * p^q];
        eNew = Mod[e, n];
        If[eNew > 0, Sow[{p, eNew}]];
      ],
      {pair, pairs}
    ]
  ][[2]];
  reducedPairs = If[reducedPairs === {}, {}, First[reducedPairs]];

  (* --- Step 2a: if everything absorbed, radicand collapsed to constant --- *)
  If[Length[reducedPairs] === 0,
    Return[tragerFailure["DegenerateRadical",
      "Reason" -> "after reducing exponents mod n, radicand is constant",
      "g" -> c, "n" -> n, "yScale" -> yScale
    ]]
  ];

  (* --- Step 3: gcd of n with the (now-reduced) exponents --- *)
  dGcd = GCD[n, Sequence @@ reducedPairs[[All, 2]]];

  If[dGcd === 1,
    (* already absolutely irreducible *)
    Return[<|
      "n" -> n,
      "g" -> Expand[c * Times @@ (#[[1]]^#[[2]] & /@ reducedPairs)],
      "yScale" -> yScale,
      "extension" -> Missing[]
    |>]
  ];

  (* --- Step 4: d > 1; take the principal factor y^(n/d) = alpha --- *)
  (* alpha = c^(1/d) * prod p_i^(e_i/d). If c^(1/d) is not rational, we    *)
  (* would need to work over Q(alpha); that is deferred (see §11), so we   *)
  (* emit UnsupportedBaseField with the concrete reduced form attached.    *)
  cDthRoot = c^(1/dGcd);
  If[!(Head[cDthRoot] === Integer || Head[cDthRoot] === Rational),
    Return[tragerFailure["UnsupportedBaseField",
      "Reason" -> "reduced factor has a leading coefficient outside Q",
      "d" -> dGcd,
      "c" -> c,
      "Suggestion" -> <|
        "n" -> n/dGcd,
        "g" -> Expand[cDthRoot * Times @@ (#[[1]]^(#[[2]]/dGcd) & /@ reducedPairs)],
        "extension" -> cDthRoot
      |>
    ]]
  ];

  nNew = n/dGcd;
  gNew = Expand[cDthRoot * Times @@ (#[[1]]^(#[[2]]/dGcd) & /@ reducedPairs)];
  Message[IntegrateTrager::autoreduce, n, nNew, gNew];

  (* After dividing out dGcd, new exponents gcd with n/d is 1 automatically, *)
  (* so no further iteration of step 3 is needed (see plan §2 note).         *)

  <|
    "n" -> nNew,
    "g" -> gNew,
    "yScale" -> yScale,
    "extension" -> Missing[]
  |>
];

reduceIrreducibility[n_, g_, x_Symbol] :=
  tragerFailure["NotSimpleRadical",
    "Reason" -> "index n must be an integer >= 2",
    "n" -> n
  ];
