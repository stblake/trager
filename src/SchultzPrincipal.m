(* ::Package:: *)

(* ::Title:: *)
(* Schultz 2015 Lemma 4.1 -- Riemann-Roch space and principal-generator test *)

(* ::Text:: *)
(* See Sch §4.1 (pp. 8-10) Lemma 4.1.                                          *)
(*                                                                              *)
(* For a Schultz divisor D represented as (aFin, aInf) on the curve y^n = g(x):*)
(*                                                                              *)
(*    R(D) := D^∞ ∩ D_∞ = { f ∈ K : ord_P(f) ≥ ord_P(D) at every place P }   *)
(*                                                                              *)
(* is a finite-dimensional k-vector space (the "Riemann-Roch space" of the     *)
(* dual divisor). Lemma 4.1 says there are k[x]-bases {φ_i} of D^∞ and         *)
(* k[[1/x]]-bases {ψ_i} of D_∞ such that ψ_i = x^{−d_i} φ_i for unique         *)
(* integer "exponents" d_i (up to permutation), and                             *)
(*                                                                              *)
(*    R(D) has k-basis  { x^j φ_i : 1 ≤ i ≤ n,  0 ≤ j ≤ −d_i }.                *)
(*                                                                              *)
(* For a divisor D of degree 0, dim_k R(D) ≤ 1, with equality iff D is        *)
(* principal — and in that case R(D) = k · F where F is a principal generator *)
(* (a function with div(F) = −D).                                               *)
(*                                                                              *)
(* This module computes R(D) directly by linear algebra over k, without going *)
(* through the basis-alignment machinery of Lemma 4.1: we parametrise          *)
(* candidate elements f = a · aFin (η-coords) with a ∈ k[x]^n of bounded       *)
(* degree, impose the f ∈ D_∞ condition as the linear constraint               *)
(*    a · T  ∈  k[[1/x]]^n,    T := aFin · diag(x^δ) · aInf^{-1},              *)
(* and solve over k. The non-trivial null vectors give a k-basis of R(D).      *)
(*                                                                              *)
(* The convention (consistent with src/SchultzDivisor.m and Sch §4.1):         *)
(*   • aFin row i = a k[x]-basis element of D^∞ in η-coords (η_i = w_{i-1}).   *)
(*   • aInf row i = a k[[1/x]]-basis element of D_∞ in (η · x^{-δ})-coords,    *)
(*     i.e. row j of aInf · diag(x^{-δ}) is the same basis element in η-coords.*)
(*                                                                              *)
(* Polynomial-degree bound. The parameter `CDeg` for deg(a_i) is set to        *)
(*   max_{i,j} (−v_∞(T[i, j])),                                                 *)
(* the largest positive-x degree appearing in any entry of T. This is          *)
(* sufficient: any f ∈ R(D) has v_∞(f's η-coord) ≥ ord at infinity, and       *)
(* the budget for polynomial growth in a is exactly the gap between the        *)
(* polynomial parts of T's columns and the v_∞ ≥ 0 target. We retry with       *)
(* a generous over-estimate (× 2) once if the initial null-space search        *)
(* terminates too tight — but in practice MMax is the right bound for          *)
(* well-formed Schultz divisors.                                                *)

(* ::Section:: *)
(* schultzRiemannRoch -- compute k-basis of R(D)                               *)
(*                                                                              *)
(* Inputs:                                                                      *)
(*   d         - Schultz divisor (with "aFin", "aInf", "basis" keys).           *)
(*                                                                              *)
(* Options:                                                                     *)
(*   "DegreeOverride" -> Automatic | integer                                    *)
(*       Force a specific degree budget for a_i (overrides MMax). Use to        *)
(*       diagnose / extend search; default Automatic = MMax.                    *)
(*   "DegreeBuffer" -> nonnegative integer (default 0)                          *)
(*       Add this to the auto-computed MMax. Useful when the Lemma 4.1          *)
(*       d_i values are not all bounded by MMax (rare on well-conditioned       *)
(*       inputs but worth having).                                              *)
(*                                                                              *)
(* Output: a list of AF elements forming a k-basis of R(D).                     *)
(*   • Empty list ⇔ R(D) = {0}.                                                 *)
(*   • Single-element list ⇔ R(D) is one-dimensional.                           *)
(*   • Multi-element list ⇔ R(D) has dimension > 1 (e.g. when deg(D) is         *)
(*     positive and large enough that R(D) carries multiple independent         *)
(*     sections by Riemann–Roch).                                               *)

ClearAll[schultzRiemannRoch];
Options[schultzRiemannRoch] = {
  "DegreeOverride" -> Automatic,
  "DegreeBuffer"   -> 0
};

schultzRiemannRoch[d_?schultzDivisorQ, OptionsPattern[]] := Module[
  {basis, x, n, deltas, aFin, aInf, BInv, T, MMax, CDegOpt, CDeg,
   uvars, aPoly, constraintEqs, MtxConstraints, ns, basisAFs,
   Tnum, Tden, colDen},

  basis = d["basis"];
  x = basis["x"]; n = basis["n"]; deltas = basis["deltas"];
  aFin = d["aFin"]; aInf = d["aInf"];

  (* T = aFin · diag(x^δ) · aInf^{-1}.                                          *)
  (* Sch §4.1 / Lemma 4.1: the d_i exponents and R(D) k-basis are read off     *)
  (* from this single n × n matrix in k(x).                                     *)
  BInv = Inverse[aInf];
  T = Table[
    Together[Sum[
      aFin[[i, k]] * x^deltas[[k]] * BInv[[k, j]],
      {k, 1, n}
    ]],
    {i, n}, {j, n}
  ];

  (* MMax = max positive-x degree across T entries.                              *)
  MMax = Module[{degs},
    degs = Flatten @ Table[
      If[zeroQ[T[[i, j]]], -10^9, -valInfinity[T[[i, j]], x]],
      {i, n}, {j, n}
    ];
    Max[0, Max[degs]]
  ];

  (* Choose degree budget. Override > Auto = MMax + buffer.                      *)
  CDegOpt = OptionValue["DegreeOverride"];
  CDeg = Which[
    IntegerQ[CDegOpt] && CDegOpt >= 0, CDegOpt,
    True, MMax + OptionValue["DegreeBuffer"]
  ];

  (* Allocate variables u[i, k] for i = 1..n, k = 0..CDeg.                       *)
  uvars = Flatten @ Table[uVar[i, k], {i, n}, {k, 0, CDeg}];

  (* a_i(x) = Σ_{k=0}^{CDeg} u[i, k] x^k.                                        *)
  aPoly = Table[
    Sum[uVar[i, k] * x^k, {k, 0, CDeg}],
    {i, n}
  ];

  (* Performance optimization (Series-at-infinity). For each entry T[i, j],   *)
  (* expand at x = ∞ to depth `MMax + 1` (capturing all positive-x powers).    *)
  (* The result is a Laurent polynomial in x (terms x^k for k from MMax down  *)
  (* to −1 for our purposes — we only care about k ≥ 1). Then                 *)
  (*    β_j = Σ_i a_i · series(T[i, j])                                         *)
  (* is a Laurent polynomial in x with coefficients linear in the u-variables. *)
  (* Extracting the k ≥ 1 coefficients gives the constraints directly, no      *)
  (* Together / PolynomialQuotient needed. This is dramatically faster on      *)
  (* high-c torsion divisors whose explicit T entries can have polynomial      *)
  (* numerators/denominators of degree 200+: with the Series-truncation we     *)
  (* sidestep that bulk entirely, working only with the (CDeg + 1)-term        *)
  (* Laurent prefixes that govern the ord-at-infinity constraints.              *)

  Tnum = Null;  (* unused in series path *)
  Tden = Null;

  Module[{seriesDepth, Tser},
    seriesDepth = MMax + 1;  (* terms from x^{MMax} down to x^{-1}: depth +1 *)
    (* Series expansion of T at infinity for each entry. Convert series to     *)
    (* Normal form (a Laurent polynomial in x).                                 *)
    Tser = Map[
      Normal[Series[#, {x, Infinity, seriesDepth}]] &,
      T, {2}
    ];

    constraintEqs = Flatten @ Table[
      Module[{betaJ, coefList, i},
        betaJ = Sum[aPoly[[i]] * Tser[[i, j]], {i, n}];
        (* β_j as a Laurent polynomial in x (with linear-in-u coefficients).   *)
        (* We need coefficients of x^k for k ≥ 1 to vanish.                     *)
        (* Use CoefficientList for non-negative powers; for negative powers we *)
        (* don't care (they live in k[[1/x]]). To handle Laurent, expand.       *)
        betaJ = Expand[betaJ];
        Module[{maxDeg, k, eqs = {}},
          maxDeg = Which[
            zeroQ[betaJ], 0,           (* no coefficients to extract from 0       *)
            PolynomialQ[betaJ, x], Exponent[betaJ, x],
            True, MMax + CDeg
          ];
          Do[
            Module[{coefK = Coefficient[betaJ, x, k]},
              If[!zeroQ[coefK], AppendTo[eqs, coefK]]
            ],
            {k, 1, maxDeg}
          ];
          eqs
        ]
      ],
      {j, n}
    ];
  ];

  (* Each entry of constraintEqs is linear in uvars. Build coefficient matrix. *)
  If[constraintEqs === {},
    (* No constraints — every u-assignment is in the null space; full           *)
    (* parameter space is the basis. Emit identity-vector-shaped basis.          *)
    ns = IdentityMatrix[Length[uvars]];
    ,
    MtxConstraints = Table[
      Coefficient[ce, v],
      {ce, constraintEqs}, {v, uvars}
    ];
    ns = NullSpace[MtxConstraints];
  ];

  If[ns === {} || ns === {{}}, Return[{}]];

  (* Each null-space row is a u-assignment giving an element of R(D).           *)
  basisAFs = Map[
    Function[nsRow,
      Module[{uVal, aPolyVal, fEta},
        uVal = AssociationThread[uvars -> nsRow];
        aPolyVal = Table[
          Sum[uVal[uVar[i, k]] * x^k, {k, 0, CDeg}],
          {i, n}
        ];
        fEta = Table[
          Together[Sum[aPolyVal[[i]] * aFin[[i, j]], {i, n}]],
          {j, n}
        ];
        afMake[fEta, basis]
      ]
    ],
    ns
  ];

  basisAFs
];

(* ::Section:: *)
(* schultzPrincipalGenerator -- principality test for degree-0 divisors.       *)
(*                                                                              *)
(* Returns:                                                                     *)
(*   Missing["NotDegreeZero", deg]   if deg(D) ≠ 0 (cannot be principal).      *)
(*   Missing["NotPrincipal"]         if R(D) = {0} (D not principal).          *)
(*   AF element                     the (unique up to k-scalar) generator F   *)
(*                                   with div(F) = −D, i.e. F generates D as   *)
(*                                   a k[x]-module fragment / k[[1/x]]-fragment.*)

ClearAll[schultzPrincipalGenerator];
Options[schultzPrincipalGenerator] = Options[schultzRiemannRoch];

schultzPrincipalGenerator[d_?schultzDivisorQ, opts : OptionsPattern[]] := Module[
  {deg, rrBasis},
  deg = schultzDivisorDegree[d];
  If[deg =!= 0,
    Return[Missing["NotDegreeZero", deg]]
  ];
  rrBasis = schultzRiemannRoch[d, opts];
  Which[
    rrBasis === {},
      Missing["NotPrincipal"],
    Length[rrBasis] === 1,
      First[rrBasis],
    True,
      (* Higher-than-1 dim should not occur for deg-0 D in genuinely principal *)
      (* cases — emit a diagnostic for the user.                                 *)
      Missing["RiemannRochOverDimensional", Length[rrBasis], rrBasis]
  ]
];

(* ::Section:: *)
(* schultzTorsionPrincipalGenerator -- search for the smallest c with c·D     *)
(* principal, returning (c, F) such that div(F) = c · D. Used by the log       *)
(* term construction (Sch §3.2 eq. 3.4 / SchultzPlan §S.6.1).                  *)
(*                                                                              *)
(* For deg(D) = 0, this is the divisor torsion order. Per Mazur (1977), the    *)
(* torsion order on an elliptic curve over ℚ is ≤ 12; higher genus has        *)
(* a computable bound via good-reduction (Sch §4.2). The default upper bound   *)
(* of 12 mirrors `Options[constructLogTerms]` in src/TragerLogTerms.m.          *)

ClearAll[schultzTorsionPrincipalGenerator];
Options[schultzTorsionPrincipalGenerator] = {
  "MaxOrder"       -> 12,
  "DegreeOverride" -> Automatic,
  "DegreeBuffer"   -> 0
};

(* Inputs:                                                                      *)
(*   d  - the divisor D to test (deg(D) = 0 expected).                          *)
(*   schultzMultiplyFn - a function (D, k) ↦ k·D as Schultz divisor. Provided *)
(*       by the caller (typically via schultzDivisorPower in SchultzDivisor.m).*)
(*                                                                              *)
(* Returns: <|"order" -> c, "function" -> F|> on success,                      *)
(*           <|"order" -> "failed"|> when the search exhausts MaxOrder.        *)

schultzTorsionPrincipalGenerator[
  d_?schultzDivisorQ,
  schultzMultiplyFn_,
  OptionsPattern[]
] := Catch[Module[
  {maxOrder, deg, currD, c, gen, rrOpts},
  maxOrder = OptionValue["MaxOrder"];
  rrOpts = FilterRules[
    {"DegreeOverride" -> OptionValue["DegreeOverride"],
     "DegreeBuffer"   -> OptionValue["DegreeBuffer"]},
    Options[schultzPrincipalGenerator]
  ];
  deg = schultzDivisorDegree[d];
  If[deg =!= 0,
    Throw[<|"order" -> "failed",
            "lastResult" -> Missing["NotDegreeZero", deg]|>]
  ];

  (* c = 1, 2, …, maxOrder. `Return` inside Do does not propagate cleanly out *)
  (* of Mathematica's Module/Do combination, so we wrap in Catch/Throw.        *)
  Do[
    currD = If[c === 1, d, schultzMultiplyFn[d, c]];
    gen = schultzPrincipalGenerator[currD, Sequence @@ rrOpts];
    If[!MissingQ[gen],
      Throw[<|"order" -> c, "function" -> gen|>]
    ],
    {c, 1, maxOrder}
  ];

  <|"order" -> "failed",
    "lastResult" -> Missing["NotPrincipalWithinBound",
                            "MaxOrder" -> maxOrder]|>
]];

(* End of module *)
