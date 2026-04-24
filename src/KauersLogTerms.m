(* ::Package:: *)

(* ::Title:: *)
(* Phase 5 -- Kauers log-term construction (heuristic)                      *)

(* ::Text:: *)
(* Direct port of M. Kauers' LogarithmicPart from papers/kauers.m, adapted *)
(* to the IntegrateTrager pipeline interface. Drop-in replacement for      *)
(* constructLogTerms / MillerKauersLogTerms.                                *)
(*                                                                           *)
(* Algorithm (Kauers 2008, summarised):                                    *)
(*                                                                           *)
(*   1. Reconstruct (u, v, F) in K[x, y] from the Hermite remainder.       *)
(*   2. Compute G = block-order GroebnerBasis({F, v, u − t v'}, [x,y] > t).*)
(*   3. Take R_z = first element of G (univariate in t after the block      *)
(*      elimination).                                                       *)
(*   4. Factor R_z over Q, drop the t-only factor (zero-residue branch     *)
(*      places) and constant factors. Each remaining {gg, nn} pair         *)
(*      contributes one log term.                                           *)
(*   5. Per (gg, nn): find a "principal divisor" by iteratively SQUARING   *)
(*      the WHOLE Gröbner basis G^k and searching for p ∈ GB(G^k ∪ {F, gg})*)
(*      such that GB({F, gg, p}) === GB(G^k ∪ {F, gg}). Emit               *)
(*        ∑_{γ : gg(γ) = 0} (nn / k) · γ · log(p(x, y, γ))                  *)
(*      where k is the squaring count at which the test passed.            *)
(*                                                                           *)
(* Differences vs MillerLogTerms                                            *)
(*                                                                           *)
(* - No primary decomposition. Kauers works directly with the original     *)
(*   block-elim GB and squares it, which exposes products like (x − 2yt)²  *)
(*   as candidate logands. Miller's pseudocode reduces those products      *)
(*   inside h^μ and loses the structure, so Miller fails on integrands     *)
(*   like x²/((x²−1)(x⁸+1)^(1/4)) where Kauers succeeds with a partial    *)
(*   answer.                                                                *)
(* - Kauers may return only a partial integral (some R_z factors fail the  *)
(*   principal-divisor search at every iteration ≤ MaxTorsionOrder). The   *)
(*   un-handled factors silently contribute nothing to the log part; the   *)
(*   pipeline's Phase-6 verifier catches the resulting derivative mismatch *)
(*   as ImplementationIncomplete.                                           *)
(* - Kauers misses cases like Miller Ex 10 where the strict primary-decomp *)
(*   approach is essential. Use "LogTermsMethod" -> "Miller" for those.    *)
(*                                                                           *)
(* The MaxTorsionOrder option here is the squaring count `k` bound, NOT a  *)
(* divisor torsion order. Default 10 (matches kauers.m's default).         *)

(* ::Section:: *)
(* Block-order Gröbner basis (block ordering [v_1,...,v_{n-1}] > v_n)      *)

ClearAll[kauersGroebner];

kauersGroebner[exprs_List, vars_List] :=
  GroebnerBasis[exprs, vars,
    MonomialOrder -> millerBlockOrder[Length[vars]],
    Method -> "GroebnerWalk"];

(* GB equality: same monomial order ⟹ identical reduced GB iff same ideal. *)
ClearAll[kauersGBEqualQ];
kauersGBEqualQ[a_List, b_List] :=
  Sort[Expand /@ a] === Sort[Expand /@ b];

(* ::Section:: *)
(* Kauers' principal-divisor search                                         *)
(*                                                                           *)
(* Given an ideal (presented as a Gröbner basis) plus a list of "u" gens   *)
(* that are NEVER added to themselves during squaring, finds an element    *)
(* p ∈ GB(gb ∪ u) whose adjunction (with u alone) generates the same       *)
(* ideal. Returns 1 if no such p exists in the current GB.                  *)

ClearAll[kauersPrincipalDivisor];

kauersPrincipalDivisor[gb_List, u_List, v_List] := Module[
  {G, hit},
  G = kauersGroebner[Join[gb, u], v];
  hit = SelectFirst[G,
    kauersGBEqualQ[kauersGroebner[Append[u, #], v], G] &,
    1];
  hit
];

(* ::Section:: *)
(* Iterated squaring loop.                                                  *)
(*                                                                           *)
(* Returns {p, k} where p is a principal divisor of G^k ∪ u (k ≥ 1), or    *)
(* {1, k} if none found within `bound` squarings.                           *)

ClearAll[kauersPrincipalPower];

kauersPrincipalPower[gb_List, u_List, v_List, bound_Integer] := Module[
  {id = gb, p, k = 1},
  p = kauersPrincipalDivisor[id, u, v];
  While[k < bound && p === 1,
    k++;
    id = kauersGroebner[Join[Flatten @ Outer[Times, id, gb], u], v];
    p = kauersPrincipalDivisor[id, u, v];
  ];
  {p, k}
];

(* ::Section:: *)
(* Roots of an irreducible factor of R_z, returned as Galois conjugates.   *)

ClearAll[kauersRoots];

kauersRoots[gg_, t_Symbol] := Module[{deg = Exponent[gg, t], rootFn},
  If[deg === 1,
    Return[{-Coefficient[gg, t, 0] / Coefficient[gg, t, 1]}]
  ];
  rootFn = Function[Evaluate[t], Evaluate[gg]];
  Table[Root[rootFn, k], {k, deg}]
];

(* ::Section:: *)
(* Public API                                                                *)

ClearAll[KauersLogTerms];

Options[KauersLogTerms] = {
  MaxTorsionOrder -> 10,
  (* Accepted for call-site compatibility with constructLogTerms; ignored. *)
  Multiplicities  -> Automatic,
  QBasis          -> Automatic,
  BasisCoeffs     -> Automatic
};

KauersLogTerms[residues_List, remainderAF_?afElementQ, Dpoly_,
                basis_?basisDescriptorQ, y_Symbol,
                OptionsPattern[]] := Catch[Module[
  {n, g, x, dmax, F, vFull, vprime, Gpoly, u, t, G, Rz, factors,
   logTerms, p, kIter, gg, nn, mult, bound, contributions,
   remainderCoeffsZero},

  n = basis["n"];
  g = basis["g"];
  x = basis["x"];
  dmax = Last[basis["d"]];
  bound = OptionValue[MaxTorsionOrder];

  remainderCoeffsZero = AllTrue[remainderAF["Coeffs"],
    TrueQ[Together[#] === 0] &];
  If[remainderCoeffsZero, Throw[{}]];

  (* Step 1: reconstruct (u, v, F) in K[x, y]. *)
  F      = y^n - g;
  vFull  = Expand[Dpoly * dmax];
  vprime = D[vFull, x];
  Gpoly  = Expand[afToStandard[remainderAF, basis, y] * vFull];
  u      = reduceYDegree[Gpoly, x, y, n, g];

  (* Step 2: block-order Gröbner basis. *)
  t = Unique["t$kauers"];
  G = kauersGroebner[{F, vFull, u - t * vprime}, {x, y, t}];

  (* Step 3: R_z = first element. Sanity-check it is a polynomial in t       *)
  (* alone with rational coefficients (else the integrand is non-elementary).*)
  Rz = First[G];
  If[!FreeQ[Rz, x] || !FreeQ[Rz, y],
    Throw[tragerFailure["KauersNoUnivariateInZ",
      "Reason" -> "first GB element is not univariate in t",
      "GB"     -> G]]
  ];
  If[!rationalPolynomialQ[Rz, t],
    Throw[tragerFailure["NonElementary",
      "Reason" -> "R_z has non-constant coefficients (residues are not constant)",
      "Rz"     -> Rz]]
  ];

  (* Step 4: factor R_z, drop t-only and constant factors. *)
  factors = DeleteCases[Rest[FactorList[Rz]],
    {t, _} | {e_ /; FreeQ[e, t], _}];
  If[factors === {}, Throw[{}]];

  (* Step 5: per-factor principal-power search. *)
  logTerms = {};
  Do[
    {gg, nn} = factor;
    {p, kIter} = kauersPrincipalPower[G, {F, gg}, {x, y, t}, bound];
    If[!TrueQ[p === 1] && !tragerFailureQ[p],
      mult = Together[nn / kIter];
      contributions = Map[
        Function[gamma, {Together[mult * gamma], p /. t -> gamma}],
        kauersRoots[gg, t]
      ];
      logTerms = Join[logTerms, contributions]
    ]
    (* If p === 1 (no principal divisor found within bound), silently skip *)
    (* this factor — the resulting derivative mismatch surfaces in the     *)
    (* pipeline's Phase-6 verifier as ImplementationIncomplete.            *),
    {factor, factors}
  ];

  logTerms
]];
