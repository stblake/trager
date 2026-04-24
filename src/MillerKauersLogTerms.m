(* ::Package:: *)

(* ::Title:: *)
(* Phase 5 -- Miller-Kauers log-term construction                           *)

(* ::Text:: *)
(* Drop-in replacement for constructLogTerms (TragerLogTerms.m).            *)
(*                                                                           *)
(* Implements Brian Miller's 2012 refinement of the Kauers heuristic        *)
(* (papers/Miller 2012, Chapters III-IV; papers/kauers.m). Key differences  *)
(* vs the Trager divisor-classical path:                                    *)
(*                                                                           *)
(* - No explicit residue divisors or integer-combination divisor arithmetic.*)
(* - No Z-basis of residues needed; Miller's primary decomposition of       *)
(*   J_i = Id(F, v, u − z·v', r_i) partitions residues automatically.       *)
(* - The "removal condition" + multiplicity search (§4.1.6) fixes the       *)
(*   Kauers bug where a correct logand is found but with wrong multiplicity.*)
(*                                                                           *)
(* Algorithm outline (Miller §IV.0, p. 14):                                 *)
(*                                                                           *)
(*   1. Reconstruct u, v, F in K[x, y]:                                     *)
(*        F = y^n − g,  v = D_full = Dpoly · d[n−1],                        *)
(*        u = afToStandard(remainder) · D_full  mod F.                      *)
(*   2. Compute G = GroebnerBasis[{F, v, u − z·v'}, [x, y] > z] using       *)
(*      Kauers' block-elimination order.                                    *)
(*   3. R_z := minimal univariate-in-z element of G, stripped of z^k        *)
(*      (branch-place zero-residues, per Kauers/kauers.m:581).              *)
(*   4. Factor R_z = ∏ r_i(z) over Q into distinct irreducible factors.     *)
(*   5. Per factor r_i:                                                     *)
(*        J_i = {F, v, u − z·v', r_i}                                        *)
(*        primes = zeroDimPrimaryDecomposition[J_i, {x, y, z}]              *)
(*        Per prime h (radical, zero-dim):                                   *)
(*          Loop μ = 1, 2, …, MaxTorsionOrder:                              *)
(*            t_μ = GroebnerBasis[{F, r_i} ∪ h^μ]                           *)
(*            Per p ∈ t_μ:                                                  *)
(*              if GroebnerBasis[{F, r_i, p}] === t_μ:                      *)
(*                for each Galois root γ of r_i:                            *)
(*                   emit {γ/μ, p /. z → γ}                                 *)
(*                continue to next prime                                    *)
(*          μ exhausted ⟹ Failure.                                          *)
(*                                                                           *)
(* At genus 0, μ = 1 always succeeds — so for our pipeline's use case       *)
(* this reduces to one GB test per prime. Higher-multiplicity splits are    *)
(* the reason we still loop.                                                 *)
(*                                                                           *)
(* Output: list of {coeff, vArg} pairs, same shape as constructLogTerms, so *)
(* src/Reassemble.m consumes them without modification.                     *)

(* ::Section:: *)
(* Kauers' block-elimination weight matrix, ported from kauers.m:537-549.   *)
(* For n variables ordered [v_1, v_2, …, v_n] the matrix gives the block    *)
(* order {v_1, …, v_{n−1}} > v_n:                                           *)
(*   - Row 1: total degree of the first (n−1) variables.                    *)
(*   - Row 2: degree of the elim variable v_n.                              *)
(*   - Rows 3…n: reverse-lex tie-break on v_{n−1}, v_{n−2}, …, v_2.         *)
(*                                                                           *)
(* Construction identical to kauers.m's blockOrderGreaterThanLast[n]; see   *)
(* "[x,y,z,...] > t, thanks to Dan Lichtblau from WRI" comment at          *)
(* kauers.m:539.                                                            *)

ClearAll[millerBlockOrder];

millerBlockOrder[n_Integer /; n >= 2] := Module[{drl},
  drl = Prepend[
    Table[-KroneckerDelta[j + k - (n + 1)], {j, n - 1}, {k, n}],
    Table[1, {n}]
  ];
  ReplacePart[drl, {{1, -1} -> 0, {2, -1} -> 1}]
];

(* ::Section:: *)
(* R_z extraction                                                            *)
(*                                                                           *)
(* After computing the block-order GB, the minimal element (smallest wrt    *)
(* the block order) is the unique generator of I ∩ K[z] — a polynomial in  *)
(* z only. We identify it by selecting GB elements whose Variables are      *)
(* a subset of {zInt}, and picking the one of smallest total degree.        *)

ClearAll[millerExtractRzPolynomial];

millerExtractRzPolynomial[G_List, zInt_Symbol, mainVars_List] := Module[
  {candidates, sorted},
  candidates = Select[G,
    And[FreeQ[#, Alternatives @@ mainVars], !FreeQ[#, zInt]]&];
  If[candidates === {},
    Return[tragerFailure["MillerKauersNoUnivariateInZ",
      "Reason" -> "block-order Gröbner basis has no univariate-in-z element",
      "GB"     -> G]]
  ];
  sorted = SortBy[candidates, Exponent[#, zInt]&];
  First[sorted]
];

(* ::Section:: *)
(* Factor R_z into distinct irreducible factors over Q (with multiplicities)*)
(*                                                                           *)
(* Returns a list of {r_i, e_i} pairs where e_i is the place-weighted       *)
(* multiplicity of r_i in the **Rothstein–Trager resultant**                 *)
(*   R_trager(z) = ∏_p res_x(res_y(z v' − u, F), p(x)^{mult_p}).             *)
(* We use the RT resultant rather than the block-GB minimal element         *)
(* because the GB produces the SQUARE-FREE part of R_trager, losing the     *)
(* ramification / place-count multiplicities that scale each log term.     *)
(*                                                                           *)
(* For simple-radical y^n = g branch places (y = 0), ramification index e = *)
(* n appears as a factor of e in R_trager but not in the GB R_z. For        *)
(* integrands whose RT image has multiple places mapping to the same z-     *)
(* value (e.g. y/(x² − 2)), R_trager has the correct count but the GB      *)
(* minimum loses it. Both flavours share the same zero set — only the       *)
(* multiplicities differ — so factoring R_trager gives exactly the same     *)
(* irreducible factors {r_i} as factoring the GB R_z; only the e_i change. *)

ClearAll[millerFactorRz];

millerFactorRz[Rz_, zInt_Symbol] := Module[{factors},
  factors = Rest[FactorList[Rz]];
  factors = DeleteCases[factors, {zInt, _}];
  factors = DeleteCases[factors, {e_ /; FreeQ[e, zInt], _}];
  factors
];


(* ::Section:: *)
(* Ideal power: h^μ as a list of generators.                                 *)
(*                                                                           *)
(* For an ideal h with generators {g_1, …, g_k}, h^μ is generated by all   *)
(* products of μ-tuples of generators. The list can grow combinatorially   *)
(* (C(k+μ-1, μ) distinct products up to ordering), so we always normalise  *)
(* via GroebnerBasis after constructing.                                    *)

ClearAll[idealPowerGens];

idealPowerGens[gens_List, 1] := gens;
idealPowerGens[gens_List, mu_Integer /; mu >= 2] := Module[{prev},
  prev = idealPowerGens[gens, mu - 1];
  DeleteDuplicates[Flatten[Outer[Times, prev, gens]]]
];

(* ::Section:: *)
(* Per-prime multiplicity search                                             *)
(*                                                                           *)
(* For a zero-dim radical ideal h = prime component of J_i, iterate μ from  *)
(* 1 up to maxTorsion. At each step compute t_μ = GroebnerBasis[{F, r_i} ∪  *)
(* h^μ] and scan its elements for a p such that GroebnerBasis[{F, r_i, p}]  *)
(* equals t_μ. On success, emit one {coeff, vArg} pair per Galois           *)
(* conjugate γ of r_i:  coeff = γ/μ,  vArg = p /. zInt → γ.                *)
(*                                                                           *)
(* The test (F, r_i, p) ≟ (F, r_i) + h^μ is Miller §4.1.6's key check.     *)
(* It ensures p vanishes to order exactly μ on the divisor associated with *)
(* h, correcting Kauers' bug where a correct logand ships with the wrong  *)
(* multiplicity.                                                            *)

ClearAll[millerMultiplicitySearch];

(* Maximum subset size to try when forming sums of GB elements as candidate *)
(* logands. Miller's explicit algorithm (§IV.0 pseudocode) tests only      *)
(* individual GB elements, but his Ch V examples (Ex 7, Ex 10) succeed     *)
(* with 2-element sums at μ = 1 that the individual-element loop misses.  *)
(* Set to 3 to cover his examples; bump higher for pathological cases.     *)
$millerMaxSumSubsetSize = 3;

millerMultiplicitySearch[hGens_List, F_, ri_, zInt_Symbol,
                         vars_List, maxTorsion_Integer,
                         y_Symbol, basis_?basisDescriptorQ] := Module[
  {mu, hPow, tMu, expectedGB, pCandidates, candidateGB, roots, contributions,
   branchScale},
  (* Scaling factor: if y lies in the prime h (i.e., y ≡ 0 on V(h) — branch *)
  (* places of the simple radical y^n = g), the RT residue γ is off by the *)
  (* ramification index n, and the true Liouville residue at the place is *)
  (* n·γ. Scale the log-term coefficient accordingly. Non-branch primes    *)
  (* don't need scaling (γ = true residue).                                 *)
  branchScale = If[millerPrimeContainsY[hGens, y, vars], basis["n"], 1];
  Do[
    hPow = idealPowerGens[hGens, mu];
    expectedGB = GroebnerBasis[Join[{F, ri}, hPow], vars,
      MonomialOrder     -> Lexicographic,
      CoefficientDomain -> RationalFunctions];
    (* Try individual GB elements first, then combinatorial sums of up to  *)
    (* $millerMaxSumSubsetSize elements. Sorted by LeafCount so the        *)
    (* simplest candidate wins.                                             *)
    pCandidates = millerCandidateLogands[expectedGB, $millerMaxSumSubsetSize];
    Do[
      candidateGB = GroebnerBasis[{F, ri, p}, vars,
        MonomialOrder     -> Lexicographic,
        CoefficientDomain -> RationalFunctions];
      If[millerGBEqualQ[candidateGB, expectedGB],
        roots = millerRootsOfUnivariate[ri, zInt];
        contributions = Map[
          millerEmitPair[#, mu, branchScale, p, zInt]&,
          roots
        ];
        Return[contributions, Module]
      ],
      {p, pCandidates}
    ],
    {mu, 1, maxTorsion}
  ];
  (* No μ ≤ maxTorsion produced a principal generator. For genus-0 inputs,  *)
  (* this is an internal inconsistency (every degree-0 divisor on P^1 is    *)
  (* principal); for genus ≥ 1 inputs it signals a torsion order exceeding  *)
  (* the search bound.                                                      *)
  tragerFailure["MillerKauersTorsionBoundExceeded",
    "MaxTorsionOrder" -> maxTorsion,
    "PrimeGens"       -> hGens,
    "rFactor"         -> ri,
    "Reason"          -> "no p ∈ GroebnerBasis[{F, r_i} ∪ h^μ] satisfies the \
ideal-equality test for μ ≤ MaxTorsionOrder"]
];

(* Does a prime ideal contain y? Equivalent to: does y ≡ 0 on V(P)? At a   *)
(* simple-radical branch place (y^n = g with g(α) = 0), the place has      *)
(* y-coordinate 0; non-branch places have y ≠ 0. The test is used to       *)
(* decide whether to apply the ramification-index scaling to the log-term *)
(* coefficient.                                                             *)

ClearAll[millerPrimeContainsY];
millerPrimeContainsY[hGens_List, y_Symbol, vars_List] := Module[{rem},
  rem = PolynomialReduce[y, hGens, vars, MonomialOrder -> Lexicographic][[2]];
  TrueQ[rem === 0] || TrueQ[zeroQ[rem]]
];

(* Build the list of logand candidates from a Gröbner basis. Starts with   *)
(* individual elements (fastest to test), then adds 2-element sums, etc.   *)
(* up to the specified maxSubsetSize. De-duplicates aggressively.          *)

ClearAll[millerCandidateLogands];

millerCandidateLogands[gb_List, maxSubsetSize_Integer] := Module[
  {subsets, candidates},
  subsets = Flatten[
    Table[Subsets[gb, {k}], {k, 1, Min[maxSubsetSize, Length[gb]]}],
    1
  ];
  candidates = Map[Total, subsets];
  (* Drop numeric-zero and pure-constant entries.                          *)
  candidates = Select[candidates,
    !TrueQ[zeroQ[#]] && !FreeQ[#, Alternatives @@ Variables[gb]]&];
  DeleteDuplicatesBy[SortBy[candidates, LeafCount], Expand]
];

(* Equality test on Gröbner bases: two GBs (both reduced, both in the same  *)
(* variable order) represent the same ideal iff their element sets match   *)
(* after normalisation (Expand + sort). We compare on Expand-normalised    *)
(* lists.                                                                    *)

ClearAll[millerGBEqualQ];
millerGBEqualQ[a_List, b_List] := Module[{na, nb},
  na = Sort[Expand /@ a];
  nb = Sort[Expand /@ b];
  na === nb
];

(* Roots of an irreducible r_i(zInt) over Q. If r_i is linear (= zInt − c)  *)
(* we return {c}; otherwise we return {Root[r_i &, k]} for k = 1..degree.  *)

ClearAll[millerRootsOfUnivariate];
millerRootsOfUnivariate[ri_, zInt_Symbol] := Module[
  {deg = Exponent[ri, zInt], rootFn},
  If[deg === 1,
    (* r_i = a·zInt + b → root = -b/a *)
    Return[{-Coefficient[ri, zInt, 0] / Coefficient[ri, zInt, 1]}]
  ];
  rootFn = Function[Evaluate[zInt], Evaluate[ri]];
  Table[Root[rootFn, k], {k, deg}]
];

(* Emit one {coeff, vArg} pair for a single Galois root γ. The coefficient *)
(* is (branchScale · γ / μ) where branchScale = n at branch places (y ∈ P *)
(* in the prime) and 1 elsewhere. This corrects the RT residue at branch  *)
(* places where the local uniformizer is y, not x − α, so the true        *)
(* Liouville residue is n·γ rather than γ.                                 *)

ClearAll[millerEmitPair];
millerEmitPair[gamma_, mu_Integer, branchScale_Integer, p_, zInt_Symbol] :=
  Module[{coeff, vArg},
    coeff = Together[branchScale * gamma / mu];
    vArg  = p /. zInt -> gamma;
    {coeff, vArg}
  ];

(* ::Section:: *)
(* Public API                                                                *)

ClearAll[MillerKauersLogTerms];

Options[MillerKauersLogTerms] = {
  MaxTorsionOrder -> 12,
  (* The following options are accepted for call-site compatibility with    *)
  (* constructLogTerms; Miller's algorithm derives equivalent information    *)
  (* internally from the Gröbner basis of the Kauers ideal.                 *)
  Multiplicities  -> Automatic,
  QBasis          -> Automatic,
  BasisCoeffs     -> Automatic
};

MillerKauersLogTerms[residues_List, remainderAF_?afElementQ, Dpoly_,
                    basis_?basisDescriptorQ, y_Symbol,
                    OptionsPattern[]] := Catch[Module[
  {n, g, x, dmax, F, vFull, vprime, Gpoly, u, zInt,
   blockOrd, G, Rz, rFactors, logTerms, maxTorsion,
   primes, contributions, remainderCoeffsZero},

  n = basis["n"];
  g = basis["g"];
  x = basis["x"];
  dmax = Last[basis["d"]];
  maxTorsion = OptionValue[MaxTorsionOrder];

  (* Early exit: if the remainder is zero, there is no log part. *)
  remainderCoeffsZero = AllTrue[remainderAF["Coeffs"],
    TrueQ[Together[#] === 0] &];
  If[remainderCoeffsZero, Throw[{}]];

  (* Step 1: reconstruct (u, v, F) in K[x, y]. Use the "full" denominator  *)
  (* v = Dpoly · d[n−1] so that integrand = u / v with u, v coprime on the *)
  (* curve; the d_i basis denominators are absorbed into v and their       *)
  (* branch-place contributions drop out via the z^k strip in Step 3.      *)
  F      = y^n - g;
  vFull  = Expand[Dpoly * dmax];
  vprime = D[vFull, x];
  Gpoly  = Expand[afToStandard[remainderAF, basis, y] * vFull];
  u      = reduceYDegree[Gpoly, x, y, n, g];

  (* Step 2: Kauers' block-order Gröbner basis. *)
  zInt     = Unique["z$miller"];
  blockOrd = millerBlockOrder[3];   (* [x, y] > zInt, 3 vars total *)
  (* CoefficientDomain -> RationalFunctions: parameters in $tragerParameters *)
  (* are treated as elements of K(params), not as extra polynomial variables. *)
  (* Without this, GroebnerBasis includes them in its variable set and the   *)
  (* 3x3 block-order matrix `blockOrd` no longer spans every term, raising   *)
  (* GroebnerBasis::mnmord2.                                                 *)
  G = GroebnerBasis[{F, vFull, u - zInt * vprime}, {x, y, zInt},
    MonomialOrder      -> blockOrd,
    CoefficientDomain  -> RationalFunctions,
    Method             -> "GroebnerWalk"];

  (* Step 3: R_z = minimal univariate-in-z element of the block-order GB.   *)
  (* Kept as the "elementarity witness" (if it's not in Q[z], integrand is *)
  (* non-elementary) but NOT used for multiplicity extraction.               *)
  Rz = millerExtractRzPolynomial[G, zInt, {x, y}];
  If[tragerFailureQ[Rz], Throw[Rz]];
  If[!rationalPolynomialQ[Rz, zInt],
    Throw[tragerFailure["NonElementary",
      "Reason" -> "R_z has non-constant coefficients (residues not in Q̄)",
      "Rz"     -> Rz]]
  ];

  (* Step 4: factor R_z (from the block-order GB) into distinct            *)
  (* irreducible factors over Q. The multiplicities are not used here —    *)
  (* we derive the per-place ramification scaling inside                   *)
  (* millerMultiplicitySearch by testing whether y lies in the prime.      *)
  rFactors = millerFactorRz[Rz, zInt];
  If[rFactors === {}, Throw[{}]];

  (* Step 5: per-factor primary decomposition + multiplicity search. *)
  logTerms = {};
  Do[
    Module[{ri = rFactor[[1]]},
      primes = zeroDimPrimaryDecomposition[
        {F, vFull, u - zInt * vprime, ri}, {x, y, zInt}];
      If[tragerFailureQ[primes], Throw[primes]];
      Do[
        contributions = millerMultiplicitySearch[
          prime, F, ri, zInt, {x, y, zInt}, maxTorsion, y, basis];
        If[tragerFailureQ[contributions], Throw[contributions]];
        logTerms = Join[logTerms, contributions],
        {prime, primes}
      ]
    ],
    {rFactor, rFactors}
  ];

  logTerms
]];
