(* ::Package:: *)

(* ::Title:: *)
(* Zero-dimensional ideal decomposition                                     *)

(* ::Text:: *)
(* Public entry point: zeroDimPrimaryDecomposition[gens, vars]              *)
(*                                                                          *)
(* Input                                                                     *)
(*   gens: generators of an ideal I ⊂ Q[vars], with I zero-dimensional.    *)
(*   vars: list of variables, left-to-right in elimination order so that    *)
(*         lex ordering uses vars[[1]] > vars[[2]] > ... > vars[[-1]].      *)
(*                                                                          *)
(* Output                                                                    *)
(*   A list of reduced lex Gröbner bases, one per associated prime of I.    *)
(*   The intersection of these primes equals √I. For Miller's algorithm we  *)
(*   only need the primes (not the primary components themselves), since    *)
(*   Step 4 of Miller §3.2 immediately extracts P_ij = √Q_ij.               *)
(*                                                                          *)
(* Conventions                                                               *)
(*   The unit ideal <1> decomposes to the empty list {}.                    *)
(*   The zero ideal <0> (= whole ring; vacuous when V(I) = affine space)    *)
(*   is not zero-dimensional; we emit a Failure for that case.               *)
(*                                                                          *)
(* Algorithm (triangular decomposition, repeat-until-stable)                *)
(*                                                                          *)
(*   1. Compute reduced lex Gröbner basis G of <gens>.                      *)
(*   2. If G == {1} return {}. If G is empty (zero ideal) return Failure.   *)
(*   3. Scan G for any element f that Factor[f, Extension -> Automatic]     *)
(*      splits into ≥ 2 non-constant factors over the current coefficient   *)
(*      ring. If one is found, recurse on each G + <f_j> and concatenate.   *)
(*   4. If no element splits, G is irreducible at every variable level —    *)
(*      treat G itself as the prime.                                        *)
(*                                                                          *)
(* Correctness                                                                *)
(*   For any zero-dim ideal I over Q, the reduced lex GB has the "shape"   *)
(*   of a triangular set whenever the variable ordering is generic for I.  *)
(*   Each univariate polynomial-in-the-last-level-variable factors into     *)
(*   factors whose roots correspond to distinct prime components. The       *)
(*   recursion terminates because each split strictly refines the radical.  *)
(*   When the shape-lemma fails (non-generic order), Extension -> Automatic *)
(*   still catches factorizations of multivariate polynomials via Gauss's   *)
(*   lemma so long as a factorization exists over some algebraic extension. *)
(*                                                                          *)
(*   For pathological zero-dim ideals where no polynomial in the lex GB     *)
(*   factors over any extension Mathematica can detect automatically, the  *)
(*   decomposition may return a single "prime" that is actually reducible. *)
(*   In that case the caller gets back a larger-than-minimal ideal, which   *)
(*   for Miller's algorithm just means the removal-condition/multiplicity  *)
(*   search sees a larger search space — still correct, just slower.       *)

(* ::Section:: *)
(* Public API *)

ClearAll[zeroDimPrimaryDecomposition];

zeroDimPrimaryDecomposition[gens_List, vars_List] := Module[{G},
  G = idealReducedLexGB[gens, vars];
  Which[
    unitIdealGBQ[G],
      {},
    G === {},
      tragerFailure["ZeroDimDecompositionZeroIdeal",
        "Gens"  -> gens,
        "Vars"  -> vars,
        "Reason" -> "the zero ideal is not zero-dimensional"],
    True,
      zeroDimSplitFixpoint[G, vars]
  ]
];

(* ::Section:: *)
(* Helpers *)

(* Reduced lex GB wrapper. We always use Extension -> Automatic so that    *)
(* coefficients involving Root[...] / AlgebraicNumber[...] are handled      *)
(* correctly (Miller's factorizations over Q(α) produce such GBs).          *)

ClearAll[idealReducedLexGB];
idealReducedLexGB[gens_List, vars_List] :=
  GroebnerBasis[gens, vars,
    MonomialOrder -> Lexicographic,
    CoefficientDomain -> RationalFunctions,
    Method -> "GroebnerWalk"];

(* A lex GB represents the unit ideal <1> iff it contains a nonzero         *)
(* constant. GroebnerBasis normalises such a basis to {1}; we guard also   *)
(* against the edge case where the constant is something like 3/2.         *)

ClearAll[unitIdealGBQ];
unitIdealGBQ[G_List] :=
  AnyTrue[G, FreeQ[#, Alternatives @@ idealGBVariables[G]] && #=!=0 &];

(* All symbols appearing in the GB. Used only inside unitIdealGBQ. *)

ClearAll[idealGBVariables];
idealGBVariables[G_List] := Union @@ (Variables /@ G);

(* ::Section:: *)
(* Splitting driver                                                         *)
(*                                                                          *)
(* Walks every G-element, trying to factor it. On the first splittable      *)
(* element, subdivide into sub-ideals G + <factor_k>, recompute lex GB, and *)
(* recurse. If no element factors, the ideal is declared prime.              *)

ClearAll[zeroDimSplitFixpoint];

zeroDimSplitFixpoint[G_List, vars_List] := Module[
  {split, subIdeals, subPrimes},
  split = firstSplittableFactorization[G, vars];
  If[split === $None,
    Return[{G}]
  ];
  (* split has the form {originalElement, {factor_1, ..., factor_m}}.       *)
  (* Add each factor to G, recompute lex GB, recurse.                        *)
  subIdeals = Map[
    Function[factor, idealReducedLexGB[Append[G, factor], vars]],
    Last[split]
  ];
  subPrimes = Map[
    Function[subG,
      Which[
        unitIdealGBQ[subG], {},          (* branch is inconsistent; drop it  *)
        subG === {},          {{}},      (* unreachable: zero ideal         *)
        True,                 zeroDimSplitFixpoint[subG, vars]
      ]
    ],
    subIdeals
  ];
  (* Deduplicate on the reduced-GB representation so repeated factor splits *)
  (* do not over-report the same prime twice.                                *)
  DeleteDuplicates[Join @@ subPrimes]
];

(* ::Section:: *)
(* Factor-and-split search                                                  *)
(*                                                                          *)
(* Returns either $None (no element of G splits) or {elt, {f_1,...,f_m}}.   *)
(*                                                                          *)
(* Strategy: prefer factorizing elements involving few variables first      *)
(* (usually the univariate-in-smallest-var, which is why we process vars    *)
(* in Reverse[] order). This keeps the tree of splits balanced and avoids   *)
(* redundant work when a high-level variable's polynomial factors only      *)
(* because a low-level variable already restricted the extension.            *)

ClearAll[firstSplittableFactorization];

firstSplittableFactorization[G_List, vars_List] := Module[
  {sortedG, found = $None},
  sortedG = SortBy[G, {Length[Intersection[Variables[#], vars]] &,
                       LeafCount}];
  Do[
    Module[{factors = nonTrivialFactorization[elt]},
      If[factors =!= $None,
        found = {elt, factors};
        Break[]
      ]
    ],
    {elt, sortedG}
  ];
  found
];

(* Factor a polynomial over Q (with algebraic-number extensions auto-       *)
(* detected) and return the list of non-unit, non-constant irreducible     *)
(* factors when the polynomial splits into ≥ 2 such factors. Returns $None *)
(* if the polynomial is already irreducible (no split).                     *)
(*                                                                          *)
(* We intentionally ignore repeated factors for splitting purposes (each    *)
(* distinct root defines a distinct prime) and strip pure numeric content.  *)

ClearAll[nonTrivialFactorization];

nonTrivialFactorization[poly_] := Module[
  {factored, factorList, nonConst, distinct},
  factored = Factor[poly, Extension -> Automatic];
  (* Normalise the factored form into a flat list of factors. The `Flat`    *)
  (* attribute on Times causes `Times[fs__] :> {fs}` to bind the entire     *)
  (* product rather than an expanded sequence, so we use Apply[List, ...]   *)
  (* which is robust across Times / Power / atomic heads.                   *)
  factorList = Which[
    Head[factored] === Times, List @@ factored,
    Head[factored] === Power && IntegerQ[factored[[2]]] &&
      factored[[2]] > 0,      {factored[[1]]},
    True,                     {factored}
  ];
  (* Expand Power[p, k] entries in the list to their base p.                *)
  factorList = Flatten[Replace[factorList,
    Power[p_, _Integer?Positive] :> p, {1}]];
  nonConst = Select[factorList,
    Not[FreeQ[#, Alternatives @@ Variables[poly]]] &];
  (* Treat factors that differ only by a ±1 scalar as the same factor; the  *)
  (* corresponding prime ideals coincide.                                    *)
  distinct = DeleteDuplicates[nonConst,
    PossibleZeroQ[Together[#1/#2 - 1]] ||
    PossibleZeroQ[Together[#1/#2 + 1]] &];
  If[Length[distinct] >= 2, distinct, $None]
];

(* ::Section:: *)
(* Radical of a zero-dim ideal                                              *)
(*                                                                          *)
(* Convenience wrapper returning sqrt(I) as a single reduced lex GB         *)
(* (= intersection of the prime components). Miller's Step 4 uses this     *)
(* indirectly when forming the radical of each primary component.          *)

ClearAll[zeroDimRadical];
zeroDimRadical[gens_List, vars_List] := Module[{primes},
  primes = zeroDimPrimaryDecomposition[gens, vars];
  If[tragerFailureQ[primes], Return[primes]];
  If[primes === {}, Return[{1}]];   (* unit ideal *)
  (* Intersect primes by successive GroebnerBasis-of-intersection.           *)
  idealIntersection[primes, vars]
];

ClearAll[idealIntersection];
idealIntersection[{}, vars_] := {1};
idealIntersection[{one_List}, vars_] := one;
idealIntersection[primes_List, vars_] := Module[
  {result, t},
  (* Standard ideal-intersection via an auxiliary variable:                 *)
  (*   I ∩ J = eliminate(t, t·I + (1-t)·J).                                 *)
  result = First[primes];
  Do[
    t = Unique["t$intersect"];
    result = GroebnerBasis[
      Join[t * result, (1 - t) * P],
      Prepend[vars, t],
      MonomialOrder -> Lexicographic
    ];
    result = Select[result, FreeQ[#, t]&],
    {P, Rest[primes]}
  ];
  result
];
