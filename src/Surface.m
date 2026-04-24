(* ::Package:: *)

(* ::Title:: *)
(* Surface-syntax wrapper: IntegrateTrager[f, x] *)

(* ::Text:: *)
(* Let the user write                                                        *)
(*                                                                           *)
(*   IntegrateTrager[1/Sqrt[x^2 + 1], x]                                    *)
(*                                                                           *)
(* without an explicit y-symbol or curve relation. Walks the integrand to   *)
(* find radical patterns, synthesises a fresh y and the relation y^n = g,  *)
(* rewrites the integrand in terms of y, and delegates to the two-argument *)
(* IntegrateTrager.                                                         *)
(*                                                                           *)
(* Recognised patterns, all with n >= 2 integer:                              *)
(*   Sqrt[f]              -> y^2 == f,         Sqrt[f]^k  -> y^k           *)
(*   f^(1/n)              -> y^n == f                                       *)
(*   f^(k/n)  (k, n coprime, n > 1)  -> y^n == f,  integrand uses y^k      *)
(*                                                                           *)
(* If two distinct radicals appear (e.g. Sqrt[f1] and CubeRoot[f2] or       *)
(* Sqrt[f1] and Sqrt[f2] with f1 =!= f2), we refuse with NotSimpleRadical. *)

(* ::Section:: *)
(* findRadicals                                                              *)
(*                                                                           *)
(* Return {{radicand_i, n_i}, ...} for every distinct (radicand, n) pair   *)
(* appearing in the integrand. Power-of-radicals are reduced: Sqrt[f]^k    *)
(* counts as one pair (f, 2), not k pairs.                                  *)

ClearAll[findRadicals];
findRadicals[expr_, x_Symbol] := Module[{cases, normalized},
  cases = Cases[expr,
    Power[f_, r_Rational] /; !FreeQ[f, x] :> {f, Denominator[r]},
    {0, Infinity}
  ];
  (* Sqrt[f] parses as Power[f, 1/2] -> already covered. *)
  (* f^(k/n) also covered, with denominator n.                              *)
  (* Deduplicate on (radicand, n).                                           *)
  normalized = {Together[#[[1]]], #[[2]]} & /@ cases;
  DeleteDuplicates[normalized]
];

(* ::Section:: *)
(* substituteRadical                                                         *)
(*                                                                           *)
(* Given the chosen (radicand, n), rewrite the integrand with y replacing  *)
(* any f^(k/n) as y^k.                                                       *)

ClearAll[substituteRadical];
substituteRadical[expr_, radicand_, n_Integer, y_Symbol, x_Symbol] := Module[
  {result},
  result = expr /. {
    Power[f_, r_Rational] /; TrueQ[Together[f - radicand] === 0] &&
                            Denominator[r] === n :>
      y^Numerator[r]
  };
  result
];

(* ::Section:: *)
(* IntegrateTrager[f, x] (single-radical surface wrapper)                    *)

(* When the user supplies no y and no relation, detect a radical pattern   *)
(* and reroute to the core function.                                        *)

IntegrateTrager[f_, x_Symbol, opts : OptionsPattern[]] := Module[
  {radicals, radicand, n, yTmp, rewritten, result, distinct},

  (* Internal y-symbol: lives in Trager`Private` so it is freshly named per *)
  (* call (yTmp$NNN under Module renaming) and cannot collide with any user *)
  (* parameter name like "y", "a", or even "yTmp".                           *)
  radicals = findRadicals[f, x];

  (* No radicals: purely rational in x, nothing to do here (core does not   *)
  (* handle pure rational integration yet).                                 *)
  If[radicals === {},
    Return[Failure["NotSimpleRadical", <|
      "Reason" -> "integrand contains no algebraic radical in x; \
IntegrateTrager[f, {x, y, y^n == g}] is needed for an explicit form, or \
use Mathematica's Integrate for purely rational integrands",
      "Integrand" -> f
    |>]]
  ];

  (* Multiple distinct radicals: unsupported (Trager Appendix A territory).  *)
  distinct = DeleteDuplicates[radicals];
  If[Length[distinct] > 1,
    Return[Failure["NotSimpleRadical", <|
      "Reason" -> "integrand contains multiple distinct algebraic radicals; only simple-radical extensions are supported",
      "Radicals" -> distinct
    |>]]
  ];

  {radicand, n} = First[distinct];

  (* Manufacture a fresh y and rewrite the integrand using it.              *)
  rewritten = substituteRadical[f, radicand, n, yTmp, x];
  result = IntegrateTrager[rewritten,
    {x, yTmp, yTmp^n == radicand},
    opts];
  (* Map yTmp back to the radical form for the user.                        *)
  If[MatchQ[result, _Failure], Return[result]];
  If[AssociationQ[result] && KeyExistsQ[result, "Result"],
    (* Diagnostics mode *)
    result["Result"] = result["Result"] /. yTmp -> radicand^(1/n);
    result,
    result /. yTmp -> radicand^(1/n)
  ]
];
