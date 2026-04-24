(* ::Package:: *)

(* ::Title:: *)
(* Log -> ArcTan post-processing                                              *)

(* ::Text:: *)
(* Phase-6 cleanup. Trager's algorithm produces antiderivatives of the form  *)
(*                                                                            *)
(*     algPart + Sum_j  c_j * Log[v_j]                                        *)
(*                                                                            *)
(* where the residues c_j live in some algebraic extension of Q. When two     *)
(* log terms appear with complex-conjugate coefficients and complex-conjugate*)
(* arguments,                                                                *)
(*                                                                            *)
(*     a Log[A + I B] + conj(a) Log[A - I B],                                 *)
(*                                                                            *)
(* the pair is real and equals                                                *)
(*                                                                            *)
(*     2 Im[a] * ArcTan[A / B]    (when Re[a] = 0, Im[a] != 0),               *)
(*                                                                            *)
(* using the identity                                                          *)
(*                                                                            *)
(*     ArcTan[A/B] = (I/2) * Log[(A + I B) / (A - I B)].                       *)
(*                                                                            *)
(* The dual identity covers the Re[a] != 0 case (yielding -2 I Re[a] ArcTan).*)
(* Detecting and rewriting these pairs gives a real-valued display form for  *)
(* what is otherwise a sum of complex logarithms whose imaginary parts       *)
(* mathematically cancel.                                                     *)
(*                                                                            *)
(* The rules below match the Z-pattern                                        *)
(*                                                                            *)
(*     a Log[A] + b Log[B]                                                    *)
(*                                                                            *)
(* and check that (A, B) form a complex-conjugate pair in x by splitting     *)
(* (A + B)/2 (the real part) and (A - B)/2 (the imaginary part) and          *)
(* verifying which has zero real / imaginary content.                         *)

(* ::Section:: *)
(* Real / imaginary projection of an x-expression                             *)
(*                                                                            *)
(* Following kauers.m: substitute every Complex[a, b] in the expression by   *)
(* a + b * eps (where eps is a fresh formal symbol), expand to first order    *)
(* in eps, and read off the linear coefficient as the imaginary part. The     *)
(* zero-th order coefficient is the real part. The series approach is more   *)
(* robust than ComplexExpand for expressions with embedded Root[] objects     *)
(* and fractional powers, which is the regime Trager outputs land in.         *)

ClearAll[imagTerms];
imagTerms[expr_, x_] := Module[{eps},
  SeriesCoefficient[
    Series[expr /. {Complex[a_, b_] :> (a + b eps)}, {eps, 0, 1}],
    1] /. _SeriesCoefficient -> 0
];

ClearAll[realTerms];
realTerms[expr_, x_] := imagTerms[I expr, x];

(* ::Section:: *)
(* Rational-shape predicate (helper for arcTanTerm)                            *)

ClearAll[rationalShapeQ];
rationalShapeQ[e_, x_] := With[{te = Together[e]},
  Denominator[te] =!= 1 &&
  PolynomialQ[Numerator[te], x] && PolynomialQ[Denominator[te], x]
];

(* ::Section:: *)
(* arcTanTerm[re, im, x] -- pick the nicer of ArcTan[re/im] vs -ArcTan[im/re] *)
(*                                                                            *)
(* Both forms are equivalent because D[ArcTan[u], x] = D[-ArcTan[1/u], x].    *)
(* We prefer the form whose argument is rational (or polynomial / free of x), *)
(* falling back to the inverse if the radicand sits in the denominator. When  *)
(* neither form has a polynomial / rational shape we multiply numerator and   *)
(* denominator by enough copies of the radical so that the irrational part    *)
(* gets squared away (equivalent to rationalising the denominator).           *)

ClearAll[arcTanTerm];
arcTanTerm[re_, im_, x_] := Module[{im2, re2, n},

  If[FreeQ[im, x] || PolynomialQ[im, x] || rationalShapeQ[im, x],
    Return[ ArcTan[Cancel @ Together[re/im]] ]
  ];

  If[FreeQ[re, x] || PolynomialQ[re, x] || rationalShapeQ[re, x],
    Return[ -ArcTan[Cancel @ Together[im/re]] ]
  ];

  (* Rationalise im by multiplying through (n-1) extra copies of im, where n *)
  (* is the largest fractional-power denominator appearing inside im.         *)
  n = Max[
    Cases[im,
      Power[p_, k_Rational] /; !FreeQ[p, x] :> Abs[Denominator[k]],
      {0, Infinity}] /. {} -> {1}
  ];

  im2 = Factor @ Expand[ im Product[im, {n - 1}] ];
  re2 = re Product[im, {n - 1}];

  If[FreeQ[im2, x] || PolynomialQ[im2, x] || rationalShapeQ[im2, x],
    Return[ ArcTan[re2/im2] ]
  ];

  n = Max[
    Cases[re,
      Power[p_, k_Rational] /; !FreeQ[p, x] :> Abs[Denominator[k]],
      {0, Infinity}] /. {} -> {1}
  ];
  im2 = im Product[re, {n - 1}];
  re2 = Factor @ Expand[ re Product[re, {n - 1}] ];

  If[FreeQ[re2, x] || PolynomialQ[re2, x] || rationalShapeQ[re2, x],
    Return[ -ArcTan[im2/re2] ]
  ];

  ArcTan[Cancel @ Together[re/im]]
];

(* ::Section:: *)
(* Pair-of-logs replacement rules                                              *)
(*                                                                            *)
(* The rules pattern-match on a Plus[a Log[A], b Log[B]] inside any larger    *)
(* expression. We test that:                                                  *)
(*                                                                            *)
(*   1. a, b are constants (FreeQ in the integration variable x);             *)
(*   2. either Im[a] != 0 (rule A) or Re[a] != 0 (rule B);                    *)
(*   3. Im[a] + Im[b] = 0 (rule A) / Re[a] + Re[b] = 0 (rule B), so the pair  *)
(*      assembles into a single ArcTan with a real coefficient;               *)
(*   4. (A + B)/2 + (A - B)/2 = A and similarly for B (a sanity check that    *)
(*      A and B really do split as Re +/- I*Im in x);                         *)
(*   5. (A + B)/2 has zero imaginary part and (A - B)/2 has zero real part   *)
(*      in x, so Re_x = (A + B)/2 and Im_x = -I * (A - B)/2 are the           *)
(*      real / imaginary components on which ArcTan acts.                     *)
(*                                                                            *)
(* The rules are constructed lazily as functions of x because Mathematica's   *)
(* RuleDelayed pattern cannot reference an outer variable without binding it  *)
(* at construction time.                                                      *)

ClearAll[logToArcTanRules];
logToArcTanRules[x_] := Module[{a, b, A, B, ruleA, ruleB},

  (* Rule A: pure-imaginary coefficient case (Re[a] = 0, Im[a] != 0). *)
  ruleA = HoldPattern[a_ Log[A_] + b_ Log[B_]] /;
    FreeQ[a, x] && FreeQ[b, x] &&
    TrueQ[Im[a] != 0] &&
    TrueQ[Cancel[Im[a] + Im[b]] == 0] &&
    PossibleZeroQ[Cancel[(A + B)/2 + (A - B)/2 - A]] &&
    PossibleZeroQ[Cancel[(A + B)/2 - (A - B)/2 - B]] &&
    PossibleZeroQ[imagTerms[(A + B)/2, x]] &&
    PossibleZeroQ[realTerms[(A - B)/2, x]] &&
    !PossibleZeroQ[realTerms[(A + B)/2, x]] &&
    !PossibleZeroQ[imagTerms[(A - B)/2, x]] :>
    2 Im[a] arcTanTerm[realTerms[(A + B)/2, x],
                       imagTerms[(A - B)/2, x], x] +
    Re[a] Log[A] + Re[b] Log[B];

  (* Rule B: anti-conjugate case (Re[a] + Re[b] = 0, Re[a] != 0). Writing  *)
  (* A = u + I v and B = u - I v, expanding a = Re[a] + I Im[a], using the *)
  (* identity Log[u+Iv] - Log[u-Iv] = -2 I ArcTan[u/v], and grouping by   *)
  (* Re[a] (which sums) vs Im[a] (which doesn't) gives                    *)
  (*                                                                        *)
  (*   a Log[A] + b Log[B]                                                  *)
  (*     = Re[a]*(Log[A] - Log[B]) + I*(Im[a]*Log[A] + Im[b]*Log[B])        *)
  (*     = -2 I Re[a] ArcTan[u/v] + I Im[a] Log[A] + I Im[b] Log[B].        *)
  (*                                                                        *)
  (* Note: the kauers.m source omits the explicit I factor on the residual *)
  (* Log terms, which is a transcription error — without the I, the rule    *)
  (* fails the differentiation check on test inputs whose Im[a]+Im[b] != 0. *)
  ruleB = HoldPattern[a_ Log[A_] + b_ Log[B_]] /;
    FreeQ[a, x] && FreeQ[b, x] &&
    TrueQ[Re[a] != 0] &&
    TrueQ[Cancel[Re[a] + Re[b]] == 0] &&
    PossibleZeroQ[Cancel[(A + B)/2 + (A - B)/2 - A]] &&
    PossibleZeroQ[Cancel[(A + B)/2 - (A - B)/2 - B]] &&
    PossibleZeroQ[imagTerms[(A + B)/2, x]] &&
    PossibleZeroQ[realTerms[(A - B)/2, x]] &&
    !PossibleZeroQ[realTerms[(A + B)/2, x]] &&
    !PossibleZeroQ[imagTerms[(A - B)/2, x]] :>
    -2 I Re[a] arcTanTerm[realTerms[(A + B)/2, x],
                          imagTerms[(A - B)/2, x], x] +
    I Im[a] Log[A] + I Im[b] Log[B];

  {ruleA, ruleB}
];

(* ::Section:: *)
(* Public entry point                                                         *)
(*                                                                            *)
(* Apply both rules to fixed point. ReplaceRepeated (//.) is needed because  *)
(* a single Plus[] node may contain several conjugate pairs that are only    *)
(* uncovered after earlier rewrites finish.                                   *)

ClearAll[logsToArcTan];
logsToArcTan[expr_, x_Symbol] := Module[{rules},
  rules = logToArcTanRules[x];
  expr //. rules[[1]] //. rules[[2]]
];
