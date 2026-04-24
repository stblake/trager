(* ::Package:: *)

(* ::Title:: *)
(* Tests for shiftAwayFromInfinity *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

Off[IntegrateTrager::autoreduce];

(* Round-trip helper.                                                        *)
(* For an integrand f(x, y) dx and its forward-shifted form f~(z, y) dz,    *)
(* the identity                                                              *)
(*   inverse(f~) * (-1/(x - a)^2) ==  f(x, y)    (mod y^n -> g)             *)
(* must hold. The (-1/(x-a)^2) factor accounts for dz/dx = -z^2 evaluated   *)
(* at z = 1/(x-a).                                                           *)

roundTripOK[integrand_, x_Symbol, y_Symbol, n_Integer, g_, r_Association] := Module[
  {back, reducedBack, reducedOrig},
  back = r["inverse"][r["integrand"]] * (-1/(x - r["a"])^2);
  reducedBack = reduceYDegree[Together[back], x, y, n, g];
  reducedOrig = reduceYDegree[Together[integrand], x, y, n, g];
  TrueQ[Together[reducedBack - reducedOrig] === 0]
];

tsection["shiftAwayFromInfinity: basic case, y^2 = x^2 + 1"];

Module[{r},
  r = shiftAwayFromInfinity[1/y, x, y, 2, x^2 + 1, z];
  tassertEqual["a = 0 (g(0) nonzero)", 0, r["a"]];
  tassertEqual["n unchanged", 2, r["n"]];
  tassertEqual["gNew = 1 + z^2", 1 + z^2, Expand[r["g"]]];
  tassertEqual["yScale = z", z, Expand[r["yScale"]]];
  tassertEqual["genus preserved",
    0, computeGenus[r["n"], r["g"], z]];
  tassert["round-trip recovers integrand",
    roundTripOK[1/y, x, y, 2, x^2 + 1, r]];
];

tsection["shiftAwayFromInfinity: a = 0 when g(0) = 0 but gNew is non-constant"];

Module[{r},
  (* y^2 = x: a = 0 works even though g(0) = 0 -- the ceil scaling      *)
  (* produces gNew = z, a valid genus-0 curve.                            *)
  r = shiftAwayFromInfinity[1/y, x, y, 2, x, z];
  tassertEqual["a = 0 accepted (gNew still valid)", 0, r["a"]];
  tassertEqual["gNew = z", z, Expand[r["g"]]];
  tassertEqual["genus preserved", 0, computeGenus[r["n"], r["g"], z]];
  tassert["round-trip recovers integrand",
    roundTripOK[1/y, x, y, 2, x, r]];
];

tsection["shiftAwayFromInfinity: a-search skips denominator roots"];

Module[{r},
  (* Integrand 1/((x-2)*y) has denominator vanishing at x=2.                *)
  (* g(x) = x^2+1 has no rational root, so only the integrand denominator   *)
  (* rules out a = 2. a = 0 should still be picked.                         *)
  r = shiftAwayFromInfinity[1/((x - 2)*y), x, y, 2, x^2 + 1, z];
  tassertEqual["a = 0 OK for denominator (x-2)", 0, r["a"]];
  tassert["round-trip recovers integrand",
    roundTripOK[1/((x - 2)*y), x, y, 2, x^2 + 1, r]];
];

Module[{r},
  (* Integrand 1/(x*y), g = x^2 + 1: a = 0 excluded by denominator.         *)
  (* Next candidate a = 1.                                                  *)
  r = shiftAwayFromInfinity[1/(x*y), x, y, 2, x^2 + 1, z];
  tassertEqual["a = 1 (x=0 is denominator root)", 1, r["a"]];
  tassert["round-trip recovers integrand",
    roundTripOK[1/(x*y), x, y, 2, x^2 + 1, r]];
];

tsection["shiftAwayFromInfinity: ceil scaling (exercises kn - m > 0)"];

Module[{r},
  (* y^2 = x^3: m = 3, n = 2, k = ceil(3/2) = 2, kn-m = 1.                 *)
  (* G(z) = z^3 * (1/z)^3 = 1. gNew = z^1 * 1 = z.                         *)
  r = shiftAwayFromInfinity[1/y, x, y, 2, x^3, z];
  tassertEqual["a = 0 for y^2=x^3", 0, r["a"]];
  tassertEqual["gNew = z", z, Expand[r["g"]]];
  tassertEqual["yScale = z^2", z^2, Expand[r["yScale"]]];
  tassertEqual["genus preserved", 0, computeGenus[r["n"], r["g"], z]];
  tassert["round-trip recovers integrand",
    roundTripOK[1/y, x, y, 2, x^3, r]];
];

Module[{r},
  (* y^3 = x: m = 1, n = 3, k = 1, kn-m = 2.                               *)
  (* G(z) = z * (1/z) = 1. gNew = z^2.                                     *)
  r = shiftAwayFromInfinity[1/y, x, y, 3, x, z];
  tassertEqual["a = 0 for y^3=x", 0, r["a"]];
  tassertEqual["gNew = z^2", z^2, Expand[r["g"]]];
  tassert["round-trip recovers integrand",
    roundTripOK[1/y, x, y, 3, x, r]];
];

tsection["shiftAwayFromInfinity: y^3 = x^2 (plan tier-1)"];

Module[{r},
  (* m = 2, n = 3, k = 1, kn-m = 1. G = z^2 * (1/z)^2 = 1. gNew = z.       *)
  r = shiftAwayFromInfinity[1/y, x, y, 3, x^2, z];
  tassertEqual["a = 0", 0, r["a"]];
  tassertEqual["gNew = z", z, Expand[r["g"]]];
  tassertEqual["yScale = z", z, Expand[r["yScale"]]];
  tassert["round-trip recovers integrand",
    roundTripOK[1/y, x, y, 3, x^2, r]];
];

tsection["shiftAwayFromInfinity: y^4 = x^3 (plan tier-1)"];

Module[{r},
  (* m = 3, n = 4, k = 1, kn-m = 1. G = 1. gNew = z.                      *)
  r = shiftAwayFromInfinity[1/y, x, y, 4, x^3, z];
  tassertEqual["a = 0", 0, r["a"]];
  tassertEqual["gNew = z", z, Expand[r["g"]]];
  tassert["round-trip recovers integrand",
    roundTripOK[1/y, x, y, 4, x^3, r]];
];

tsection["shiftAwayFromInfinity: non-trivial integrand numerator"];

Module[{r, int},
  int = x/y;
  r = shiftAwayFromInfinity[int, x, y, 2, x^2 + 1, z];
  tassert["round-trip x/y on y^2=x^2+1",
    roundTripOK[int, x, y, 2, x^2 + 1, r]];
];

Module[{r, int},
  int = (x + y)/(x^2 + 1);
  r = shiftAwayFromInfinity[int, x, y, 2, x^2 + 1, z];
  tassert["round-trip (x+y)/(x^2+1) on y^2=x^2+1",
    roundTripOK[int, x, y, 2, x^2 + 1, r]];
];

Module[{r, int},
  int = y^2 / x;      (* y^2 will be reduced to x^3 on y^2=x^3 (cusp) *)
  r = shiftAwayFromInfinity[int, x, y, 2, x^3, z];
  tassert["round-trip y^2/x on y^2=x^3",
    roundTripOK[int, x, y, 2, x^3, r]];
];

tsection["shiftAwayFromInfinity: Mobius shift with a != 0"];

Module[{r, int},
  (* y^2 = (x-3)(x-4): a=0 is fine since g(0) = 12 != 0. Force a shift     *)
  (* by using an integrand pole at x=0.                                    *)
  int = 1/(x*y);
  r = shiftAwayFromInfinity[int, x, y, 2, (x - 3)*(x - 4), z];
  tassert["a != 0 produces valid shift",
    IntegerQ[r["a"]] && r["a"] =!= 0];
  tassertEqual["genus preserved",
    0, computeGenus[r["n"], r["g"], z]];
  tassert["round-trip on a != 0 case",
    roundTripOK[int, x, y, 2, (x - 3)*(x - 4), r]];
];

tsection["shiftAwayFromInfinity: reduceIrreducibility chaining"];

Module[{r},
  (* y^4 = x^2: m=2, n=4, k=1, kn-m=2. gNew_raw = z^2 * 1 = z^2.           *)
  (* reduceIrreducibility on (4, z^2): gcd(4,2)=2 -> n_new=2, g_new=z.     *)
  r = shiftAwayFromInfinity[1/y, x, y, 4, x^2, z];
  tassertEqual["n reduced from 4 to 2", 2, r["n"]];
  tassertEqual["gNew = z after reduction", z, Expand[r["g"]]];
];

tsection["shiftAwayFromInfinity: failure path"];

(* We can't easily construct InfinityShiftFailed for a small bound because   *)
(* g only has finitely many roots and the denominator only finitely many;   *)
(* with searchBound = 0 and an integrand that kills a = 0, it should fail. *)
Module[{r},
  r = shiftAwayFromInfinity[1/(x*y), x, y, 2, x, z, 0];
  tassertFailure["searchBound = 0 and a = 0 blocked -> fails",
    "InfinityShiftFailed", r];
];

On[IntegrateTrager::autoreduce];

tSummary[];
