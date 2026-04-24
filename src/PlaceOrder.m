(* ::Package:: *)

(* ::Title:: *)
(* Order of an AF element at a specific place; principal-generator verification *)

(* ::Text:: *)
(* Port of the missing correctness check in findPrincipalGenerator.           *)
(*                                                                           *)
(* The two-phase HNF + normalizeAtInfinity reduction in PrincipalGen.m       *)
(* produces a K[z]-basis of the I_D module and then picks the first row that *)
(* is integral at infinity. In genus 0 this is always the principal generator*)
(* (up to a K[z]-unit), but in higher genus I_D can contain MULTIPLE         *)
(* integral-at-infinity elements whose divisors are distinct degree-0        *)
(* divisors — only one of which equals D.                                    *)
(*                                                                           *)
(* Example (y^4 = 1+z^4, D = (0,1) − (0,-1)): at k=3 the scan finds          *)
(*    v = -z / (y+1)                                                        *)
(* whose divisor is (0,1) + (0,i) + (0,-i) − 3·(0,-1), NOT 3·D. torsionIfCan *)
(* then wrongly stops at k=3 before reaching the true torsion order k=4      *)
(* where v = (y-1)/(y+1) is the actual generator.                           *)
(*                                                                           *)
(* The remedy implemented here: after each candidate row is found, verify    *)
(* ord_P(v) = k · ord_P(D) at every place P over supp(A). Non-branch places *)
(* (g(β) ≠ 0) are handled via a local Taylor expansion of y(z). Branch       *)
(* places (g(β) = 0) use a simplified constant-value check, which is exact  *)
(* when the candidate is a local unit at the branch place — the common case.*)
(*                                                                           *)
(* See TragerPlan.md §14 and §17, Trager Ch 6 §1 (principal generator),     *)
(* Trager Ch 5 §4 (branch-place residue = 0 for simple radicals).           *)

(* ::Section:: *)
(* afOrderAtNonBranchPlace                                                   *)
(*                                                                           *)
(* At a non-branch place P = (β, y_β) with g(β) ≠ 0 and y_β^n = g(β), the   *)
(* local uniformizer is t = z − β and y has a Taylor expansion              *)
(*    y(β + t) = y_β · (g(β + t) / g(β))^{1/n}                              *)
(* (a power series in t with constant term y_β). Substituting into the AF   *)
(* element Σ c_j(z) · y^j / d_j(z) gives a Laurent series in t whose        *)
(* leading exponent is ord_P(v).                                             *)
(*                                                                           *)
(* The `initialSeriesOrder` defaults to 8; if the resulting series is       *)
(* identically zero within that truncation we double and retry, up to a    *)
(* cap — a truly zero element returns Infinity.                             *)

ClearAll[afOrderAtNonBranchPlace];
afOrderAtNonBranchPlace[af_?afElementQ, beta_, yBeta_,
                        basis_?basisDescriptorQ, y_Symbol,
                        initialSeriesOrder_Integer: 8] := Module[
  {n, z, g, d, t, gBeta, fT, ySeries, cSeries, djSeries, total,
   seriesOrd, maxRetry, leadingExp, den},

  n = basis["n"]; z = basis["x"]; g = basis["g"]; d = basis["d"];
  gBeta = Together[g /. z -> beta];

  If[zeroQ[gBeta],
    Return[$Failed]
  ];

  seriesOrd = initialSeriesOrder;
  maxRetry  = 4;   (* double up to 128 terms worth *)

  t = Unique["pTrag"];

  While[maxRetry > 0,
    Module[{result, fTExpanded},
      fTExpanded = Together[(g /. z -> beta + t) / gBeta];
      ySeries    = yBeta * Series[fTExpanded^(1/n), {t, 0, seriesOrd}];

      total = Sum[
        Module[{cj = af["Coeffs"][[j + 1]], dj = d[[j + 1]]},
          cSeries  = Series[cj /. z -> beta + t, {t, 0, seriesOrd}];
          djSeries = Series[dj /. z -> beta + t, {t, 0, seriesOrd}];
          cSeries / djSeries * ySeries^j
        ],
        {j, 0, n - 1}
      ];

      total = total + O[t]^(seriesOrd + 1);

      Which[
        total === 0, Return[Infinity],
        Head[total] === SeriesData,
          If[AllTrue[total[[3]], zeroQ],
            seriesOrd *= 2;
            maxRetry -= 1,
            leadingExp = total[[4]];
            den        = total[[6]];
            Return[leadingExp / den]
          ],
        True,
          (* Constant (or polynomial in t with nonzero constant term after *)
          (* normalization) => order 0 at this place.                        *)
          Return[0]
      ]
    ]
  ];

  Infinity
];

(* ::Section:: *)
(* afValueAt -- evaluate an AF element as a K(z, y) expression at a point   *)
(*                                                                           *)
(* Used for branch-place heuristic and for testing membership in supp(div). *)

ClearAll[afValueAt];
afValueAt[af_?afElementQ, beta_, yBetaVal_, basis_?basisDescriptorQ,
          y_Symbol] := Module[
  {std, val},
  std = afToStandard[af, basis, y];
  val = std /. {basis["x"] -> beta, y -> yBetaVal};
  Simplify[val]
];

(* ::Section:: *)
(* afOrderAtBranchPlace                                                     *)
(*                                                                           *)
(* At a simple branch place (β, 0) with g(β) = 0, mult_β(g) = 1, the       *)
(* local structure is ramified of index n: uniformizer s satisfies s^n =   *)
(* (z − β) · u for a unit u, and y ∼ s · v for a unit v.                   *)
(*                                                                           *)
(* A rigorous order computation involves a Puiseux expansion with fractional*)
(* exponents and is heavier than the non-branch case. For the residue-     *)
(* divisor verification we use the fact that most candidate generators are *)
(* UNITS at branch places (neither zero nor pole there), so a simple value  *)
(* check suffices: if afValueAt[af, β, 0] is a finite nonzero expression,  *)
(* the order is 0 — which matches the expected order for k·D on divisors   *)
(* whose support avoids branch places (the case for simple-radical         *)
(* residues per Trager Ch 5 §4).                                            *)
(*                                                                           *)
(* Return values:                                                            *)
(*   0          — confirmed unit (nonzero finite value at (β, 0))            *)
(*   $Unknown   — value is zero or undefined; finer analysis needed.        *)

ClearAll[afOrderAtBranchPlace];
afOrderAtBranchPlace[af_?afElementQ, beta_, basis_?basisDescriptorQ,
                     y_Symbol] := Module[
  {val, num, den, denAtBeta},
  val = afValueAt[af, beta, 0, basis, y];
  val = Together[val];
  num = Numerator[val];
  den = Denominator[val];
  denAtBeta = Together[den /. basis["x"] -> beta];
  Which[
    zeroQ[denAtBeta], $Unknown,    (* denominator vanishes at β *)
    zeroQ[num],       $Unknown,    (* numerator vanishes at β  *)
    True,                     0
  ]
];

(* ::Section:: *)
(* enumeratePlacesOverA -- list of (β, y_β, isBranch) for A's root places *)
(*                                                                           *)
(* Factor A over Q, then for each irreducible factor p of degree d:         *)
(*   - If d == 1: β is the rational root of p.                              *)
(*   - If d > 1:  β is represented as Root[p, k] for k = 1..d.              *)
(* At each β, g(β) determines branch vs. non-branch:                        *)
(*   - g(β) = 0: ONE place (β, 0), isBranch -> True.                         *)
(*   - g(β) ≠ 0: n places (β, y_β) for each y_β^n = g(β).                    *)
(*                                                                           *)
(* y_β values: we enumerate `Solve[y^n == gβ, y]` which gives symbolic/     *)
(* radical/Root form depending on the degree. For n up to 4 Mathematica     *)
(* typically returns radicals.                                               *)

ClearAll[rootsOfPolyInZ];
rootsOfPolyInZ[p_, z_Symbol] := Module[{deg, coeffs},
  deg = Exponent[p, z];
  Which[
    deg === 0, {},
    deg === 1,
      {Together[-Coefficient[p, z, 0] / Coefficient[p, z, 1]]},
    True,
      coeffs = CoefficientList[p, z];
      Table[
        Root[
          Evaluate[Sum[coeffs[[i]] * Slot[1]^(i - 1), {i, Length[coeffs]}]] &,
          k
        ],
        {k, deg}
      ]
  ]
];

ClearAll[enumeratePlacesOverA];
enumeratePlacesOverA[A_, basis_?basisDescriptorQ, y_Symbol] := Module[
  {z, n, g, factors, places},

  z = basis["x"]; n = basis["n"]; g = basis["g"];
  factors = First /@ Rest[FactorList[A]];
  places = {};

  Do[
    Module[{p = factor, roots, beta, gBeta, yVals},
      roots = rootsOfPolyInZ[p, z];

      Do[
        beta  = betaRoot;
        gBeta = Together[g /. z -> beta];
        If[zeroQ[gBeta],
          AppendTo[places,
            <|"beta" -> beta, "yBeta" -> 0, "isBranch" -> True|>],
          yVals = y /. Solve[y^n == gBeta, y];
          Do[
            AppendTo[places,
              <|"beta" -> beta, "yBeta" -> yb, "isBranch" -> False|>],
            {yb, yVals}
          ]
        ],
        {betaRoot, roots}
      ]
    ],
    {factor, factors}
  ];

  places
];

(* ::Section:: *)
(* verifyPrincipalGeneratorForPair                                          *)
(*                                                                           *)
(* Given a candidate v (AF element) claimed to be a principal generator of  *)
(* k · (div1 − div2), verify:                                                *)
(*    ord_P(v) == k · (1 if P ∈ supp(div1), −1 if P ∈ supp(div2), 0 else)   *)
(* at every place P over supp(A). div1 and div2 are assumed to share the    *)
(* same A (= Dpoly) — the standard situation for Phase-4 residue divisors.  *)
(*                                                                           *)
(* Membership in supp(div_i) is decided by evaluating div_i.h (in standard  *)
(* form) at (β, y_β): zero iff the place is in the support.                 *)
(*                                                                           *)
(* At branch places we only verify ord = 0 (unit). If the expected order is *)
(* nonzero at a branch place, or the branch-place evaluation is ambiguous,  *)
(* we fall back to an undetermined result which torsionIfCan treats         *)
(* conservatively (continues to higher k).                                   *)
(*                                                                           *)
(* Returns True on confirmed match, False on confirmed mismatch, $Unknown   *)
(* when branch-place analysis was inconclusive (rare — typically means the  *)
(* AF element has an unexpected branch-place zero).                          *)

ClearAll[verifyPrincipalGeneratorForPair];
verifyPrincipalGeneratorForPair[v_?afElementQ,
                                div1_?divisorQ, div2_?divisorQ,
                                k_Integer,
                                basis_?basisDescriptorQ, y_Symbol] := Catch[
  Module[{A, places, h1Val, h2Val, inSupp1, inSupp2, expOrd, actOrd,
          branchResult, unknownSeen = False},

    A = div1["A"];

    places = enumeratePlacesOverA[A, basis, y];

    Do[
      Module[{beta = place["beta"], yBeta = place["yBeta"],
              isBranch = place["isBranch"]},

        h1Val = afValueAt[div1["h"], beta, yBeta, basis, y];
        h2Val = afValueAt[div2["h"], beta, yBeta, basis, y];

        inSupp1 = zeroQ[h1Val];
        inSupp2 = zeroQ[h2Val];

        expOrd = k * (If[inSupp1, 1, 0] - If[inSupp2, 1, 0]);

        If[isBranch,
          (* Branch-place simple check. *)
          If[expOrd =!= 0,
            (* Support at a branch place -- simple check insufficient. *)
            unknownSeen = True;
            Continue[]
          ];
          branchResult = afOrderAtBranchPlace[v, beta, basis, y];
          Which[
            branchResult === 0, Null, (* confirmed unit; ok *)
            branchResult === $Unknown, unknownSeen = True; Continue[],
            True, Throw[False]
          ],

          (* Non-branch place: exact ord via Series. *)
          actOrd = afOrderAtNonBranchPlace[v, beta, yBeta, basis, y];
          If[actOrd === $Failed,
            (* Should not happen for non-branch; treat as unknown. *)
            unknownSeen = True; Continue[]
          ];
          actOrd = Simplify[actOrd];
          If[TrueQ[actOrd =!= expOrd],
            Throw[False]
          ]
        ]
      ],
      {place, places}
    ];

    If[unknownSeen, $Unknown, True]
  ]
];
