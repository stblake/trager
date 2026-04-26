(* ::Package:: *)

(* ::Title:: *)
(* Tests for the Schultz §S.6.2 fail-in-style certificate (deferred body). *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

(* ::Section:: *)
(* Stub-level shape checks. complementaryInfinityBasis and                      *)
(* secondKindNormalForms are deferred (Sch Lemma 4.2, 5.5) and currently       *)
(* return Missing["NotImplemented", ...] descriptors. schultzFailInStyle       *)
(* should produce a Failure["NonElementary"] with certificate keys present     *)
(* and the deferred fields filled with the same Missing[] values.               *)

tsection["complementaryInfinityBasis: deferred"];

Module[{basis, eps},
  basis = buildIntegralBasis[2, x^3 + 1, x];
  eps = complementaryInfinityBasis[basis];
  tassert["returns a Missing[] descriptor",
    MatchQ[eps, _Missing]];
  tassertEqual["Missing tag is NotImplemented",
    "NotImplemented", eps[[1]]];
];

tsection["secondKindNormalForms: deferred"];

Module[{basis, gammas},
  basis = buildIntegralBasis[2, x^3 + 1, x];
  gammas = secondKindNormalForms[basis];
  tassert["returns a Missing[] descriptor",
    MatchQ[gammas, _Missing]];
];

(* ::Section:: *)
(* schultzFailInStyle assembles a structured Failure["NonElementary"] even      *)
(* though the underlying Lemma 5.5 is deferred — the certificate has all      *)
(* expected keys with Missing[] placeholders, ready for downstream callers    *)
(* to inspect.                                                                  *)

tsection["schultzFailInStyle: structured certificate Failure"];

Module[{basis, integrandAF, b, fail, cert},
  basis = buildIntegralBasis[2, x^2 + 1, x];
  integrandAF = afMake[{0, 1/(x^2 + 1)}, basis];
  b = x^2 + 1;
  fail = schultzFailInStyle[integrandAF, b, basis, y,
    <|"Reason" -> "test invocation"|>];
  tassertFailure["returns Failure[NonElementary]", "NonElementary", fail];
  tassertEqual["Method tag is Schultz", "Schultz", fail[[2]]["Method"]];
  cert = fail[[2]]["Certificate"];
  tassert["Certificate is an Association",
    AssociationQ[cert]];
  tassert["Certificate has gamma key", KeyExistsQ[cert, "gamma"]];
  tassert["Certificate has coeffs key", KeyExistsQ[cert, "coeffs"]];
  tassert["Certificate has firstKindResidual key",
    KeyExistsQ[cert, "firstKindResidual"]];
  tassert["Certificate has logTerms key", KeyExistsQ[cert, "logTerms"]];
  tassert["gamma is currently Missing[NotImplemented]",
    MatchQ[cert["gamma"], _Missing]];
];

tSummary[];
