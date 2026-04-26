(* ::Package:: *)

(* ::Title:: *)
(* Trager — algebraic integration via Trager's algorithm                    *)

(* ::Text:: *)
(* Wraps the implementation as a single Mathematica package whose only      *)
(* public symbol is IntegrateTrager. All helper functions live in           *)
(* Trager`Private` and are not exposed via $ContextPath.                    *)
(*                                                                           *)
(* Public API                                                                *)
(*   IntegrateTrager[f, {x, y, y^n == g}]                                   *)
(*   IntegrateTrager[f, x]   (* surface-syntax form, auto-detects radical *)*)
(*                                                                           *)
(* Loading                                                                    *)
(*   Get["/absolute/path/to/src/Trager.m"]                                  *)
(*   or after SetDirectory[...]: Get["Trager.m"].                          *)
(*                                                                           *)
(* Reference                                                                 *)
(*   Trager, "Integration of Algebraic Functions", MIT Ph.D. thesis (1984).*)
(*   The chapter / section structure of the thesis is preserved across the *)
(*   internal source files (Phase 0 = Ch 3 §3, Phase 1 = Ch 2 §5,           *)
(*   Phase 2 = Ch 4 §3, Phase 3 = Ch 4 §2, Phase 4 = Ch 5 §2,               *)
(*   Phase 5 = Ch 5–6, Phase 6 = composite reassembly).                     *)

BeginPackage["Trager`"];

IntegrateTrager::usage =
  "IntegrateTrager[f, {x, y, y^n == g}] integrates an algebraic function f \
that is rational in (x, y), where y is a simple radical satisfying y^n = g(x) \
with g in Q[x] and n an integer >= 2. Returns an elementary antiderivative \
or a Failure[...] object on out-of-scope or non-elementary input.\n\n\
IntegrateTrager[f, x] auto-detects a single algebraic radical pattern \
f^(k/n) in the integrand and delegates to the three-argument form.\n\n\
Options include \"LogTermsMethod\" -> \"Trager\" | \"Miller\" | \"Kauers\" \
to select between the three log-part construction algorithms (Trager 1984 \
Ch 5; Miller 2012; Kauers 2008). See documentation in src/IntegrateTrager.m.";

Begin["`Private`"];

$TragerRoot = DirectoryName[
  If[$InputFileName === "" || $InputFileName === Null,
    (* interactive load: fall back to the current directory *)
    FileNameJoin[{Directory[], "Trager.m"}],
    $InputFileName
  ]
];

(* Load order — Trager 1984 chapter / section mapping in parentheses:        *)
(*   Common.m              — utilities (Failure helpers, type predicates)    *)
(*   Validate.m            — Phase 0 input validation                         *)
(*   Reduce.m              — Phase 0 (Ch 3 §3 absolute irreducibility)       *)
(*   Genus.m               — Ch 2 §4 genus computation                       *)
(*   Basis.m               — Ch 2 §5 simple-radical integral basis           *)
(*   Arithmetic.m          — Ch 2 AF arithmetic on integral basis            *)
(*   Shift.m               — Phase 2 (Ch 4 §3 poles at infinity)             *)
(*   Hermite.m             — Phase 3 (Ch 4 §2 algebraic Hermite reduction)   *)
(*   Residues.m            — Phase 4 (Ch 5 §2 Rothstein-Trager residues)     *)
(*   Normalize.m           — Ch 2 §3 normal at infinity (HNF + correction)   *)
(*   Divisor.m             — Ch 5 §3 divisor construction                    *)
(*   PlaceOrder.m          — Ch 5 §1 + §4 places, branch valuations          *)
(*   PrincipalGen.m        — Ch 6 §1 principal divisor generator             *)
(*   Torsion.m             — Ch 6 §3 divisor reduction (torsion bound)       *)
(*   TragerLogTerms.m      — Phase 5 Trager method (Ch 5 + Ch 6)             *)
(*   IdealDecomposition.m  — supports Miller method (Becker-Weispfenning)    *)
(*   MillerKauersLogTerms.m — Phase 5 Miller method (Miller 2012)            *)
(*   KauersLogTerms.m      — Phase 5 Kauers method (Kauers 2008)             *)
(*   LogToArcTan.m         — Phase 6 conjugate-log -> ArcTan rewrite          *)
(*   Reassemble.m          — Phase 6 Möbius and rescale inversions           *)
(*   IntegrateTrager.m     — top-level pipeline (Ch 1 §2 outline)            *)
(*   Surface.m             — surface-syntax `IntegrateTrager[f, x]`         *)

Get[FileNameJoin[{$TragerRoot, "Common.m"}]];
Get[FileNameJoin[{$TragerRoot, "Validate.m"}]];
Get[FileNameJoin[{$TragerRoot, "Reduce.m"}]];
Get[FileNameJoin[{$TragerRoot, "Genus.m"}]];
Get[FileNameJoin[{$TragerRoot, "Basis.m"}]];
Get[FileNameJoin[{$TragerRoot, "Arithmetic.m"}]];
Get[FileNameJoin[{$TragerRoot, "Shift.m"}]];
Get[FileNameJoin[{$TragerRoot, "Hermite.m"}]];
Get[FileNameJoin[{$TragerRoot, "Residues.m"}]];
Get[FileNameJoin[{$TragerRoot, "Normalize.m"}]];
Get[FileNameJoin[{$TragerRoot, "Divisor.m"}]];
Get[FileNameJoin[{$TragerRoot, "SchultzDivisor.m"}]];
Get[FileNameJoin[{$TragerRoot, "SchultzPrincipal.m"}]];
Get[FileNameJoin[{$TragerRoot, "SchultzHermite.m"}]];
Get[FileNameJoin[{$TragerRoot, "SchultzPlaces.m"}]];
Get[FileNameJoin[{$TragerRoot, "SchultzResidueDivisor.m"}]];
Get[FileNameJoin[{$TragerRoot, "SchultzResidues.m"}]];
Get[FileNameJoin[{$TragerRoot, "PlaceOrder.m"}]];
Get[FileNameJoin[{$TragerRoot, "PrincipalGen.m"}]];
Get[FileNameJoin[{$TragerRoot, "Torsion.m"}]];
Get[FileNameJoin[{$TragerRoot, "TragerLogTerms.m"}]];
Get[FileNameJoin[{$TragerRoot, "SchultzLogTerms.m"}]];
Get[FileNameJoin[{$TragerRoot, "SchultzFailStyle.m"}]];
Get[FileNameJoin[{$TragerRoot, "IdealDecomposition.m"}]];
Get[FileNameJoin[{$TragerRoot, "MillerKauersLogTerms.m"}]];
Get[FileNameJoin[{$TragerRoot, "KauersLogTerms.m"}]];
Get[FileNameJoin[{$TragerRoot, "LogToArcTan.m"}]];
Get[FileNameJoin[{$TragerRoot, "Reassemble.m"}]];
Get[FileNameJoin[{$TragerRoot, "SchultzPipeline.m"}]];
Get[FileNameJoin[{$TragerRoot, "IntegrateTrager.m"}]];
Get[FileNameJoin[{$TragerRoot, "Surface.m"}]];

End[];   (* `Private` *)

EndPackage[];
