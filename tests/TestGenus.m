(* ::Package:: *)

(* ::Title:: *)
(* Tests for computeGenus *)

Get[FileNameJoin[{Directory[], "src", "Trager.m"}]];
Get[FileNameJoin[{Directory[], "tests", "TestHarness.m"}]];

tsection["computeGenus: genus-0 cases (our declared scope)"];

tassertEqual["y^2 = x^2 + 1", 0, computeGenus[2, x^2 + 1, x]];
tassertEqual["y^2 = x^2 - 1", 0, computeGenus[2, x^2 - 1, x]];
tassertEqual["y^2 = 1 - x^2", 0, computeGenus[2, 1 - x^2, x]];
tassertEqual["y^2 = x", 0, computeGenus[2, x, x]];
tassertEqual["y^3 = x", 0, computeGenus[3, x, x]];
tassertEqual["y^3 = x^2", 0, computeGenus[3, x^2, x]];
tassertEqual["y^3 = x^2 (1-x)", 0, computeGenus[3, x^2 (1 - x), x]];
tassertEqual["y^4 = x^3", 0, computeGenus[4, x^3, x]];
tassertEqual["y^4 = x (x-1)^3", 0, computeGenus[4, x*(x - 1)^3, x]];

tsection["computeGenus: positive genus (must return > 0)"];

(* y^2 = x^3 + 1 is elliptic (genus 1) *)
tassertEqual["y^2 = x^3 + 1 (elliptic)", 1, computeGenus[2, x^3 + 1, x]];

(* y^2 = x^3 - x (elliptic) *)
tassertEqual["y^2 = x^3 - x", 1, computeGenus[2, x^3 - x, x]];

(* y^2 = x^4 + 1 (elliptic after a transformation, but raw genus 1 via RH) *)
tassertEqual["y^2 = x^4 + 1", 1, computeGenus[2, x^4 + 1, x]];

(* y^2 = x^5 - x is hyperelliptic genus 2 *)
tassertEqual["y^2 = x^5 - x (hyperelliptic)", 2, computeGenus[2, x^5 - x, x]];

(* y^3 = x^2 + 1 is genus 1 *)
tassertEqual["y^3 = x^2 + 1", 1, computeGenus[3, x^2 + 1, x]];

(* y^3 = 1 - x^2 is genus 1 *)
tassertEqual["y^3 = 1 - x^2", 1, computeGenus[3, 1 - x^2, x]];

(* y^3 = x^4 - x (genus ?) *)
(* g = x(x-1)(x^2+x+1); factors m: (1,1), (1,1), (2,1)                     *)
(* finite = 1*(3-1) + 1*(3-1) + 2*(3-1) = 8                                *)
(* deg g = 4; gcd(3,4)=1; infty = 2                                         *)
(* 2g-2 = -6 + 8 + 2 = 4; g = 3                                             *)
tassertEqual["y^3 = x^4 - x", 3, computeGenus[3, x^4 - x, x]];

tsection["computeGenus: cross-check against plan's tier-4 genus-gate tests"];

tassertEqual["y^2 = x^3 + 1 (plan tier-4)", 1,
  computeGenus[2, x^3 + 1, x]];
tassertEqual["y^2 = x^4 + 1 (plan tier-4)", 1,
  computeGenus[2, x^4 + 1, x]];

tsection["computeGenus: degenerate input -> sentinel"];

tassertEqual["constant radicand returns -1", -1,
  computeGenus[2, 7, x]];
tassertEqual["n = 1 (non-integer via pattern) returns -1", -1,
  computeGenus[1, x + 1, x]];

tSummary[];
