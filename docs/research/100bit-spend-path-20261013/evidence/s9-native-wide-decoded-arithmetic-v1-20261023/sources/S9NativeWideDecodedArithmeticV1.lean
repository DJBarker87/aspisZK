import S9ActualPairWideAddCurrentV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9NativeWideDecodedArithmeticV1
open AspisR1S9ProductionPairCutV1
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Canonical := AspisR1S9ActualPairWideCanonicalV1.Canonical
abbrev toCurrent := AspisR1S9ActualPairWideCanonicalV1.toCurrent
abbrev decode (w : W) := AspisR1CurrentWide.Proof.decodeWide (toCurrent w)

/-- Reuse exact current-wide arithmetic for the same successful actual source
addition. Canonical inputs are explicit; no output contract is assumed. -/
theorem actual_add_success_decoded (x y out : W)
    (hx : Canonical x) (hy : Canonical y)
    (h : aspis_core.field.wide_exact.WideExact.add x y=.ok out) :
    Canonical out ∧ decode out=decode x+decode y := by
  have hm := AspisR1S9ActualPairWideAddCurrentV1.actual_wide_add_maps_current x y hx hy
  rw [h] at hm
  have hc : AspisR1CurrentWide.field.wide_exact.WideExact.add
      (toCurrent x) (toCurrent y)=.ok (toCurrent out) := hm.symm
  exact AspisR1CurrentWide.Proof.wide_add_success
    (toCurrent x) (toCurrent y) (toCurrent out) hx hy hc

/-- Reuse exact current-wide arithmetic for the same successful actual source
multiplication, with all canonical-output and decoded-value conclusions. -/
theorem actual_mul_success_decoded (x y out : W)
    (hx : Canonical x) (hy : Canonical y)
    (h : aspis_core.field.wide_exact.WideExact.mul x y=.ok out) :
    Canonical out ∧ decode out=decode x*decode y := by
  have hm := AspisR1S9ActualPairWideCanonicalV1.actual_wide_mul_maps_current x y hx hy
  rw [h] at hm
  have hc : AspisR1CurrentWide.field.wide_exact.WideExact.mul
      (toCurrent x) (toCurrent y)=.ok (toCurrent out) := hm.symm
  exact AspisR1CurrentWide.Proof.wide_mul_success_exact
    (toCurrent x) (toCurrent y) (toCurrent out) hx hy hc

#print axioms actual_add_success_decoded
#print axioms actual_mul_success_decoded
end AspisR1S9NativeWideDecodedArithmeticV1
