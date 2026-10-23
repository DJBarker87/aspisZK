import S9ActualPairWideCanonicalV1
import S3PowersCanonicalTraceV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualIndexedPowersArithmeticV1
open AspisR1S9ActualPairWideCanonicalV1

def decode (x : W) : AspisWideTower.WideExact := AspisR1CurrentWide.Proof.decodeWide (toCurrent x)

private theorem one_carrier :
    toCurrent AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.ONE =
      AspisR1PowersExactProduct.toFull AspisR1CurrentPowers.field.WideExact.ONE := by
  simp only [AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.ONE,
    AspisR1S9ProductionPairCutV1.aspis_core.field.QM31.ONE,
    AspisR1S9ProductionPairCutV1.aspis_core.field.QM31.ZERO,
    AspisR1CurrentPowers.field.WideExact.ONE,AspisR1CurrentPowers.field.QM31.ONE,
    AspisR1CurrentPowers.field.QM31.ZERO]
  rfl

/-- Reuse the old S3 field interpretation of ONE; no new concrete numeral
normalization or identity to the old FnMut control flow is asserted. -/
theorem one_canonical : Canonical
    AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.ONE := by
  change AspisR1CurrentWide.Proof.CanonicalWide
    (toCurrent AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.ONE)
  rw [one_carrier]
  exact AspisR1S3PowersCanonicalTraceV1.one_canonical

theorem one_decode : decode
    AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.ONE = 1 := by
  unfold decode
  rw [one_carrier]
  exact AspisR1S3PowersCanonicalTraceV1.one_decode

/-- Exact field product for the SAME successful actual native multiplication.
This reuses the complete current-source Result map and existing checked Wide
product proof, rather than assuming canonicality is an algebra theorem. -/
theorem mul_success_exact (x y z : W) (hx : Canonical x) (hy : Canonical y)
    (h : AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.mul x y = .ok z) :
    Canonical z ∧ decode z = decode x * decode y := by
  have hm := actual_wide_mul_maps_current x y hx hy
  rw [h] at hm
  have hr : AspisR1CurrentWide.field.wide_exact.WideExact.mul
      (toCurrent x) (toCurrent y) = .ok (toCurrent z) := hm.symm
  exact AspisR1CurrentWide.Proof.wide_mul_success_exact
    (toCurrent x) (toCurrent y) (toCurrent z) hx hy hr

#print axioms one_canonical
#print axioms one_decode
#print axioms mul_success_exact
end AspisR1S9ActualIndexedPowersArithmeticV1
