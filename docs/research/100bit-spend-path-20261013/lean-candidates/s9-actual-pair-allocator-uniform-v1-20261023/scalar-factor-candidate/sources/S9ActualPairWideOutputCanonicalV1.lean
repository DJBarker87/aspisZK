import S9ActualPairWideAddHelperTransportV1
import S9ActualPairMulM31HelperTransportV1
import S9ActualPairMixedSourceMapV1
import S9CombinedWideMulQM31HelperTotalExactV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualPairWideOutputCanonicalV1
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Q := aspis_core.field.QM31
abbrev Canonical := AspisR1S9ActualPairWideCanonicalV1.Canonical
abbrev toCurrent := AspisR1S9ActualPairWideCanonicalV1.toCurrent

theorem zero_canonical : Canonical
    AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.ZERO := by
  simp only [AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact.ZERO,
    AspisR1S9ProductionPairCutV1.aspis_core.field.QM31.ZERO]
  change ((0 < 2147483647 ∧ 0 < 2147483647) ∧
          (0 < 2147483647 ∧ 0 < 2147483647)) ∧
         ((0 < 2147483647 ∧ 0 < 2147483647) ∧
          (0 < 2147483647 ∧ 0 < 2147483647))
  decide


theorem add_success_canonical (x y z : W) (hx : Canonical x) (hy : Canonical y)
    (h : aspis_core.field.wide_exact.WideExact.add x y = .ok z) : Canonical z := by
  have hm := AspisR1S9ActualPairWideAddCurrentV1.actual_wide_add_maps_current x y hx hy
  rw [h] at hm
  have hc : AspisR1CurrentWide.field.wide_exact.WideExact.add (toCurrent x) (toCurrent y) =
      .ok (toCurrent z) := hm.symm
  obtain ⟨v,hv,hcan,_⟩ := AspisR1CurrentWide.Proof.wide_add_total_exact
    (toCurrent x) (toCurrent y) hx hy
  have heq : v = toCurrent z := Result.ok.inj (hv.symm.trans hc)
  rw [heq] at hcan
  exact hcan

theorem mul_m31_success_canonical (x z : W) (s : U32) (hx : Canonical x)
    (h : aspis_core.field.wide_exact.WideExact.mul_m31 x s = .ok z) : Canonical z := by
  have hm := AspisR1S9ActualPairMulM31CurrentV1.actual_wide_mul_m31_maps_current x s
  rw [h] at hm
  have hc : AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31 (toCurrent x) s =
      .ok (toCurrent z) := hm.symm
  exact (AspisR1CurrentWide.Proof.wide_mul_m31_success
    (toCurrent x) (toCurrent z) s hx hc).1

theorem mul_qm31_success_canonical (x z : W) (q : Q) (hx : Canonical x)
    (h : aspis_core.field.wide_exact.WideExact.mul_qm31 x q = .ok z) : Canonical z := by
  have hm := AspisR1S9ActualPairMixedSourceMapV1.wide_mul_qm31_maps x q
  rw [h] at hm
  have hc : AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31
      (AspisR1S9ActualPairMixedSourceMapV1.toActualWide x)
      (AspisR1S9ActualPairMixedSourceMapV1.toActualQM q) =
      .ok (AspisR1S9ActualPairMixedSourceMapV1.toActualWide z) := hm.symm
  obtain ⟨q',v,_,_,hv,hcan,_⟩ :=
    AspisR1S9CombinedWideMulQM31HelperTotalExactV1.combined_wide_mul_qm31_total_exact
      (AspisR1S9ActualPairMixedSourceMapV1.toActualWide x)
      (AspisR1S9ActualPairMixedSourceMapV1.toActualQM q) hx
  have heq : v = AspisR1S9ActualPairMixedSourceMapV1.toActualWide z :=
    Result.ok.inj (hv.symm.trans hc)
  rw [heq] at hcan
  exact hcan

#print axioms zero_canonical
#print axioms add_success_canonical
#print axioms mul_m31_success_canonical
#print axioms mul_qm31_success_canonical
end AspisR1S9ActualPairWideOutputCanonicalV1
