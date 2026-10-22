import S9WideAddTowerSourceMapV1
import S3S9ConcreteFieldOpsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideAddConcreteMapV1

abbrev SourceWide := AspisR1S9WideAddTowerSourceMapV1.SourceWide
abbrev HelperWide := AspisR1S9ConcreteFieldOpsV1.W
abbrev SourceCanonical := AspisR1S9WideAddTowerSourceMapV1.WideCanonical
abbrev HelperCanonical := AspisR1S9CurrentFieldOpsV1.Canonical

def toHelperWide := AspisR1S9WideAddTowerSourceMapV1.toHelperWide

/-- The transparent generated WideExact.add body returns the same value as the
installed concrete helper slot on canonical source operands. The returned value
is canonical in the helper's CurrentWide representation. -/
theorem source_wide_add_maps_to_concrete
    (x y : SourceWide) (hx : SourceCanonical x) (hy : SourceCanonical y) :
    ∃ z : SourceWide,
      AspisR1S9WideAddSourceBodyV1.field.wide_exact.WideExact.add x y = .ok z ∧
      @AspisR1S9HelperP6.FieldOps.wideAdd
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (toHelperWide x) (toHelperWide y) = .ok (toHelperWide z) ∧
      HelperCanonical (toHelperWide z) := by
  obtain ⟨z, hsource, hcurrent⟩ :=
    AspisR1S9WideAddTowerSourceMapV1.source_wide_add_maps_to_current x y hx hy
  have hxHelper : HelperCanonical (toHelperWide x) :=
    (AspisR1S9WideAddTowerSourceMapV1.source_wide_canonical_iff_helper x).mp hx
  have hyHelper : HelperCanonical (toHelperWide y) :=
    (AspisR1S9WideAddTowerSourceMapV1.source_wide_canonical_iff_helper y).mp hy
  obtain ⟨w, hw, hwCanonical, _hwDecode⟩ :=
    AspisR1S9CurrentFieldOpsV1.actualWideAdd_total_exact
      (toHelperWide x) (toHelperWide y) hxHelper hyHelper
  have htoE_x : AspisR1S9CurrentFieldOpsV1.toE (toHelperWide x) =
      AspisR1S9WideAddTowerSourceMapV1.toCurrentWide x := by
    rfl
  have htoE_y : AspisR1S9CurrentFieldOpsV1.toE (toHelperWide y) =
      AspisR1S9WideAddTowerSourceMapV1.toCurrentWide y := by
    rfl
  have hfromE_z : AspisR1S9CurrentFieldOpsV1.fromE
      (AspisR1S9WideAddTowerSourceMapV1.toCurrentWide z) = toHelperWide z := by
    rfl
  have hactual : AspisR1S9CurrentFieldOpsV1.actualWideAdd
      (toHelperWide x) (toHelperWide y) = .ok (toHelperWide z) := by
    unfold AspisR1S9CurrentFieldOpsV1.actualWideAdd
    simp only [htoE_x, htoE_y, hcurrent, bind_tc_ok, hfromE_z]
  have hslot : @AspisR1S9HelperP6.FieldOps.wideAdd
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (toHelperWide x) (toHelperWide y) = .ok (toHelperWide z) := by
    rw [AspisR1S9ConcreteFieldOpsV1.concrete_wideAdd_dispatch]
    exact hactual
  have heq : w = toHelperWide z :=
    Result.ok.inj (hw.symm.trans hactual)
  refine ⟨z, hsource, hslot, ?_⟩
  rw [← heq]
  exact hwCanonical

#print axioms source_wide_add_maps_to_concrete

end AspisR1S9WideAddConcreteMapV1
