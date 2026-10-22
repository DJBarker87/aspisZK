import S9WideAddConcreteMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideAddConcreteMeaningV1

open AspisR1S9WideAddConcreteMapV1

/-- Adds the existing CurrentWide semantic law to the same-result source/slot
bridge. The decoded equation and canonicality refer to the exact output returned
by both operations. -/
theorem source_wide_add_concrete_meaning
    (x y : SourceWide) (hx : SourceCanonical x) (hy : SourceCanonical y) :
    ∃ z : SourceWide,
      AspisR1S9WideAddSourceBodyV1.field.wide_exact.WideExact.add x y = .ok z ∧
      @AspisR1S9HelperP6.FieldOps.wideAdd
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (toHelperWide x) (toHelperWide y) = .ok (toHelperWide z) ∧
      HelperCanonical (toHelperWide z) ∧
      AspisR1S9CurrentFieldOpsV1.decode (toHelperWide z) =
        AspisR1S9CurrentFieldOpsV1.decode (toHelperWide x) +
        AspisR1S9CurrentFieldOpsV1.decode (toHelperWide y) := by
  obtain ⟨z, hsource, hslot, hcanonical⟩ :=
    source_wide_add_maps_to_concrete x y hx hy
  have hxHelper : HelperCanonical (toHelperWide x) :=
    (AspisR1S9WideAddTowerSourceMapV1.source_wide_canonical_iff_helper x).mp hx
  have hyHelper : HelperCanonical (toHelperWide y) :=
    (AspisR1S9WideAddTowerSourceMapV1.source_wide_canonical_iff_helper y).mp hy
  obtain ⟨w, hw, _hwCanonical, hwDecode⟩ :=
    AspisR1S9CurrentFieldOpsV1.actualWideAdd_total_exact
      (toHelperWide x) (toHelperWide y) hxHelper hyHelper
  have hslot' : AspisR1S9CurrentFieldOpsV1.actualWideAdd
      (toHelperWide x) (toHelperWide y) = .ok (toHelperWide z) := by
    rw [AspisR1S9ConcreteFieldOpsV1.concrete_wideAdd_dispatch] at hslot
    exact hslot
  have heq : w = toHelperWide z :=
    Result.ok.inj (hw.symm.trans hslot')
  refine ⟨z, hsource, hslot, hcanonical, ?_⟩
  rw [← heq]
  exact hwDecode

#print axioms source_wide_add_concrete_meaning

end AspisR1S9WideAddConcreteMeaningV1
