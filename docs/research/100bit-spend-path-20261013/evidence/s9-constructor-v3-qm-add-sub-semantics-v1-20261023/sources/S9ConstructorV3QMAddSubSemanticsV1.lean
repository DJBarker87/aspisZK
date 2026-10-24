import S9ConstructorV3QMAddSubMapV1
import S9ConstructorV3QMMulSemanticsV1
import S9WideSourceQMCurrentOpsV1
import CurrentWideQMField
import CurrentWideQMSubV5

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ConstructorV3QMAddSubSemanticsV1
abbrev S := AspisR1S9ConstructorV3QMMulSemanticsV1.SourceQM
abbrev toActualQM := AspisR1S9ConstructorV3QMMulSemanticsV1.toActualQM
abbrev Can := AspisR1S9ConstructorV3QMMulSemanticsV1.Can
abbrev decode := AspisR1S9ConstructorV3QMMulSemanticsV1.decode
abbrev toCurrent (x : S) := AspisR1S9WideSourceQMCurrentOpsV1.qToCurrent (toActualQM x)

/-- This same accepted constructor add call has the existing exact-tower meaning. -/
theorem generated_add_success_exact (x y z : S) (hx : Can x) (hy : Can y)
    (hcall : AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.add x y = .ok z) :
    Can z ∧ decode z = decode x + decode y := by
  have hm := AspisR1S9ConstructorV3QMAddSubMapV1.qm_add_maps x y
  rw [hcall] at hm
  have hcut : AspisR1S9WideSourceQMAddV1.qcutQMAdd (toActualQM x) (toActualQM y) =
      .ok (toActualQM z) := hm.symm
  have hcurrent := AspisR1S9WideSourceQMCurrentOpsV1.qcut_qm_add_maps_to_current
    (toActualQM x) (toActualQM y) hx hy
  rw [hcut] at hcurrent
  have hs : AspisR1CurrentWide.field.QM31.add (toCurrent x) (toCurrent y) =
      .ok (toCurrent z) := hcurrent.symm
  exact AspisR1CurrentWide.Proof.qm_add_success
    (toCurrent x) (toCurrent y) (toCurrent z) hx hy hs
#print axioms generated_add_success_exact

/-- This same accepted constructor sub call has the existing exact-tower meaning. -/
theorem generated_sub_success_exact (x y z : S) (hx : Can x) (hy : Can y)
    (hcall : AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.sub x y = .ok z) :
    Can z ∧ decode z = decode x - decode y := by
  have hm := AspisR1S9ConstructorV3QMAddSubMapV1.qm_sub_maps x y
  rw [hcall] at hm
  have hcut : AspisR1S9WideSourceQMSubV1.qcutQMSub (toActualQM x) (toActualQM y) =
      .ok (toActualQM z) := hm.symm
  have hcurrent := AspisR1S9WideSourceQMCurrentOpsV1.qcut_qm_sub_maps_to_current
    (toActualQM x) (toActualQM y) hx hy
  rw [hcut] at hcurrent
  have hs : AspisR1CurrentWide.field.QM31.sub (toCurrent x) (toCurrent y) =
      .ok (toCurrent z) := hcurrent.symm
  exact AspisR1CurrentWide.Proof.qm_sub_success
    (toCurrent x) (toCurrent y) (toCurrent z) hx hy hs
#print axioms generated_sub_success_exact

end AspisR1S9ConstructorV3QMAddSubSemanticsV1
