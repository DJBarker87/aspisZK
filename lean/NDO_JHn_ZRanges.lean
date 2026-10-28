import NDO_JHl_ZBytes
import NDO_JHn_Ranges
set_option autoImplicit false
namespace AspisR1.JHn_ZRanges
open Aeneas Aeneas.Std
attribute [local irreducible] JFx_NativeBytes.checkpoint JFx_NativeBytes.checkpointBytes
theorem source : JFq_Z0.bytes ++ JFq_Z1.bytes ++ JFq_Z2.bytes ++ JFq_Z3.bytes =
    (JFx_NativeBytes.checkpoint.val.drop 568).take 64 := by
  rw [←JFq_Z0.selected,←JFq_Z1.selected,←JFq_Z2.selected,←JFq_Z3.selected]
  rw [JHn_Ranges.adjacent _ 568 16 16,JHn_Ranges.adjacent _ 568 32 16,JHn_Ranges.adjacent _ 568 48 16]
#print axioms source
end AspisR1.JHn_ZRanges
