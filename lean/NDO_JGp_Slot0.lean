import Port4B_SlotInstall
import NDO_JFw_Range
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGp_Slot0
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.proofBytes JFw_Frames.window

def value : Slice U8 := JFw_Frames.window 28359 4672
theorem length : value.length=4672 := JFw_Frames.window_length 28359 4672 (by decide)
#print axioms length

theorem source : Port4B_SlotInstall.nodeSlot JFx_NativeBytes.proof 0#usize=ok value := by
  unfold Port4B_SlotInstall.nodeSlot
  erw [dif_pos (show (0#usize).val<6 by decide)]
  have start : Port4B_SlotInstall.offset (0#usize).val (by decide)=28359#usize := by
    apply UScalar.eq_of_val_eq
    rfl
  have finish : Port4B_SlotInstall.offset ((0#usize).val+1) (by decide)=33031#usize := by
    apply UScalar.eq_of_val_eq
    rfl
  erw [start,finish]
  have read := JFw_Range.read 28359#usize 33031#usize (by decide) (by decide)
  exact read
#print axioms source
end AspisR1.JGp_Slot0
end
