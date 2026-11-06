import NJS_Extract.Funs
import NGD_SlotModel
import Port4B_SlotInstall
import Port3_Wrapping
set_option autoImplicit false
noncomputable section
namespace NJS_Slot
open Aeneas Aeneas.Std Result
open AspisR1
/-- Both scalar child calls are instantiated with the CLOSED offset theorem.
The borrowed view retains the full Result of the actual checked slice operation. -/
theorem source (proof : Slice U8) (s : Usize) (small : s.val<6) :
 NJS_Extract.verifier.candidate.slot NGD_SlotRef.slot_offset proof s =
 Port4B_SlotInstall.nodeSlot proof s := by
 have nextval : (Usize.wrapping_add s 1#usize).val=s.val+1 :=
   Port3_Wrapping.increment s (by omega)
 have nextbound : (Usize.wrapping_add s 1#usize).val≤6 := by omega
 have off : Port4B_SlotInstall.offset (Usize.wrapping_add s 1#usize).val nextbound =
     Port4B_SlotInstall.offset (s.val+1) (by omega) := by
   apply UScalar.eq_of_val_eq
   change OraclePortSelectedDraft.slotStart _ = OraclePortSelectedDraft.slotStart _
   rw [nextval]
 simp only [NJS_Extract.verifier.candidate.slot,NGD_SlotModel.reference s (by omega),
   NGD_SlotModel.reference _ nextbound,lift,bind_tc_ok,
   Port4B_SlotInstall.nodeSlot,dif_pos small,off]
#check source
#print axioms source
end NJS_Slot
