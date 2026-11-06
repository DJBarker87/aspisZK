import NJS_Extract.Funs
import NGD_SlotModel
import Port4B_SlotInstall
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
 have cases : s=0#usize ∨ s=1#usize ∨ s=2#usize ∨ s=3#usize ∨ s=4#usize ∨ s=5#usize := by scalar_tac
 rcases cases with h|h|h|h|h|h
 all_goals subst s
 all_goals simp only [NJS_Extract.verifier.candidate.slot,
   NGD_SlotBoundaries.boundary0,NGD_SlotBoundaries.boundary1,
   NGD_SlotBoundaries.boundary2,NGD_SlotBoundaries.boundary3,
   NGD_SlotBoundaries.boundary4,NGD_SlotBoundaries.boundary5,
   NGD_SlotBoundaries.boundary6,lift,bind_tc_ok]
 all_goals rfl
#check source
#print axioms source
end NJS_Slot
