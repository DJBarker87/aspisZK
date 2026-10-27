import JGm_TX2_Supplied
import JGp_Slot0
import JGp_Slot1
import JGp_Slot2
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGu_Supplied
open Aeneas Aeneas.Std Result MultiproofConeRef
def nodes0 : Slice U8 := JGm_TX2_Supplied.leading JGp_Slot0.value 4416#usize
theorem length0 : nodes0.val.length=4416 :=
  JGm_TX2_Supplied.size _ _ (by rw [JGp_Slot0.length];decide)
#print axioms length0
def nodes1 : Slice U8 := JGm_TX2_Supplied.leading JGp_Slot1.value 4416#usize
theorem length1 : nodes1.val.length=4416 :=
  JGm_TX2_Supplied.size _ _ (by rw [JGp_Slot1.length];decide)
#print axioms length1
def nodes2 : Slice U8 := JGm_TX2_Supplied.leading JGp_Slot2.value 3840#usize
theorem length2 : nodes2.val.length=3840 :=
  JGm_TX2_Supplied.size _ _ (by rw [JGp_Slot2.length];decide)
#print axioms length2
end AspisR1.JGu_Supplied
end
