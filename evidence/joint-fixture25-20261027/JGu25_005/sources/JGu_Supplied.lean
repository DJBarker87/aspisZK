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
  JGm_TX2_Supplied.size _ _ (by change (4416:Nat)≤JGp_Slot0.value.val.length; have len : JGp_Slot0.value.val.length=4672 := JGp_Slot0.length; rw [len];decide)
#print axioms length0
def nodes1 : Slice U8 := JGm_TX2_Supplied.leading JGp_Slot1.value 4416#usize
theorem length1 : nodes1.val.length=4416 :=
  JGm_TX2_Supplied.size _ _ (by change (4416:Nat)≤JGp_Slot1.value.val.length; have len : JGp_Slot1.value.val.length=4672 := JGp_Slot1.length; rw [len];decide)
#print axioms length1
def nodes2 : Slice U8 := JGm_TX2_Supplied.leading JGp_Slot2.value 3840#usize
theorem length2 : nodes2.val.length=3840 :=
  JGm_TX2_Supplied.size _ _ (by change (3840:Nat)≤JGp_Slot2.value.val.length; have len : JGp_Slot2.value.val.length=4096 := JGp_Slot2.length; rw [len];decide)
#print axioms length2
end AspisR1.JGu_Supplied
end
