import NHL_Packets
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHL_ValuesPacket
open Aeneas Aeneas.Std Result

theorem accepted (input before after : Slice U8)
 (child : NFU_Retarget.compact.expand_values input before=ok (.Ok (),after)) :
 NHL_Packets.values input before=ok (.Ok (),after) := by
 unfold NHL_Packets.values
 rw [child,bind_tc_ok]
 rfl

theorem length (input before : Slice U8) (inputSize : input.val.length=464) (beforeSize : before.val.length=928) :
 ∃ after, NHL_Packets.values input before=ok (.Ok (),after) ∧ after.val.length=928 := by
 obtain ⟨after,call,_,size,_⟩ := NGV_ExpandAssociation.result input before
   (by omega) (by rw [inputSize]) (by rw [inputSize,beforeSize])
 exact ⟨after,accepted input before after call,size.trans beforeSize⟩
#print axioms accepted
#print axioms length
end AspisR1.NHL_ValuesPacket
