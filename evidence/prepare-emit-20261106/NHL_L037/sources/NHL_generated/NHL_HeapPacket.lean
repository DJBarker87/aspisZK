import NHL_Packets
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHL_HeapPacket
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

theorem rejected : NHL_Packets.filled false core.marker.CopyU8 14759#usize 0#u8=ok (.Err .Allocation) := by
 unfold NHL_Packets.filled
 rw [OraclePortStdAllocation.filled_exact]
 rfl

theorem accepted : ∃ logical : alloc.vec.Vec U8,
 NHL_Packets.filled true core.marker.CopyU8 14759#usize 0#u8=ok (.Ok logical) ∧ logical.val.length=14759 := by
 obtain ⟨logical,heap,size⟩ := NHF_HeapPrefix.outcome true
 refine ⟨logical,?_,size⟩
 unfold NHL_Packets.filled
 rw [heap,bind_tc_ok]

#print axioms rejected
#print axioms accepted
end AspisR1.NHL_HeapPacket
