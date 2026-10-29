import R1Z.PV_OWNC_GuardState
set_option autoImplicit false
namespace R1Z.PV_OWNC_HeaderStores
open PV_OWNC_SourceIterator PV_OWNC_GuardState
/-- Each of the four source header stores is explicit; none changes the saved
remaining slice or the allocation owned by the separate destination guard. -/
theorem cap (h : Header) :
 (clearCap h).cap=0 ∧ (clearCap h).buf=h.buf ∧
 (clearCap h).ptr=h.ptr ∧ (clearCap h).endPtr=h.endPtr := ⟨rfl,rfl,rfl,rfl⟩
theorem buf (h : Header) :
 (clearBuf (clearCap h)).buf=2 ∧ (clearBuf (clearCap h)).cap=0 := ⟨rfl,rfl⟩
theorem ptr (h : Header) :
 (clearPtr (clearBuf (clearCap h))).ptr=2 ∧
 (clearPtr (clearBuf (clearCap h))).endPtr=h.endPtr := ⟨rfl,rfl⟩
theorem endPtr (h : Header) : reset h=⟨2,2,2,0⟩ := rfl
theorem empty_remaining (h : Header) : remaining (reset h)=(2,0) := by
 simp only [remaining,reset,clearEnd,clearPtr,clearBuf,clearCap,Nat.sub_self,Nat.zero_div]
#print axioms cap
#print axioms buf
#print axioms ptr
#print axioms endPtr
#print axioms empty_remaining
end R1Z.PV_OWNC_HeaderStores
