import PV_LIB_SPEC_CallbackRuntime
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_CallbackRecheck
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_EVHB_RawVecOwner
open PV_LIB_SPEC_CallbackStores PV_LIB_SPEC_AllocationImages

/-- Original malloc ownership, backing and pointer facts survive the suffix.
The bytes are changed; no whole-world equality with the old reply is claimed. -/
theorem ownership (resources : Resources) (encode : Encode) (s : Store Data)
    (regs : Registers) (w : OWNER) (p : Nat)
    (allocation : (resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize) (world w)).answer = .returned (.ok p))
    (nonnull : p≠0) :
    (reply resources encode s regs w).answer = .returned (.ok (PV_THR2_PacketBoxReply.value s)) ∧
    OwnedAt (reply resources encode s regs w).world.world w.next ∧
    receiver (reply resources encode s regs w).world (PV_THR2_PacketBoxRegister.place s) =
      some (w.next,capacityStore (pointerStore
        (PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_ClosureBoxAllocation.shape
          PV_OWN2_ClientLayout.layout.alignment) p) 1) := by
  rw [success resources encode s regs w p allocation nonnull]
  have old := PV_THR2_ClosureBoxAllocation.returned resources encode s w p allocation nonnull
  exact ⟨old.1,old.2,PV_THR2_PacketBoxPointerAssociation.returned resources encode s w
    PV_THR2_ClosureBoxAllocation.shape PV_OWN2_ClientLayout.layout.alignment p allocation nonnull⟩

/-- Each scalar byte at the adopted e0621 store is initialized, including0. -/
theorem capture_pointer (resources : Resources) (encode : Encode) (s : Store Data)
    (regs : Registers) (w : OWNER) (p i : Nat)
    (allocation : (resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize) (world w)).answer = .returned (.ok p))
    (nonnull : p≠0) (bound : i<8) :
    (reply resources encode s regs w).world.world.memory (p+(40+i)) = some (byte regs.rcx i).val := by
  rw [success resources encode s regs w p allocation nonnull]
  apply stored
  simp only [image,callback,if_neg (by omega : ¬40+i<32),if_neg (by omega : ¬40+i<40),
    if_pos (by omega : 40+i<48),Nat.add_sub_cancel_left,word]

theorem capture_length (resources : Resources) (encode : Encode) (s : Store Data)
    (regs : Registers) (w : OWNER) (p i : Nat)
    (allocation : (resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize) (world w)).answer = .returned (.ok p))
    (nonnull : p≠0) (bound : i<8) :
    (reply resources encode s regs w).world.world.memory (p+(48+i)) = some (byte regs.rax i).val := by
  rw [success resources encode s regs w p allocation nonnull]
  apply stored
  simp only [image,callback,if_neg (by omega : ¬48+i<32),if_neg (by omega : ¬48+i<40),
    if_neg (by omega : ¬48+i<48),if_pos (by omega : 48+i<56),Nat.add_sub_cancel_left,word]

/-- All backend fields except memory retain the provider's exact values on
EVERY answer, including side events and allocator bookkeeping. -/
theorem backend (resources : Resources) (encode : Encode) (s : Store Data)
    (regs : Registers) (w : OWNER) :
    {(reply resources encode s regs w).world.world with
      memory := (PV_THR2_ClosureBoxAllocation.reply resources encode s w).world.world.memory} =
      (PV_THR2_ClosureBoxAllocation.reply resources encode s w).world.world := by
  dsimp only [reply]
  split
  · split <;> rfl
  · rfl

/-- A real copy of an unknown stack byte overwrites a previously KNOWN byte
with unknown. The initialized-byte serializer rejected by C7 stays rejected. -/
theorem copied_unknown (resources : Resources) (encode : Encode) (s : Store Data)
    (regs : Registers) (w : OWNER) (p : Nat)
    (allocation : (resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize) (world w)).answer = .returned (.ok p))
    (nonnull : p≠0) (unknown : w.world.memory (regs.rsp+0x38) = none) :
    (reply resources encode s regs w).world.world.memory p = none := by
  have h := copied resources encode s regs w p 0 allocation nonnull (by decide)
  simpa only [Nat.add_zero,unknown] using h

#print axioms ownership
#print axioms capture_pointer
#print axioms capture_length
#print axioms backend
#print axioms copied_unknown
end PV_LIB_SPEC_CallbackRecheck
