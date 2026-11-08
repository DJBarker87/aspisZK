import PV_LIB_SPEC_CallbackNativeGap
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_CallbackStores
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_LIB_SPEC_AllocationImages
local instance : DecidableEq Data := Classical.decEq _

/-- Native register operands at e060a, NOT a byte-image or Store transformer.
ELF fc8808eb454f3156dba550140398cc3a74af4c88ee5b3491d2d04d33ee904558.
r12 is Packet's physical ArcInner base, rcx/rax the captured slice pointer/len.
The snapshot is taken from PRE-allocation memory, preserving unknown padding.
Binding these registers to an original source execution is a separate obligation. -/
structure Registers where
  rsp : Nat
  r12 : Nat
  rcx : Nat
  rax : Nat

def image (regs : Registers) (w : OWNER) : Image :=
  callback w.world.memory regs.rsp regs.r12 regs.rcx regs.rax

/-- Fixed native instruction suffix: e0614/e0619 copy32 bytes;
e061d/e0621/e0625 store three qwords. Applied ONLY on nonnull malloc success.
All other resource answers retain the full existing provider reply. -/
def reply (resources : Resources) (encode : Encode) (s : Store Data)
    (regs : Registers) (w : OWNER) : Reply OWNER PV_RJ4IDB.NativeEvent Data :=
  let raw := PV_THR2_PacketBoxResource.reply resources encode s w
    PV_THR2_ClosureBoxAllocation.shape PV_OWN2_ClientLayout.layout.alignment
  let out := PV_THR2_ClosureBoxAllocation.reply resources encode s w
  match raw.answer with
  | .returned (.ok p) => if p=0 then out else
    {out with world := initialized p (image regs w) out.world}
  | _ => out

/-- Exact callback token, with the ACTUAL issued activation supplying backing.
No callback-source decode-success condition or resource restriction is added. -/
def handler (resources : Resources) (encode : Encode) (regs : Registers)
    (fallback : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (request : PV_STX2_Native.Request Data) (w : OWNER) : Reply OWNER PV_RJ4IDB.NativeEvent Data :=
  match request with
  | .child fn a [_] => if fn=PV_THR2_Source361BoxTable.fnClosureBoxFull then
      reply resources encode ⟨fun _ => none,a⟩ regs w
    else fallback request w
  | _ => fallback request w

theorem resource_answer (resources : Resources) (encode : Encode) (s : Store Data) (w : OWNER) :
    (PV_THR2_PacketBoxResource.reply resources encode s w
      PV_THR2_ClosureBoxAllocation.shape PV_OWN2_ClientLayout.layout.alignment).answer =
      (resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize) (world w)).answer :=
  PV_THR2_PacketBoxResource.answer resources encode s w _ _

theorem at_call (resources : Resources) (encode : Encode) (s : Store Data) (regs : Registers)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (payload : Data) (w : OWNER) :
    handler resources encode regs H
      (.child PV_THR2_Source361BoxTable.fnClosureBoxFull s.nextActivation [payload]) w =
      reply resources encode s regs w := by
  simp only [handler,ite_true,reply,PV_THR2_ClosureBoxAllocation.reply,
    PV_THR2_PacketBoxResource.reply,PV_THR2_PacketBoxReply.finish,
    PV_THR2_PacketBoxRegister.pre,PV_THR2_PacketBoxRegister.place,
    PV_THR2_PacketBoxBacking.root,PV_THR2_PacketBoxReply.value]

theorem success (resources : Resources) (encode : Encode) (s : Store Data) (regs : Registers)
    (w : OWNER) (p : Nat)
    (allocation : (resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize) (world w)).answer = .returned (.ok p))
    (nonnull : p≠0) :
    reply resources encode s regs w =
      {(PV_THR2_ClosureBoxAllocation.reply resources encode s w) with world := initialized p (image regs w) (PV_THR2_ClosureBoxAllocation.reply resources encode s w).world} := by
  dsimp only [reply]
  simp only [(resource_answer resources encode s w).trans allocation,if_neg nonnull]

/-- ALL answer constructors, events and OWNER ghost fields agree with the
named provider; only native bytes change on success. This includes null,
pending, failure, fault and divergence, rather than imposing a success premise. -/
theorem framed (resources : Resources) (encode : Encode) (s : Store Data) (regs : Registers) (w : OWNER) :
    let out := reply resources encode s regs w
    let old := PV_THR2_ClosureBoxAllocation.reply resources encode s w
    out.answer = old.answer ∧ out.events = old.events ∧
      out.world.next = old.world.next ∧ out.world.places = old.world.places ∧
      out.world.world.frame = old.world.world.frame := by
  dsimp only [reply]
  split
  · split <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  · exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem copied (resources : Resources) (encode : Encode) (s : Store Data) (regs : Registers)
    (w : OWNER) (p i : Nat)
    (allocation : (resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize) (world w)).answer = .returned (.ok p))
    (nonnull : p≠0) (bound : i<32) :
    (reply resources encode s regs w).world.world.memory (p+i) =
      w.world.memory (regs.rsp+0x38+i) := by
  rw [success resources encode s regs w p allocation nonnull]
  apply stored
  exact if_pos bound

theorem packet_word (resources : Resources) (encode : Encode) (s : Store Data) (regs : Registers)
    (w : OWNER) (p i : Nat)
    (allocation : (resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize) (world w)).answer = .returned (.ok p))
    (nonnull : p≠0) (bound : i<8) :
    (reply resources encode s regs w).world.world.memory (p+(32+i)) = some (byte regs.r12 i).val := by
  rw [success resources encode s regs w p allocation nonnull]
  apply stored
  simp only [image,callback,if_neg (by omega : ¬ 32+i<32),if_pos (by omega : 32+i<40),
    Nat.add_sub_cancel_left,word]

theorem tail (resources : Resources) (encode : Encode) (s : Store Data) (regs : Registers)
    (w : OWNER) (p address : Nat)
    (allocation : (resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize) (world w)).answer = .returned (.ok p))
    (nonnull : p≠0) (outside : address<p ∨ p+56≤address) :
    (reply resources encode s regs w).world.world.memory address =
      (PV_THR2_ClosureBoxAllocation.reply resources encode s w).world.world.memory address := by
  rw [success resources encode s regs w p allocation nonnull]
  rcases outside with before | after
  · exact if_neg (by omega)
  · apply hole
    exact callback_hole _ _ _ _ _ _ (by omega)

#print axioms Registers
#print axioms image
#print axioms reply
#print axioms handler
#print axioms resource_answer
#print axioms at_call
#print axioms success
#print axioms framed
#print axioms copied
#print axioms packet_word
#print axioms tail
end PV_LIB_SPEC_CallbackStores
