import PV_LIB_SPEC_CallbackRecheck
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_CallbackSource
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_Frozen PV_LIB_SPEC_D984
local instance : DecidableEq Data := Classical.decEq _
abbrev Registers := PV_LIB_SPEC_CallbackStores.Registers

/-- Arc<Packet> keeps NonNull's source reference. r12 is obtained from its
REGISTERED physical allocation, never chosen to make the image agree. -/
def packetWord (C : Carrier OWNER Data) (w : OWNER) (packet : Data) : Option Nat := do
  let nonNull ← C.field packet 0
  let pointer ← C.field nonNull 0
  PV_LIB_SPEC_SparsePacketHandler.physical C w pointer

/-- Recognize the exact source13129 closure; field2 is the captured Packet.
Do not coerce a malformed closure to a fabricated pointer. -/
def packet (payload : Data) : Option Data :=
  match payload with
  | .object [("thread-aggregate-kind",kind),("thread-aggregate-slots",
      .array [.array [_],.array [_],.array [packet]])] =>
    if kind=PV_LIB_SPEC_CallbackNativeGap.kind then some packet else none
  | _ => none

/-- Source-bound r12 repair. Only nonnull success needs byte operands.
The remaining physical rsp/rcx/rax are explicit native cut data and still need
source/native pairing; no claim of their original-entry adequacy is made. -/
def registers (p : Parameters) (w : OWNER) (regs : Registers) (payload : Data) : Option Registers :=
  match packet payload with
  | none => none
  | some value => match packetWord (runtime p).carrier w value with
    | none => none
    | some base => some {regs with r12 := base}

def native (regs : Registers) (p : Parameters) (c : Config)
    (request : PV_STX2_Native.Request Data) (w : OWNER) : Option (Reply OWNER Event Data) :=
  match request with
  | .child fn _ [payload] =>
    if fn=PV_THR2_Source361BoxTable.fnClosureBoxFull then
      match (p.resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize) (world w)).answer with
      | .returned (.ok base) => if base=0 then PV_LIB_SPEC_CallbackRuntime.native regs p c request w else
        match registers p w regs payload with
        | none => none
        | some actual => PV_LIB_SPEC_CallbackRuntime.native actual p c request w
      | _ => PV_LIB_SPEC_CallbackRuntime.native regs p c request w
    else PV_LIB_SPEC_CallbackRuntime.native regs p c request w
  | _ => PV_LIB_SPEC_CallbackRuntime.native regs p c request w

theorem packet_capture (f hooks value : Data) :
    packet (PV_LIB_SPEC_CallbackNativeGap.payload f hooks value) = some value := by
  simp only [packet,PV_LIB_SPEC_CallbackNativeGap.payload,PV_THR2_KeyValues.pack,
    List.map_cons,List.map_nil,ite_true]

/-- Exact graph at nonnull successful callback allocation. A missing source
Packet backing is an explicit interpretation gap, not a success hypothesis. -/
theorem at_call (regs : Registers) (p : Parameters) (c : Config) (w : OWNER)
    (a : Nat) (f hooks value : Data) (base : Nat)
    (allocation : (p.resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize) (world w)).answer = .returned (.ok base))
    (nonnull : base≠0) :
    native regs p c (.child PV_THR2_Source361BoxTable.fnClosureBoxFull a
      [PV_LIB_SPEC_CallbackNativeGap.payload f hooks value]) w =
      (packetWord (runtime p).carrier w value).map (fun physical =>
        PV_LIB_SPEC_CallbackStores.reply p.resources p.encode
          {c.store with nextActivation := a} {regs with r12 := physical} w) := by
  simp only [native,ite_true,allocation,if_neg nonnull,registers,packet_capture]
  cases pointer : packetWord (runtime p).carrier w value with
  | none => rfl
  | some address =>
    exact PV_LIB_SPEC_CallbackRuntime.native_at_call _ _ _ _ _ _ _ _

/-- All non-success resource answers are unchanged, irrespective of missing
backings/unknown source bytes, so failure and pending paths are never filtered. -/
theorem other_answer (regs : Registers) (p : Parameters) (c : Config) (w : OWNER)
    (a : Nat) (payload : Data)
    (other : ∀ base, (p.resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize) (world w)).answer ≠ .returned (.ok base)) :
    native regs p c (.child PV_THR2_Source361BoxTable.fnClosureBoxFull a [payload]) w =
      PV_LIB_SPEC_CallbackRuntime.native regs p c
        (.child PV_THR2_Source361BoxTable.fnClosureBoxFull a [payload]) w := by
  simp only [native,ite_true]

#print axioms Registers
#print axioms packetWord
#print axioms packet
#print axioms registers
#print axioms native
#print axioms packet_capture
#print axioms at_call
#print axioms other_answer
end PV_LIB_SPEC_CallbackSource
