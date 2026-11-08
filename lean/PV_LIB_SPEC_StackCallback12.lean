import PV_LIB_SPEC_PhysicalStack12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_StackCallback12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_Frozen PV_LIB_SPEC_D984
local instance : DecidableEq Data := Classical.decEq _

/-- Exact closure tag/capture selection; all three scalar registers are
computed from source values and registered physical references. -/
def operands (native : PV_LIB_SPEC_PhysicalStack12.Frame) (p : Parameters) (c : Config) (w : OWNER) (payload : Data) :
    Option PV_LIB_SPEC_CallbackStores.Registers :=
  match payload with
  | .object [("thread-aggregate-kind",kind),("thread-aggregate-slots",
      .array [.array [f],.array [_],.array [packet]])] =>
    if kind=PV_LIB_SPEC_CallbackNativeGap.kind then
      PV_LIB_SPEC_PhysicalStack12.registers native p c w f packet else none
  | _ => none

/-- Install the binary suffix with source-derived r12/rcx/rax. The finite frame and the
PRE-memory remain explicit native-cut state: source/physical stack pairing
must be established, and is not inferred from a successful resource reply.
No desired-write/image/Store transformer is an input. -/
def native (nativeFrame : PV_LIB_SPEC_PhysicalStack12.Frame) (p : Parameters) (c : Config)
    (request : PV_STX2_Native.Request Data) (w : OWNER) : Option (Reply OWNER Event Data) :=
  let fallback := PV_LIB_SPEC_CallbackRuntime.native ⟨nativeFrame.rsp,0,0,0⟩ p c request w
  match request with
  | .child fn _ [payload] =>
    if fn=PV_THR2_Source361BoxTable.fnClosureBoxFull then
      match (p.resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize) (world w)).answer with
      | .returned (.ok base) => if base=0 then fallback else
        match operands nativeFrame p c w payload with
        | none => none
        | some regs => PV_LIB_SPEC_CallbackRuntime.native regs p c request w
      | _ => fallback
    else fallback
  | _ => fallback

theorem operands_graph (nativeFrame : PV_LIB_SPEC_PhysicalStack12.Frame) (p : Parameters) (c : Config) (w : OWNER) (f hooks packet : Data) :
    operands nativeFrame p c w (PV_LIB_SPEC_CallbackNativeGap.payload f hooks packet) =
      PV_LIB_SPEC_PhysicalStack12.registers nativeFrame p c w f packet := by
  simp only [operands,PV_LIB_SPEC_CallbackNativeGap.payload,PV_THR2_KeyValues.pack,
    List.map_cons,List.map_nil,ite_true]

theorem at_call (nativeFrame : PV_LIB_SPEC_PhysicalStack12.Frame) (p : Parameters) (c : Config) (w : OWNER)
    (a : Nat) (f hooks packet : Data) (base : Nat)
    (allocation : (p.resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize) (world w)).answer = .returned (.ok base))
    (nonnull : base≠0) :
    native nativeFrame p c (.child PV_THR2_Source361BoxTable.fnClosureBoxFull a
      [PV_LIB_SPEC_CallbackNativeGap.payload f hooks packet]) w =
      (PV_LIB_SPEC_PhysicalStack12.registers nativeFrame p c w f packet).map (fun regs =>
        PV_LIB_SPEC_CallbackStores.reply p.resources p.encode
          {c.store with nextActivation := a} regs w) := by
  simp only [native,ite_true,allocation,if_neg nonnull,operands_graph]
  cases PV_LIB_SPEC_PhysicalStack12.registers nativeFrame p c w f packet with
  | none => rfl
  | some regs => exact PV_LIB_SPEC_CallbackRuntime.native_at_call _ _ _ _ _ _ _ _

/-- Explicit missing operand handling; allocating a56-byte box does not prove
that its source/native correspondence exists. No success-decode premise is
inserted into a row, contract, MachineSpec or endpoint. -/
theorem missing_operands (nativeFrame : PV_LIB_SPEC_PhysicalStack12.Frame) (p : Parameters) (c : Config) (w : OWNER)
    (a : Nat) (f hooks packet : Data) (base : Nat)
    (allocation : (p.resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize) (world w)).answer = .returned (.ok base))
    (nonnull : base≠0)
    (missing : PV_LIB_SPEC_PhysicalStack12.registers nativeFrame p c w f packet = none) :
    native nativeFrame p c (.child PV_THR2_Source361BoxTable.fnClosureBoxFull a
      [PV_LIB_SPEC_CallbackNativeGap.payload f hooks packet]) w = none := by
  rw [at_call nativeFrame p c w a f hooks packet base allocation nonnull,missing]
  rfl

/-- Same all-answer ghost frame after the new source-bound native projection. -/
def answer (nativeFrame : PV_LIB_SPEC_PhysicalStack12.Frame) (p : Parameters) (c : Config)
    (request : PV_STX2_Native.Request Data) (w : OWNER) : Option (Reply OWNER Event Data) :=
  (native nativeFrame p c request w).map (PV_LIB_SPEC_BoundRuntime.frameReply request w)

theorem ordinary_framed (nativeFrame : PV_LIB_SPEC_PhysicalStack12.Frame) (p : Parameters) (c : Config)
    (request : PV_STX2_Native.Request Data) (w : OWNER) (r : Reply OWNER Event Data)
    (ordinary : PV_LIB_SPEC_BoundRuntime.allocationToken request = false)
    (result : answer nativeFrame p c request w = some r) :
    PV_LIB_SPEC_NativeRuntime.GhostFrame w r.world := by
  unfold answer at result
  cases hv : native nativeFrame p c request w with
  | none => rw [hv] at result; cases result
  | some original =>
    rw [hv] at result
    cases result
    exact PV_LIB_SPEC_BoundRuntime.ordinary_framed request w original ordinary

#print axioms operands
#print axioms native
#print axioms operands_graph
#print axioms at_call
#print axioms missing_operands
#print axioms answer
#print axioms ordinary_framed
end PV_LIB_SPEC_StackCallback12
