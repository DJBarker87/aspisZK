import PV_LIB_SPEC_CallbackSource
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_CallbackOperands
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_Frozen
abbrev Registers := PV_LIB_SPEC_CallbackStores.Registers

/-- Native-workers F is source3472's move closure: fields(&run,k), NOT a
slice(pointer,length). Source13123 wraps it in MaybeDangling; source13129
captures that wrapper, ChildSpawnHooks and Arc<Packet>. Type67 is16/8;
ChildSpawnHooks type130 is32/8; callback type132 is56/8 in adopted fc8808eb.
SESSION11_ABI_SOURCE.json records the source hash and correspondence. -/
def captureWords (C : Carrier OWNER Data) (w : OWNER) (f : Data) : Option (Nat × Nat) := do
  let closure ← C.field f 0
  let runReference ← C.field closure 0
  let .number k ← C.field closure 1 | none
  let runPointer ← PV_LIB_SPEC_SparsePacketHandler.physical C w runReference
  pure (runPointer,k)

/-- Three scalar native operands are now partial source projections. Only the
physical stack pointer remains explicit. Unknown copied stack bytes remain
actual pre-memory bytes; no initialized padding is fabricated. -/
def fromSource (p : Parameters) (w : OWNER) (rsp : Nat) (f packet : Data) : Option Registers := do
  let packetPointer ← PV_LIB_SPEC_CallbackSource.packetWord (runtime p).carrier w packet
  let (runPointer,k) ← captureWords (runtime p).carrier w f
  pure ⟨rsp,packetPointer,runPointer,k⟩

/-- For the ACTUAL source3472 aggregate and its MaybeDangling wrapper, the
capture graph is precisely source-reference resolution followed by k. A
physical stack/source-place correspondence must supply that resolution. -/
theorem capture_graph (p : Parameters) (w : OWNER) (wrapperKind : Data)
    (runReference : Data) (k : Nat) :
    captureWords (runtime p).carrier w
      (PV_THR2_KeyValues.pack wrapperKind
        [PV_THR2_KeyValues.pack
          (match PV_THR2_F15.node34 with | .leaf (.aggregateMove _ _ kind _) => kind | _ => .null)
          [runReference,.number k]]) =
      (PV_LIB_SPEC_SparsePacketHandler.physical (runtime p).carrier w runReference).map
        (fun pointer => (pointer,k)) := by
  change (do
    let pointer ← PV_LIB_SPEC_SparsePacketHandler.physical (runtime p).carrier w runReference
    pure (pointer,k)) = _
  cases PV_LIB_SPEC_SparsePacketHandler.physical (runtime p).carrier w runReference <;> rfl

/-- A missing PHYSICAL run reference cannot be repaired by choosing native
scalar operands. This is a local binding obstruction, not full-joint negation. -/
theorem missing_run (p : Parameters) (w : OWNER) (wrapperKind : Data)
    (runReference : Data) (k : Nat)
    (missing : PV_LIB_SPEC_SparsePacketHandler.physical (runtime p).carrier w runReference = none) :
    captureWords (runtime p).carrier w
      (PV_THR2_KeyValues.pack wrapperKind
        [PV_THR2_KeyValues.pack
          (match PV_THR2_F15.node34 with | .leaf (.aggregateMove _ _ kind _) => kind | _ => .null)
          [runReference,.number k]]) = none := by
  rw [capture_graph,missing]
  rfl

#print axioms Registers
#print axioms captureWords
#print axioms fromSource
#print axioms capture_graph
#print axioms missing_run
end PV_LIB_SPEC_CallbackOperands
