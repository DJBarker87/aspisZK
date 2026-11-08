import PV_LIB_SPEC_NativeConstructors
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ThreadNewNative
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_Frozen PV_LIB_SPEC_D984
/-- Adopted ELF fc8808eb: e045e copies r9(scope) into r14. For absent name,
17be53 jumps to17be67 without assigning r14;17beef STILL writes that word.
Therefore the absent-name length word is the original scope pointer, not0.
The exact source context is f361's still-live argument local4 at12290. -/
def operands (p : Parameters) (c : Config) (w : OWNER) (args : List Data) : Option (Nat × Nat) := do
  let [id,label] := args | none
  let .number threadId ← pure id | none
  if threadId=0 ∨ 2^64 ≤ threadId then none else do
    if (runtime p).control.variant label ≠ some 0 then none else do
      let scope ← c.store.cells ⟨c.frame.activation,4,[]⟩
      let scopePointer ← PV_LIB_SPEC_SparsePacketHandler.scopeWord
        (runtime p).carrier (runtime p).control w scope
      pure (threadId,scopePointer)

def shape : R1Z.PV_FXM_ReserveWorld.Shape := ⟨48,._Align1Shl3⟩
/-- Reuse the named malloc primitive, backend effects, null branch and attempt
accounting. The temporary native allocation descriptor is not exported into
source OWNER ghost state. Byte stores are ONLY17bedc..17bef7 (tail44..47 holes).
This models the absent-name branch only; it does not erase Some(String). -/
def rawReply (p : Parameters) (c : Config) (request : PV_STX2_Native.Request Data)
    (w : OWNER) (id absentLength : Nat) : Option (Reply OWNER Event Data) :=
  let raw := PV_THR2_PacketBoxResource.reply p.resources p.encode c.store w shape 8
  match raw.answer with
    | .returned (.ok base) =>
      if base=0 then some ⟨.fault .abort,raw.world,
        raw.events ++ [PV_STX_World.side "client-allocator-abort" []]⟩
      else if 2^64 ≤ base then none else
        some ⟨.returned (.ok (.number base)),
          PV_LIB_SPEC_AllocationImages.initialized base
            (PV_LIB_SPEC_AllocationImages.threadInner id 0 absentLength) raw.world,raw.events⟩
    | .returned (.fail error) => some ⟨.returned (.fail error),raw.world,raw.events⟩
    | .returned .div => some ⟨.returned .div,raw.world,raw.events⟩
    | .fault error => some ⟨.fault error,raw.world,raw.events⟩
    | .pending => some ⟨.pending,raw.world,raw.events⟩

def reply (p : Parameters) (c : Config) (request : PV_STX2_Native.Request Data)
    (w : OWNER) (id absentLength : Nat) : Option (Reply OWNER Event Data) :=
  (rawReply p c request w id absentLength).map (PV_LIB_SPEC_BoundRuntime.frameReply request w)

/-- This is an ordinary opaque-native heap allocation, not permission to
change source places or source allocation identities. -/
theorem ghost_frame (p : Parameters) (c : Config) (request : PV_STX2_Native.Request Data)
    (w : OWNER) (id length : Nat) (out : Reply OWNER Event Data)
    (ordinary : PV_LIB_SPEC_BoundRuntime.allocationToken request = false)
    (result : reply p c request w id length = some out) :
    PV_LIB_SPEC_NativeRuntime.GhostFrame w out.world := by
  unfold reply at result
  cases h : rawReply p c request w id length with
  | none => rw [h] at result; cases result
  | some raw =>
    rw [h] at result
    cases result
    exact PV_LIB_SPEC_BoundRuntime.ordinary_framed request w raw ordinary

#print axioms operands
#print axioms shape
#print axioms rawReply
#print axioms reply
#print axioms ghost_frame
end PV_LIB_SPEC_ThreadNewNative
