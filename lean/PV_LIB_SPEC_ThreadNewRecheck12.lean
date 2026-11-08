import PV_LIB_SPEC_NativeBindings12
import PV_LIB_SPEC_SuccessSchedule12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ThreadNewRecheck12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_Frozen PV_LIB_SPEC_D984
open PV_LIB_SPEC_ThreadNewNative
/-- Exact successful absent-name reply, without inventing name-length0.
All-world equality is to the named malloc primitive plus actual sparse stores.
This is a poll recheck; original-entry reachability is a separate obligation. -/
theorem success (p : Parameters) (c : Config) (req : PV_STX2_Native.Request Data)
    (w : OWNER) (id length base : Nat)
    (allocation : (p.resources (.malloc 48) (world w)).answer = .returned (.ok base))
    (nonnull : base≠0) (bounded : base < 2^64) :
    reply p c req w id length = some
      (PV_LIB_SPEC_BoundRuntime.frameReply req w
        ⟨.returned (.ok (.number base)),
          PV_LIB_SPEC_AllocationImages.initialized base
            (PV_LIB_SPEC_AllocationImages.threadInner id 0 length)
            (PV_THR2_PacketBoxResource.reply p.resources p.encode c.store w shape 8).world,
          (PV_THR2_PacketBoxResource.reply p.resources p.encode c.store w shape 8).events⟩) := by
  have raw := (PV_THR2_PacketBoxResource.answer p.resources p.encode c.store w shape 8).trans allocation
  simp only [reply,rawReply,raw,if_neg nonnull,if_neg (by omega : ¬ 2^64 ≤ base),Option.map_some]

/-- Every actual byte stored by17bedc..17bef7, including the absent-name
incoming-r14 word, has the recorded value. Tail44..47 remains allocator memory. -/
theorem sparse_stores (base id length : Nat) (w : OWNER) :
    (∀ i value, PV_LIB_SPEC_AllocationImages.threadInner id 0 length i = some value →
      (PV_LIB_SPEC_AllocationImages.initialized base
        (PV_LIB_SPEC_AllocationImages.threadInner id 0 length) w).world.memory (base+i) = value) ∧
    (∀ i, 44 ≤ i →
      (PV_LIB_SPEC_AllocationImages.initialized base
        (PV_LIB_SPEC_AllocationImages.threadInner id 0 length) w).world.memory (base+i) =
        w.world.memory (base+i)) := by
  constructor
  · intro i value stored
    exact PV_LIB_SPEC_AllocationImages.stored base i _ _ value stored
  · intro i tail
    exact PV_LIB_SPEC_AllocationImages.hole base (base+i) _ _
      (by simpa only [Nat.add_sub_cancel_left] using
        PV_LIB_SPEC_AllocationImages.thread_hole id 0 length i tail)

#print axioms success
#print axioms sparse_stores
end PV_LIB_SPEC_ThreadNewRecheck12
