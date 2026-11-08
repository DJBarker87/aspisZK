import PV_LIB_SPEC_DisjointPre18
import PV_LIB_SPEC_OriginalStackGap17
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_EntryWorld18
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen

def input (w : OWNER) : OwnInit.Input := {PV_LIB_SPEC_Entry14.input with world := w}

/-- Finite static stack grant, supplied as initial process memory. Membership
is explicit data, not inferred from numeric pointer inequality or OWNER ids.
The stack covers the full native prologues and both captured run words. -/
structure StackGrant where
  regions : List (Nat × Nat)
  base : Nat
  size : Nat
  member : (base,size) ∈ regions
  nonnull : 0 < base
  nonwrapping : base+size ≤ 2^64

/-- Thread-29': arbitrary entry WORLD, one unchanged source input and v2.
Complete Pre is required at entry, with the actual registered run coordinate.
ACTIVE initialization is entry data (source0/local20 is false in this input).
No future reachability, reply, store effect or ownership export is assumed. -/
structure Entry where
  world : OWNER
  scopeEntryRsp : Nat
  stackGrant : StackGrant
  pre : OwnInit.Pre PV_LIB_SPEC_ReachedEnvironment14.parameters (input world)
  below : stackGrant.base+360 ≤ scopeEntryRsp
  above : scopeEntryRsp+0x78+16 ≤ stackGrant.base+stackGrant.size
  aligned : scopeEntryRsp % 8 = 0
  run : ∃ id h, PV_EVHB_OwnerMachine.receiver world PV_LIB_SPEC_ConcreteCaptures.places.run = some (id,h) ∧
    h.pointer = scopeEntryRsp+0x78
  active : world.world.memory PV_LIB_SPEC_Entry13.slot.physical = some 0

def frame (entry : Entry) (activation : Nat) : PV_LIB_SPEC_PhysicalStack12.Frame :=
  PV_LIB_SPEC_OriginalStackGap17.pairedFrame entry.scopeEntryRsp activation

theorem paired (entry : Entry) (activation : Nat) :
    PV_LIB_SPEC_OriginalStackGap17.NativePair entry.scopeEntryRsp (frame entry activation).runPointer :=
  PV_LIB_SPEC_OriginalStackGap17.repaired_pair _ _ (by have := entry.below; omega)

theorem stack_contains (entry : Entry) (activation : Nat) :
    entry.stackGrant.base ≤ (frame entry activation).rsp ∧
    (frame entry activation).runPointer+16 ≤ entry.stackGrant.base+entry.stackGrant.size ∧
    (frame entry activation).runPointer+16 ≤ 2^64 := by
  have lo := entry.below
  have hi := entry.above
  have nowrap := entry.stackGrant.nonwrapping
  change entry.stackGrant.base ≤ entry.scopeEntryRsp-360 ∧
    entry.scopeEntryRsp+0x78+16 ≤ entry.stackGrant.base+entry.stackGrant.size ∧
    entry.scopeEntryRsp+0x78+16 ≤ 2^64
  omega

open PV_LIB_SPEC_DisjointPre18
open PV_LIB_SPEC_DisjointCaptures18 (captures)
theorem concrete_pre_data : OwnInit.Pre PV_LIB_SPEC_ReachedEnvironment14.parameters
    (input PV_LIB_SPEC_DisjointEntry18.state) := by
  refine ⟨rfl,rfl,owner 2 (by decide),
    owner 1 (by decide),validity,
    ?_,?_,?_⟩
  · constructor
    · intro c eq
      cases eq
      exact ⟨by decide,True.intro,True.intro⟩
    · intro c member; cases member
  · intro v address reached deref
    have valid : PV_LIB_SPEC_ConcreteEntry.Value v := by
      clear deref
      induction reached with
      | argument member =>
        change _ ∈ [.number 1,PV_LIB_SPEC_DisjointCaptures18.closure] at member
        rcases List.mem_cons.mp member with rfl | member
        · exact .count
        · rcases List.mem_singleton.mp member with rfl; exact .closure
      | field n _ selected ih => exact PV_LIB_SPEC_ConcreteEntry.fields _ _ n ih selected
      | pointee _ selected read ih =>
        have eq := PV_LIB_SPEC_ConcreteEntry.dereference _ _ ih selected
        subst eq
        change some Data.null = some _ at read
        cases read
        exact .unit
    have eq := PV_LIB_SPEC_ConcreteEntry.dereference v address valid deref
    subst address
    exact ⟨.null,rfl⟩
  · exact ⟨Unit,Unit,captures,rfl,captured⟩


def concrete : Entry where
  world := PV_LIB_SPEC_DisjointEntry18.state
  scopeEntryRsp := 1016
  stackGrant := ⟨[(512,1024)],512,1024,by simp,by decide,by decide⟩
  pre := concrete_pre_data
  below := by decide
  above := by decide
  aligned := by decide
  run := ⟨0,PV_LIB_SPEC_DisjointCaptures18.runHeader,PV_LIB_SPEC_DisjointPre18.receivers.1,rfl⟩
  active := by
    simp only [PV_LIB_SPEC_DisjointEntry18.state]
    change (if 65520=65504+8 then some 1 else _) = some 0
    rw [if_neg (by decide)]
    simp only [PV_LIB_SPEC_DisjointEntry18.hooksSlot,PV_LIB_SPEC_Entry13.slot]
    rw [PV_LIB_SPEC_ArcPhysical13.write_away _ 65504 0 65520 (Or.inr (by decide))]
    rw [PV_LIB_SPEC_ArcPhysical13.write_away _ PV_LIB_SPEC_StackSize14.minimumOffset 2097153
      65520 (Or.inl (by decide))]
    rfl

theorem concrete_pre : OwnInit.Pre PV_LIB_SPEC_ReachedEnvironment14.parameters (input concrete.world) :=
  concrete.pre

theorem inhabited : Nonempty Entry := ⟨concrete⟩

#print axioms input
#print axioms StackGrant
#print axioms Entry
#print axioms frame
#print axioms paired
#print axioms stack_contains
#print axioms concrete_pre_data
#print axioms concrete
#print axioms concrete_pre
#print axioms inhabited
end PV_LIB_SPEC_EntryWorld18
