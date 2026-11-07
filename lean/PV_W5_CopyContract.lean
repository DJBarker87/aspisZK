import PV_W5_CopyLeaf
import PV_W5_AllocatorContracts
import PV_STX2_Source7QUniformPointers2
set_option autoImplicit false
set_option pp.piBinderNames true
set_option pp.fullNames true
set_option pp.proofs false
noncomputable section
namespace PV_W5_CopyContract
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OWNER PV_EVHB_RawVecOwner
open PV_OWN2_FreshAllocation PV_OWN2_FreshAllocationRefinement
/-- Call arguments and the entry-owned source region. The allocation witness
names the preceding allocation entry; the caller must discharge this record
from the allocator's Post, never from an independent non-overlap assertion. -/
structure Entry where
  store : Store Data
  parents : List Frame
  activation : Nat
  sourceAddress : Address
  sourceId : Nat
  source : Header
  target : Nat
  count : Nat
  allocationEntry : OWNER
  allocationId : Nat
  allocationHeader : Header

def src (e : Entry) := PV_STX2_TypedReferences.reference e.sourceAddress .null

def request (e : Entry) : PV_STX2_Native.Request Data :=
  .copy (src e) (.number e.target) (.number e.count)

/-- Native slice validity belongs to the entry-owned source reference. Fresh
destination validity is DERIVED below from the preceding leaf answer and the
named native allocator semantics. No disjointness/alias premise occurs here. -/
structure Pre (resources : Resources) (e : Entry) (w : OWNER) : Prop where
  wellFormed : PV_STX2_OwnerActivationWellFormed.OwnerWellFormed w e.store.nextActivation
  sourceRegistered : receiver w (PV_STX2_Source7QBinding.ownerPlace e.sourceAddress) = some (e.sourceId,e.source)
  sourceOwned : Owned w.world e.source
  sourceBefore : Owned e.allocationEntry.world e.source
  sourceWidth : e.source.shape.width=4
  fits : e.count≤e.source.cap
  sourceAligned : e.source.pointer%4=0
  sourceNonnull : e.source.pointer≠0
  sourceBound : e.source.pointer+e.count*4≤2^64
  allocation : if e.count=0 then e.target%4=0 ∧ e.target≠0 ∧ e.target≤2^64
    else lookup e.allocationEntry.world e.allocationId = some e.allocationHeader ∧
      e.allocationHeader.shape.width=4 ∧
      (PV_STX2_Source7QAllocationReply.checked
        (PV_EVHB_AttemptAccounting.primitive resources (fun _ _ => []) e.allocationId
          (.malloc (e.count*4)) e.allocationEntry)).answer = .returned (.ok (.number e.target))

/-- Actual copy validity, with non-overlap and destination alignment proved
from native allocation facts, not included in Pre for the positive case. -/
theorem validity (resources : Resources) (granted : GrantedRegions) (e : Entry) (w : OWNER)
    (pre : Pre resources e w)
    (fresh : FreshAllocationValidity' resources granted e.allocationEntry)
    (malloc_semantics : PV_STX2_IntrinsicSemantics_Malloc resources) :
    RangeDisjoint e.source.pointer (e.count*4) e.target (e.count*4) ∧
    e.source.pointer%4=0 ∧ e.target%4=0 ∧ e.source.pointer≠0 ∧ e.target≠0 ∧
    e.source.pointer+e.count*4≤2^64 ∧ e.target+e.count*4≤2^64 := by
  by_cases zero : e.count=0
  · have empty := pre.allocation
    rw [if_pos zero] at empty
    refine ⟨?_,pre.sourceAligned,empty.1,pre.sourceNonnull,empty.2.1,pre.sourceBound,?_⟩
    · unfold RangeDisjoint
      rw [zero,Nat.zero_mul,Nat.add_zero,Nat.add_zero]
      omega
    · simpa only [zero,Nat.zero_mul,Nat.add_zero] using empty.2.2
  · have allocation := pre.allocation
    rw [if_neg zero] at allocation
    obtain ⟨header,width,returned⟩ := allocation
    have checked := PV_STX2_CheckedMallocReply.success
      (PV_EVHB_AttemptAccounting.primitive resources (fun _ _ => []) e.allocationId
        (.malloc (e.count*4)) e.allocationEntry) e.target returned
    have raw : (resources (.malloc (e.count*4)) (PV_EVHB_OwnerMachine.world e.allocationEntry)).answer = .returned (.ok e.target) := by
      have answer := checked.1
      rw [(PV_EVHB_AttemptAccounting.primitive_answer resources (fun _ _ => []) e.allocationId
        (.malloc (e.count*4)) e.allocationEntry).1] at answer
      simp only [PV_EVHB_OwnerHeap.primitive,header] at answer
      split at answer <;> exact answer
    have positive : 0<e.count*4 := by omega
    have rawShape : FreshSuccess (.malloc (e.count*4))
        (resources (.malloc (e.count*4)) (PV_EVHB_OwnerMachine.world e.allocationEntry)).answer
        e.target (e.count*4) := ⟨rfl,raw⟩
    obtain ⟨base,size,region,lower,upper⟩ := granted_contains resources granted e.allocationEntry
      (implies_old resources granted e.allocationEntry fresh) Nat (.malloc (e.count*4))
      e.target (e.count*4) rawShape checked.2 positive
    have bound := fresh.2 _ _ base size region
    have aligned : e.target%4=0 := by
      rcases malloc_semantics _ (e.count*4) e.target (by omega) raw with null | aligned
      · exact (checked.2 null).elim
      · exact aligned
    have apart := PV_W5_CopyLeaf.allocation_separation resources (fun _ _ => []) granted
      e.allocationEntry e.allocationId e.allocationHeader e.source e.target e.count header fresh
      (by simpa only [width] using raw) checked.2 (by simpa only [width] using positive)
      pre.sourceBefore width pre.sourceWidth pre.fits
    exact ⟨apart,pre.sourceAligned,aligned,pre.sourceNonnull,checked.2,pre.sourceBound,by omega⟩

def reply (H : PV_W5_NativeFrame.Backend) (e : Entry) (w : OWNER) :=
  PV_STX2_CopyReplyInterpretation.interpret e.source.pointer e.target e.count
    (PV_STX2_Source7QUniformResourceHandler.lift H (request e) w)

def output (H : PV_W5_NativeFrame.Backend) (e : Entry) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) :=
  let out := PV_STX2_SliceToVecCopy.received e.store e.parents e.activation
    (src e) (.number e.target) (.number e.count) (reply H e w)
  {out with events := prior ++ out.events}

def Post (H : PV_W5_NativeFrame.Backend) (e : Entry) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) : Prop :=
  let r := reply H e w
  let out := output H e w prior
  out.world = r.world ∧ out.events = prior ++ r.events ∧
  PV_W5_LeafBoundary.statusStore out.status = e.store ∧
  PV_STX2_OwnerActivationWellFormed.OwnerWellFormed out.world e.store.nextActivation ∧
  r.answer = (H (request e) (PV_EVHB_OwnerMachine.world w)).answer ∧
  r.events = (H (request e) (PV_EVHB_OwnerMachine.world w)).events ∧
  PV_STX2_Source7QUniformBindings2.pointer w (src e) = some e.source.pointer ∧
  RangeDisjoint e.source.pointer (e.count*4) e.target (e.count*4) ∧
  e.source.pointer%4=0 ∧ e.target%4=0 ∧ e.source.pointer≠0 ∧ e.target≠0 ∧
  e.source.pointer+e.count*4≤2^64 ∧ e.target+e.count*4≤2^64 ∧
  ∀ value, r.answer=.returned (.ok value) →
    r.world.world.memory = fun address => if e.target≤address ∧ address<e.target+e.count*4 then
      w.world.memory (e.source.pointer+(address-e.target)) else w.world.memory address

/-- Complete own-entry intrinsic reply, exact original typed source request,
all terminal/pending cases and explicit unchanged store. Input validity and
non-overlap are discharged before applying the documented byte update. -/
theorem contract (resources : Resources) (granted : GrantedRegions)
    (H : PV_W5_NativeFrame.Backend) (e : Entry) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (pre : Pre resources e w)
    (fresh : FreshAllocationValidity' resources granted e.allocationEntry)
    (malloc_semantics : PV_STX2_IntrinsicSemantics_Malloc resources) : Post H e w prior := by
  have safe := validity resources granted e w pre fresh malloc_semantics
  let adapted : PV_W5_NativeFrame.Backend := fun _ => H (request e)
  have model := PV_W5_CopyLeaf.full_reply e.store e.parents e.activation e.source.pointer e.target e.count
    adapted w prior pre.wellFormed
  rcases model with ⟨_,_,_,_,wf,answer,events,memory⟩
  refine ⟨rfl,rfl,?_,wf,answer,events,?_,safe.1,safe.2.1,safe.2.2.1,
    safe.2.2.2.1,safe.2.2.2.2.1,safe.2.2.2.2.2.1,safe.2.2.2.2.2.2,memory⟩
  · unfold output PV_STX2_SliceToVecCopy.received
    generalize reply H e w = r
    rcases r with ⟨answer,post,events⟩
    cases answer with
    | pending => rfl
    | fault f => rfl
    | returned result => cases result <;> cases e.parents <;> rfl
  · exact PV_STX2_Source7QUniformPointers2.captured w e.sourceAddress .null e.sourceId e.source pre.sourceRegistered
#print contract
#print axioms validity
#print axioms contract
end PV_W5_CopyContract
