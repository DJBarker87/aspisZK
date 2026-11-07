import PV_W5_ReplyBoundary
import PV_STX2_CopyReplyInterpretation
import PV_STX2_CopySourceFrame
import PV_STX2_CountedAllocationByteFrame
import PV_STX2_SliceToVecCopy
set_option autoImplicit false
set_option pp.piBinderNames true
set_option pp.fullNames true
set_option pp.proofs false
noncomputable section
namespace PV_W5_CopyLeaf
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OWNER PV_EVHB_RawVecOwner
open PV_OWN2_FreshAllocation PV_OWN2_FreshAllocationRefinement
/-- Complete arbitrary backend reply, lifted by the existing registry-framed
lift before installing the named intrinsic semantics. No native answer can
write the ghost registry or replace source memory. -/
def reply (H : PV_W5_NativeFrame.Backend) (w : OWNER) (src dst count : Nat) :=
  PV_STX2_CopyReplyInterpretation.interpret src dst count
    (PV_STX2_Source7QUniformResourceHandler.lift H
      (.copy (.number src) (.number dst) (.number count)) w)

/-- Native copy's actual request has no fresh activation or return cell. -/
def output (s : Store Data) (parents : List Frame) (a src dst count : Nat)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) :=
  let p := PV_STX2_SliceToVecCopy.received s parents a (.number src) (.number dst)
    (.number count) (reply H w src dst count)
  {p with events := prior ++ p.events}

def Post (s : Store Data) (parents : List Frame) (a src dst count : Nat)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) : Prop :=
  let r := reply H w src dst count
  let out := output s parents a src dst count H w prior
  out.status = (PV_STX2_SliceToVecCopy.received s parents a (.number src) (.number dst) (.number count) r).status ∧
  out.world = r.world ∧ out.events = prior ++ r.events ∧
  PV_W5_LeafBoundary.statusStore out.status = s ∧
  PV_STX2_OwnerActivationWellFormed.OwnerWellFormed out.world s.nextActivation ∧
  r.answer = (H (.copy (.number src) (.number dst) (.number count)) (PV_EVHB_OwnerMachine.world w)).answer ∧
  r.events = (H (.copy (.number src) (.number dst) (.number count)) (PV_EVHB_OwnerMachine.world w)).events ∧
  ∀ value, r.answer = .returned (.ok value) →
    r.world.world.memory = fun address => if dst≤address ∧ address<dst+count*4 then
      w.world.memory (src+(address-dst)) else w.world.memory address

/-- Full model-side own-entry reply/store/registry theorem. Native refinement
credit additionally needs validity/alignment at the actual copy entry. -/
theorem full_reply (s : Store Data) (parents : List Frame) (a src dst count : Nat)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent)
    (pre : PV_STX2_OwnerActivationWellFormed.OwnerWellFormed w s.nextActivation) :
    Post s parents a src dst count H w prior := by
  have preserved := PV_STX2_CopyReplyInterpretation.reply_preserved src dst count
    (PV_STX2_Source7QUniformResourceHandler.lift H
      (.copy (.number src) (.number dst) (.number count)) w)
  have frame : (reply H w src dst count).world.places = w.places ∧
      (reply H w src dst count).world.next = w.next := by
    unfold reply PV_STX2_CopyReplyInterpretation.interpret
    simp only [PV_STX2_Source7QUniformResourceHandler.lift]
    generalize H (.copy (.number src) (.number dst) (.number count))
      (PV_EVHB_OwnerMachine.world w) = r
    rcases r with ⟨answer,post,events⟩
    cases answer with
    | pending => exact ⟨rfl,rfl⟩
    | fault f => exact ⟨rfl,rfl⟩
    | returned result => cases result <;> exact ⟨rfl,rfl⟩
  refine ⟨rfl,rfl,rfl,?_,PV_STX2_OwnerRegistryFrame.invariant pre frame.1 frame.2,
    preserved.1,preserved.2,?_⟩
  · unfold output PV_STX2_SliceToVecCopy.received
    generalize reply H w src dst count = r
    rcases r with ⟨answer,post,events⟩
    cases answer with
    | pending => rfl
    | fault f => rfl
    | returned result => cases result <;> cases parents <;> rfl
  · intro value answer
    have native : (H (.copy (.number src) (.number dst) (.number count))
      (PV_EVHB_OwnerMachine.world w)).answer = .returned (.ok value) := preserved.1.symm.trans answer
    unfold reply PV_STX2_Source7QUniformResourceHandler.lift
    dsimp only
    change (PV_STX2_CopyReplyInterpretation.interpret src dst count
      ⟨(H (.copy (.number src) (.number dst) (.number count)) (PV_EVHB_OwnerMachine.world w)).answer,
        PV_EVHB_OwnerMachine.withWorld w (H (.copy (.number src) (.number dst) (.number count)) (PV_EVHB_OwnerMachine.world w)).world,
        (H (.copy (.number src) (.number dst) (.number count)) (PV_EVHB_OwnerMachine.world w)).events⟩).world.world.memory = _
    rw [native]
    exact PV_STX2_CopyReplyInterpretation.success src dst count _ value _

/-- Separation is derived from the SAME allocator byte-frame law used by f65,
with source ownership and bounds supplied at entry, never a disjointness premise. -/
theorem allocation_separation (resources : Resources) (encode : Encode)
    (granted : GrantedRegions) (before : OWNER) (id : Nat) (h source : Header)
    (dst count : Nat) (header : lookup before.world id = some h)
    (valid : FreshAllocationValidity' resources granted before)
    (answer : (resources (.malloc (count*h.shape.width)) (PV_EVHB_OwnerMachine.world before)).answer = .returned (.ok dst))
    (nonnull : dst≠0) (positive : 0<count*h.shape.width)
    (owned : Owned before.world source) (width : h.shape.width=4)
    (sourceWidth : source.shape.width=4) (fits : count≤source.cap) :
    RangeDisjoint source.pointer (count*4) dst (count*4) := by
  have sourcePositive : 0<source.cap*source.shape.width := by
    rw [width] at positive
    rw [sourceWidth]
    omega
  have apart := PV_STX2_MallocByteFrame.separation resources encode granted before id h dst count
    header valid answer nonnull positive source owned sourcePositive
  rw [width,sourceWidth] at apart
  unfold RangeDisjoint at apart ⊢
  have bound := Nat.mul_le_mul_right 4 fits
  rcases apart with left | right
  · exact Or.inl (Nat.le_trans (Nat.add_le_add_left bound _) left)
  · exact Or.inr right
#print full_reply
#print axioms full_reply
#print axioms allocation_separation
end PV_W5_CopyLeaf
