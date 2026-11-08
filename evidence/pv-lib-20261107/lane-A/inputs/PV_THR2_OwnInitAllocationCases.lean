import PV_THR2_OwnInitAllocationOwned
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OwnInitAllocationCases
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OwnerMachine PV_EVHB_RawVecOwner PV_EVHB_OwnerHeap
open PV_OWN2_Codec PV_OWN2_FreshAllocation PV_OWN2_FreshAllocationRefinement
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
All allocator outcomes are explicit. Typed memory is required only in the
nonnull branch, and the raw return must be this actual resource pointer. -/
def Outcome (place : PV_EVHB_OwnerMachine.Place) (words : PV_OWN2_ThreadInitLayout.InitWords)
    (answer : Answer Nat) (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) : Prop :=
  match answer with
  | .returned (.ok pointer) => if pointer=0 then r.answer = .fault .abort else
      ∃ p : Pointer, p.val=pointer ∧ r.answer = .returned (.ok (PV_THR2_OwnInitPointerCodec.encode p)) ∧
        PV_OWN2_ThreadInitLayout.InitMemory r.world ⟨place,[words]⟩
  | .returned (.fail e) => r.answer = .returned (.fail e)
  | .returned .div => r.answer = .returned .div
  | .fault f => r.answer = .fault f
  | .pending => r.answer = .pending
/-- Conditional on owner acceptance of amended translator. Hypothesis:
FreshAllocationValidity' at the actual source binding's registered pre-state.
No receiver, endpoint or fixed successful reply is supplied. This is the full
local allocation interpretation, not the original-entry OwnInit closure. -/
theorem all (C : Carrier OWNER Data) (store : Store Data) (a : Nat)
    (parents : List Frame) (s : OWNER) (resources : Resources) (encode : Encode)
    (granted : GrantedRegions) (words : PV_OWN2_ThreadInitLayout.InitWords)
    (valid : FreshAllocationValidity' resources granted
      (PV_THR2_BindingRegister.register
        ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 113},parents,store⟩ s)) :
    let c := Config.mk {activation := a,remaining := PV_THR2_F361.live.body.drop 113} parents store
    let pre := PV_THR2_BindingRegister.register c s
    Outcome ⟨a,[45]⟩ words (resources (.malloc 24) (world s)).answer
      (PV_THR2_OwnInitAllocationReply.reply resources encode pre s.next
        (PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8) words) := by
  let c := Config.mk {activation := a,remaining := PV_THR2_F361.live.body.drop 113} parents store
  let pre := PV_THR2_BindingRegister.register c s
  let h := PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8
  have frame := PV_THR2_OwnUniformReceiverFrame.registered store a parents s
  have header : lookup pre.world s.next = some h := frame.2.header
  have backend : world pre = world s := frame.1
  have primitive := PV_OWN2_ConstructorReplies.malloc_reply_cases resources encode pre s.next 24 h header
  cases answer : (resources (.malloc 24) (world s)).answer with
  | pending =>
    dsimp only [Outcome,PV_THR2_OwnInitAllocationReply.reply]
    rw [primitive]
    simp only [backend,answer,PV_THR2_OwnInitAllocationReply.finish]
  | fault f =>
    dsimp only [Outcome,PV_THR2_OwnInitAllocationReply.reply]
    rw [primitive]
    simp only [backend,answer,PV_THR2_OwnInitAllocationReply.finish]
  | returned result =>
    cases result with
    | fail e =>
      dsimp only [Outcome,PV_THR2_OwnInitAllocationReply.reply]
      rw [primitive]
      simp only [backend,answer,PV_THR2_OwnInitAllocationReply.finish]
    | div =>
      dsimp only [Outcome,PV_THR2_OwnInitAllocationReply.reply]
      rw [primitive]
      simp only [backend,answer,PV_THR2_OwnInitAllocationReply.finish]
    | ok pointer =>
      by_cases zero : pointer=0
      · dsimp only [Outcome,PV_THR2_OwnInitAllocationReply.reply]
        rw [primitive]
        simp only [backend,answer,zero,PV_THR2_OwnInitAllocationReply.finish,ite_true]
      · have bounded : pointer<18446744073709551616 :=
          PV_OWN2_FreshAllocationRefinement.pointer_lt resources granted pre valid Nat (.malloc 24) pointer 24
            ⟨rfl,by rw [backend]; exact answer⟩ zero (by omega)
        let p : Pointer := ⟨pointer,bounded⟩
        have own := PV_THR2_OwnInitAllocationOwned.returned C store a parents s resources encode granted
          p words.handle words.data words.vtable valid answer zero
        change (if pointer=0 then _ else _)
        rw [if_neg zero]
        exact ⟨p,rfl,own.1,own.2⟩
#print axioms all
end PV_THR2_OwnInitAllocationCases
