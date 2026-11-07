import PV_THR2_OwnInitAllocationCases
import PV_THR2_OwnInitAllocationOwnedAtState
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OwnInitAllocationCasesAtState
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax
open PV_EVHB_OwnerMachine PV_EVHB_RawVecOwner PV_EVHB_OwnerHeap
open PV_OWN2_Codec PV_OWN2_FreshAllocation PV_OWN2_FreshAllocationRefinement
/-- Conditional on owner acceptance of amended translator. Hypotheses: the
trace-derived retained frame and FreshAllocationValidity' at THIS actual
pre-state. All allocator answers remain; no successful reply, registration,
world reset, store evaluation or endpoint premise is supplied. -/
theorem all (pre : OWNER) (a id : Nat) (resources : Resources) (encode : Encode)
    (granted : GrantedRegions) (words : PV_OWN2_ThreadInitLayout.InitWords)
    (frame : PV_THR2_OwnUniformReceiverFrame.Frame a id
      (PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8) pre)
    (valid : FreshAllocationValidity' resources granted pre) :
    PV_THR2_OwnInitAllocationCases.Outcome ⟨a,[45]⟩ words
      (resources (.malloc 24) (world pre)).answer
      (PV_THR2_OwnInitAllocationReply.reply resources encode pre id
        (PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8) words) := by
  let h := PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8
  have header : lookup pre.world id = some h := frame.header
  have primitive := PV_OWN2_ConstructorReplies.malloc_reply_cases resources encode pre id 24 h header
  cases answer : (resources (.malloc 24) (world pre)).answer with
  | pending =>
    dsimp only [PV_THR2_OwnInitAllocationCases.Outcome,PV_THR2_OwnInitAllocationReply.reply]
    rw [primitive]
    simp only [answer,PV_THR2_OwnInitAllocationReply.finish]
  | fault f =>
    dsimp only [PV_THR2_OwnInitAllocationCases.Outcome,PV_THR2_OwnInitAllocationReply.reply]
    rw [primitive]
    simp only [answer,PV_THR2_OwnInitAllocationReply.finish]
  | returned result =>
    cases result with
    | fail e =>
      dsimp only [PV_THR2_OwnInitAllocationCases.Outcome,PV_THR2_OwnInitAllocationReply.reply]
      rw [primitive]
      simp only [answer,PV_THR2_OwnInitAllocationReply.finish]
    | div =>
      dsimp only [PV_THR2_OwnInitAllocationCases.Outcome,PV_THR2_OwnInitAllocationReply.reply]
      rw [primitive]
      simp only [answer,PV_THR2_OwnInitAllocationReply.finish]
    | ok pointer =>
      by_cases zero : pointer=0
      · dsimp only [PV_THR2_OwnInitAllocationCases.Outcome,PV_THR2_OwnInitAllocationReply.reply]
        rw [primitive]
        simp only [answer,zero,PV_THR2_OwnInitAllocationReply.finish,ite_true]
      · have bounded : pointer<18446744073709551616 :=
          PV_OWN2_FreshAllocationRefinement.pointer_lt resources granted pre valid Nat (.malloc 24) pointer 24
            ⟨rfl,answer⟩ zero (by omega)
        let p : Pointer := ⟨pointer,bounded⟩
        have own := PV_THR2_OwnInitAllocationOwnedAtState.returned pre a id resources encode granted
          p words.handle words.data words.vtable frame valid answer zero
        change (if pointer=0 then _ else _)
        rw [if_neg zero]
        exact ⟨p,rfl,own.1,own.2⟩
#print axioms all
end PV_THR2_OwnInitAllocationCasesAtState
