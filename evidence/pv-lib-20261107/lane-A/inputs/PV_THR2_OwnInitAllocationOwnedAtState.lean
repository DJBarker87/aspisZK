import PV_THR2_OwnInitAllocationOwned
import PV_OWN2_Exports
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OwnInitAllocationOwnedAtState
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax
open PV_EVHB_OwnerMachine PV_EVHB_RawVecOwner PV_EVHB_OwnerHeap
open PV_OWN2_Codec PV_OWN2_FreshAllocation PV_OWN2_FreshAllocationRefinement
/-- Conditional on owner acceptance of amended translator. Hypotheses: the
trace-derived retained frame, FreshAllocationValidity' at THIS pre-state, and
the actual nonnull successful resource case. Consume box_init_owned BY NAME
at the given world, without registering, reconstructing or resetting it.
This generalization is needed because clone214 may change the backend after
14320. It supplies no original operand association or closure premise. -/
theorem returned (pre : OWNER) (a id : Nat) (resources : Resources) (encode : Encode)
    (granted : GrantedRegions) (p handle callback vtable : Pointer)
    (frame : PV_THR2_OwnUniformReceiverFrame.Frame a id
      (PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8) pre)
    (valid : FreshAllocationValidity' resources granted pre)
    (answer : (resources (.malloc 24) (world pre)).answer = .returned (.ok p.val))
    (nonnull : p.val ≠ 0) :
    let r := PV_THR2_OwnInitAllocationReply.reply resources encode pre id
      (PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8) ⟨handle,callback,vtable⟩
    r.answer = .returned (.ok (PV_THR2_OwnInitPointerCodec.encode p)) ∧
      PV_OWN2_ThreadInitLayout.InitMemory r.world ⟨⟨a,[45]⟩,[⟨handle,callback,vtable⟩]⟩ := by
  let h := PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8
  have law := PV_OWN2_Exports.box_init_owned
    (Attr := Unit) (Data := Unit) (Native := Unit) (IoError := Unit) (OsString := Unit) (Scope := Unit)
    resources encode granted pre ⟨a,[45]⟩ id h
  have typed := law.BoxTyped p.val handle callback vtable frame.place frame.header rfl valid answer nonnull
  have exactRun := PV_OWN2_ConstructorSuccess.init_success_run resources encode pre id h p.val
    handle callback vtable frame.header answer nonnull
  dsimp only at typed
  rw [exactRun] at typed
  have counted := PV_OWN2_CountedAllocation.malloc_success resources encode pre id 24 p.val h frame.header answer nonnull
  have primitiveAnswer : (PV_EVHB_OwnerHeap.primitive resources encode id (.malloc 24) pre).answer = .returned (.ok p.val) := by
    simp only [PV_EVHB_OwnerHeap.primitive,frame.header,answer]
  dsimp only [PV_THR2_OwnInitAllocationReply.reply]
  rw [counted,PV_THR2_OwnInitAllocationReply.returned _ _ _ _ p primitiveAnswer nonnull]
  exact ⟨rfl,typed.2.1⟩
#print axioms returned
end PV_THR2_OwnInitAllocationOwnedAtState
