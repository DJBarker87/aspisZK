import PV_W5_F35Specification
import PV_STX2_ToVecConstructorDispatch
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace PV_W5_F35CallContext
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OWNER PV_EVHB_RawVecOwner
open PV_STX2_SliceMachine

/-- Exact f31@710 source call entry. Only the incoming typed usize and the
caller's existing OWNER invariant/registered result are needed. AllocInit,
argument positions and fresh activation numbering are derived from the source
call, not supplied as caller alias or payload-equality hypotheses. -/
theorem f31_entry (s : Store Data) (parents : List Frame) (a n : Nat) (w : OWNER)
    (wf : PV_STX2_OwnerActivationWellFormed.OwnerWellFormed w s.nextActivation)
    (usize : n<PV_STX2_Source7CapacityScalars.modulus)
    (registered : ∃ id h, (PV_STX2_Source7QUniformBindings.target parents).bind w.places=some id ∧
      lookup w.world id=some h ∧ h.shape.width=4 ∧ PV_EVHB_OwnerReserve.alignment h.shape.align=4) :
    let c := PV_STX2_ToVecConstructorDispatch.entered s parents a (.number n)
      PV_STX2_Source7GlobalClone.value PV_STX2_Source7LayoutConstructor.value
    PV_FN_SLICE_f35.Pre c.store c.callers s.nextActivation n false PV_STX2_Source7GlobalClone.value w := by
  let c := PV_STX2_ToVecConstructorDispatch.entered s parents a (.number n)
    PV_STX2_Source7GlobalClone.value PV_STX2_Source7LayoutConstructor.value
  have inputs := PV_STX2_ToVecConstructorDispatch.inputs s parents a (.number n)
    PV_STX2_Source7GlobalClone.value PV_STX2_Source7LayoutConstructor.value
  have target : PV_STX2_Source7QUniformBindings.target c.callers=PV_STX2_Source7QUniformBindings.target parents := rfl
  have counter : c.store.nextActivation=s.nextActivation+1 := inputs.2.2.2.2
  refine ⟨⟨?_,inputs.2.2.2.1,inputs.1,inputs.2.1,?_⟩,?_,usize,inputs.2.2.1,rfl⟩
  · rw [counter]
    exact PV_STX2_OwnerActivationWellFormed.mono wf (Nat.le_succ _)
  · rw [target]
    exact registered
  · rw [counter]
    exact Nat.lt_succ_self _

#print f31_entry
#print axioms f31_entry
end PV_W5_F35CallContext
