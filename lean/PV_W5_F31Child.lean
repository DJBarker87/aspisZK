import PV_FN_SLICE_f35
import PV_W5_F35CallContext
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace PV_W5_F31Child
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OWNER PV_EVHB_RawVecOwner
open PV_STX2_SliceMachine

abbrev entered (s : Store Data) (parents : List Frame) (a n : Nat) :=
  PV_STX2_ToVecConstructorDispatch.entered s parents a (.number n)
    PV_STX2_Source7GlobalClone.value PV_STX2_Source7LayoutConstructor.value
abbrev parent (s : Store Data) (parents : List Frame) (a n : Nat) :=
  (PV_STX2_Source7ConstructorEntry.called s parents a (.number n)
    PV_STX2_Source7GlobalClone.value PV_STX2_Source7LayoutConstructor.value).frame

def outcome (resources : Resources) (encode : Encode) (base : Carrier PV_STX_World.World Data) (K : Control)
    (s : Store Data) (parents : List Frame) (a n : Nat) (w : OWNER)
    (external : PV_W5_NoAllocShim.External) (backend : PV_W5_NativeFrame.Backend) :=
  PV_FN_SLICE_f35.outcome resources encode base K (entered s parents a n).store
    (parent s parents a n) parents s.nextActivation n false PV_STX2_Source7GlobalClone.value w [] external backend

def reply (resources : Resources) (encode : Encode) (base : Carrier PV_STX_World.World Data) (K : Control)
    (s : Store Data) (parents : List Frame) (a n : Nat) (w : OWNER)
    (external : PV_W5_NoAllocShim.External) (backend : PV_W5_NativeFrame.Backend) : Reply OWNER PV_RJ4IDB.NativeEvent Data :=
  let out := (outcome resources encode base K s parents a n w external backend).2
  ⟨PV_W5_F59Reply.answer out.status,out.world,out.events⟩

/-- Instantiate the provider's own contract at f31's exact source-issued entry.
No restated callee interface or returned-success hypothesis is introduced. -/
theorem instantiated (resources : Resources) (encode : Encode) (base : Carrier PV_STX_World.World Data) (K : Control)
    (s : Store Data) (parents : List Frame) (a n : Nat) (w : OWNER)
    (external : PV_W5_NoAllocShim.External) (backend : PV_W5_NativeFrame.Backend)
    (effects : PV_W5_LeafBoundary.Entry → OWNER → Address → Option Data)
    (wf : PV_STX2_OwnerActivationWellFormed.OwnerWellFormed w s.nextActivation)
    (usize : n<PV_STX2_Source7CapacityScalars.modulus)
    (registered : ∃ id h, (PV_STX2_Source7QUniformBindings.target parents).bind w.places=some id ∧
      lookup w.world id=some h ∧ h.shape.width=4 ∧ PV_EVHB_OwnerReserve.alignment h.shape.align=4)
    (malloc_semantics : PV_STX2_IntrinsicSemantics_Malloc resources)
    (calloc_semantics : PV_STX2_IntrinsicSemantics_AllocZeroed resources)
    (global_drop_semantics : PV_STX2_IntrinsicSemantics_GlobalDrop effects) :
    PV_FN_SLICE_f35.Post resources encode base K (entered s parents a n).store
      (parent s parents a n) parents s.nextActivation n false PV_STX2_Source7GlobalClone.value w [] external backend := by
  exact PV_FN_SLICE_f35.contract resources encode base K _ _ parents s.nextActivation n false
    PV_STX2_Source7GlobalClone.value w [] external backend effects
    (PV_W5_F35CallContext.f31_entry s parents a n w wf usize registered)
    malloc_semantics calloc_semantics global_drop_semantics

theorem registry (resources : Resources) (encode : Encode) (base : Carrier PV_STX_World.World Data) (K : Control)
    (s : Store Data) (parents : List Frame) (a n : Nat) (w : OWNER)
    (external : PV_W5_NoAllocShim.External) (backend : PV_W5_NativeFrame.Backend)
    (effects : PV_W5_LeafBoundary.Entry → OWNER → Address → Option Data)
    (wf : PV_STX2_OwnerActivationWellFormed.OwnerWellFormed w s.nextActivation)
    (usize : n<PV_STX2_Source7CapacityScalars.modulus)
    (registered : ∃ id h, (PV_STX2_Source7QUniformBindings.target parents).bind w.places=some id ∧
      lookup w.world id=some h ∧ h.shape.width=4 ∧ PV_EVHB_OwnerReserve.alignment h.shape.align=4)
    (malloc_semantics : PV_STX2_IntrinsicSemantics_Malloc resources)
    (calloc_semantics : PV_STX2_IntrinsicSemantics_AllocZeroed resources)
    (global_drop_semantics : PV_STX2_IntrinsicSemantics_GlobalDrop effects) :
    (reply resources encode base K s parents a n w external backend).world.places=w.places ∧
    (reply resources encode base K s parents a n w external backend).world.next=w.next := by
  have child := instantiated resources encode base K s parents a n w external backend effects wf usize registered
    malloc_semantics calloc_semantics global_drop_semantics
  exact ⟨child.2.2.2.1.2.1,child.2.2.2.1.2.2.1⟩

#print instantiated
#print axioms instantiated
#print axioms registry
end PV_W5_F31Child
