import PV_LIB_A_WeakOwnerFree10
import PV_LIB_A_TypedBody584
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_Payload24810
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_A_TypedDestruct

def source (payload allocator : Data) : Data × List Instruction :=
  match PV_LIB_A_TypedBody584.node20 [payload,allocator] with
  | .leaf (.call _ fn _ _ cleanup) => (fn,cleanup)
  | _ => (.null,[])

/-- Actual584's248 call resolves SpawnHooks to its exact nonempty glue608,
including its emitted cleanup. This is a specialization, not arbitrary-T credit. -/
theorem hooks_resolution :
    PV_LIB_A_DropInPlace248.resolution
      (source PV_LIB_A_TypedBindingFacts.hooksType PV_LIB_A_AllocatorProvenance.globalType).1 =
      some (.call (fnPtr 608 ⟨[.atom "Erased"],[],[],[]⟩)) := rfl

/-- The selected destructor carries the SAME actual payload pointer and source
cleanup. This stage only forwards the request; effects of608 are still executed
by its source body, never replaced by a no-op or a supplied final Store. -/
theorem hooks_selected (C : Carrier OWNER Data) (c : Config) (w : OWNER)
    (reference : Data) (a : Nat) (action : PV_STX2_Native.ReturnAction)
    (completed : c.frame.completed = none)
    (waiting : c.frame.waiting = some
      ⟨.child (source PV_LIB_A_TypedBindingFacts.hooksType
          PV_LIB_A_AllocatorProvenance.globalType).1 a [reference],action,
        (source PV_LIB_A_TypedBindingFacts.hooksType
          PV_LIB_A_AllocatorProvenance.globalType).2⟩) :
    PV_LIB_A_GenericDropMachine9.select248 C c w =
      some ⟨⟨.child (source PV_LIB_A_TypedBindingFacts.hooksType
          PV_LIB_A_AllocatorProvenance.globalType).1 a [reference],action,
        (source PV_LIB_A_TypedBindingFacts.hooksType
          PV_LIB_A_AllocatorProvenance.globalType).2⟩,reference,
        .call (fnPtr 608 ⟨[.atom "Erased"],[],[],[]⟩)⟩ := by
  simp [PV_LIB_A_GenericDropMachine9.select248,completed,waiting,
    PV_LIB_A_GenericDropMachine9.resolution248,hooks_resolution]

#print axioms source
#print axioms hooks_resolution
#print axioms hooks_selected
end PV_LIB_A_Payload24810
