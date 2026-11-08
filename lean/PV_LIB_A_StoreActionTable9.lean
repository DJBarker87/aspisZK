import PV_LIB_A_StoreActionTable8
import PV_LIB_A_ProgramBindings9
import PV_LIB_A_GenericDropMachine9
import PV_LIB_A_ProviderAllocator9
set_option autoImplicit false
noncomputable section
namespace PV_LIB_StoreActionTable
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary

/-- Adds157 and the source218/315 constructor path plus empty Global228.
Allocator recovery reads an actual tagged allocator field; it is not a default
for erased Arc types. Legacy v2 stays unchanged and importable. -/
def v2ProvenancePrograms := PV_LIB_A_ProgramBindings9.programs

def v2ProvenanceStep (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : SourceState) : SourceState :=
  PV_LIB_A_GenericDropMachine9.step (PV_LIB_A_UnwindMatch.carrier C K) K
    (v2ProvenancePrograms P) resources encode H values s

theorem provenance_phase (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State)
    (applied : SourceSite × Tail) :
    v2ProvenanceStep C K P resources encode H values ⟨s,some applied⟩ =
      PV_LIB_A_DeferredActions.step (PV_LIB_A_UnwindMatch.carrier C K) K
        (v2ProvenancePrograms P) resources encode H values ⟨s,some applied⟩ := rfl

theorem provenance_agreement (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : SourceState)
    (away : ∀ c, s.base.current.status = .running c →
      PV_LIB_A_GenericDropMachine9.select248 (PV_LIB_A_UnwindMatch.carrier C K)
        c s.base.current.world = none ∧
      PV_LIB_A_GenericDropMachine9.selectCell (PV_LIB_A_UnwindMatch.carrier C K)
        (v2ProvenancePrograms P) c s.base.current.world = none ∧
      PV_LIB_A_GenericDropMachine9.selectDrop (PV_LIB_A_UnwindMatch.carrier C K)
        (v2ProvenancePrograms P) c s.base.current.world = none) :
    v2ProvenanceStep C K P resources encode H values s =
      PV_LIB_A_DeferredActions.step (PV_LIB_A_UnwindMatch.carrier C K) K
        (v2ProvenancePrograms P) resources encode H values s :=
  PV_LIB_A_GenericDropMachine9.agreement _ _ _ _ _ _ _ _ away

/-- The ACTUAL608 tail is now source-resolved. No claim about its payload's
callback effects or last-reference OWNER adequacy is hidden in this binding. -/
theorem hooks_tail_bound : ∃ site place fn conditional unwind program,
    PV_LIB_A_TypedBody608.node6 [] = .leaf (.drop site place fn conditional unwind) ∧
    PV_LIB_A_ProgramBindings9.selected (.object [("Regular",fn)]) = some program :=
  ⟨_,_,_,_,_,_,rfl,rfl⟩

#check v2
#print axioms v2ProvenancePrograms
#print axioms v2ProvenanceStep
#print axioms provenance_phase
#print axioms provenance_agreement
#print axioms hooks_tail_bound
end PV_LIB_StoreActionTable
