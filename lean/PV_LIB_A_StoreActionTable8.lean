import PV_LIB_A_StoreActionTable
import PV_LIB_A_GenericDropMachine
import PV_LIB_A_TypedProgramTable8
import PV_LIB_A_DestructionNumbering
set_option autoImplicit false
noncomputable section
namespace PV_LIB_StoreActionTable
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary

/-- Partial typed-source resolver. Option157, erased allocator reconstruction,
dynamic callbacks, collect4 and full OWNER lifetime correspondence remain open.
The unchanged v2 remains the separate importable legacy table. -/
def v2TypedPrograms := PV_LIB_A_TypedProgramTable8.programs

/-- Candidate source step, retaining the OWNER base/resources and all deferred
native answer phases. Cleanup lowering uses its named carrier extension.
No allocation byte image is defined here (D991); no source adequacy is asserted. -/
def v2TypedStep (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : SourceState) : SourceState :=
  PV_LIB_A_GenericDropMachine.step (PV_LIB_A_UnwindMatch.carrier C K) K
    (v2TypedPrograms P) resources encode H values s

/-- No typed dispatch replays a source write in an already retained native
phase. Every original answer and its world/events still use DeferredActions. -/
theorem typed_phase (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State)
    (applied : SourceSite × Tail) :
    v2TypedStep C K P resources encode H values ⟨s,some applied⟩ =
      PV_LIB_A_DeferredActions.step (PV_LIB_A_UnwindMatch.carrier C K) K
        (v2TypedPrograms P) resources encode H values ⟨s,some applied⟩ := rfl

/-- Local step agreement, over the SAME lowered-syntax carrier/resolver. This
is not a completed transport of any old caller across changed native sites. -/
theorem typed_agreement (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : SourceState)
    (away : ∀ c, s.base.current.status = .running c →
      PV_LIB_A_DropInPlace248.select c = none ∧
      PV_LIB_A_CellDestruct504.select (PV_LIB_A_UnwindMatch.carrier C K)
        (v2TypedPrograms P) c s.base.current.world = none ∧
      PV_LIB_A_GenericDropMachine.selectDrop (PV_LIB_A_UnwindMatch.carrier C K)
        (v2TypedPrograms P) c s.base.current.world = none) :
    v2TypedStep C K P resources encode H values s =
      PV_LIB_A_DeferredActions.step (PV_LIB_A_UnwindMatch.carrier C K) K
        (v2TypedPrograms P) resources encode H values s :=
  PV_LIB_A_GenericDropMachine.agreement _ _ _ _ _ _ _ _ away

#check v2
#print axioms v2TypedPrograms
#print axioms v2TypedStep
#print axioms typed_phase
#print axioms typed_agreement
end PV_LIB_StoreActionTable
