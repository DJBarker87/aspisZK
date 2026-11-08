import PV_LIB_A_OwnerTableCongruence14
import PV_LIB_A_SourceSelectCongruence14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_TableCongruence14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary PV_LIB_StoreActionTable
abbrev Agree := @PV_THR2_TableIntrinsic.Agree

/-- Local resolver agreement extends through SOURCE phases, OWNER allocation,
operator and registration layers. Resources, replies, worlds and events are
identical. This compares one machine step, not callee activation counters. -/
theorem source (C : Carrier OWNER Data) (K : Control)
    (P Q : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : SourceState)
    (same : Agree P Q s.base) :
    sourceStep C K P resources encode H values s = sourceStep C K Q resources encode H values s := by
  unfold sourceStep
  cases phase : s.applied with
  | some p => rfl
  | none =>
    cases status : s.base.current.status with
    | running c =>
      simp only [phase,status,PV_LIB_A_SourceSelectCongruence14.select P Q c (same c status),PV_LIB_A_OwnerTableCongruence14.owner C K P Q resources encode H s.base same]
    | returned r store => simp only [phase,status,PV_LIB_A_OwnerTableCongruence14.owner C K P Q resources encode H s.base same]
    | fault f store => simp only [phase,status,PV_LIB_A_OwnerTableCongruence14.owner C K P Q resources encode H s.base same]
    | undefined site store => simp only [phase,status,PV_LIB_A_OwnerTableCongruence14.owner C K P Q resources encode H s.base same]

theorem step (C : Carrier OWNER Data) (K : Control)
    (P Q : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : SourceState)
    (same : Agree P Q s.base) :
    PV_LIB_A_DeferredActions.step C K P resources encode H values s =
      PV_LIB_A_DeferredActions.step C K Q resources encode H values s := by
  unfold PV_LIB_A_DeferredActions.step
  cases phase : s.applied with
  | none => exact source C K P Q resources encode H values s same
  | some p =>
    rcases p with ⟨site,tail⟩
    cases tail <;> simp only [source C K P Q resources encode H values s same]

#print axioms source
#print axioms step
end PV_LIB_A_TableCongruence14
