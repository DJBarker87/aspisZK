import PV_LIB_A_WeakOwnerFree10
import PV_THR2_OwnUniformNeutral
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_DestructorStep10
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable

/-- Source-instruction compatibility, used internally when composing concrete
emitted destructor prefixes. These are instruction-shape checks, never row Pre
clauses or a promise that a native callback has no effects. -/
theorem ordinary (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (completed : c.frame.completed = none) (waiting : c.frame.waiting = none)
    (allocation : PV_THR2_OwnInitAction.selected c = false)
    (operator : PV_THR2_OperatorAction.selected c = none)
    (registration : PV_THR2_OwnUniformNeutral.configuration c)
    (dynamic : PV_THR2_Dynamic.active c = none)
    (interpreted : ∀ site s,
      (PV_STX2_SliceMachine.step
        (PV_LIB_A_UnwindMatch.carrier (PV_THR2_AggregateCompletion.carrier C) K) K
        (v2ProvenancePrograms P) H c w).status ≠ .undefined site s) :
    PV_LIB_A_WeakOwnerFree10.step C K P resources encode H values
      ⟨⟨⟨.running c,w,es⟩,stack⟩,none⟩ =
      let q := PV_STX2_SliceMachine.step
        (PV_LIB_A_UnwindMatch.carrier (PV_THR2_AggregateCompletion.carrier C) K) K
        (v2ProvenancePrograms P) H c w
      ⟨⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩,none⟩ := by
  have base : PV_LIB_A_WeakOwnerFree10.step C K P resources encode H values
      ⟨⟨⟨.running c,w,es⟩,stack⟩,none⟩ =
      ⟨PV_THR2_OwnInitInterpreterBridged.step
        (PV_LIB_A_UnwindMatch.carrier (PV_THR2_AggregateCompletion.carrier C) K) K
        (v2ProvenancePrograms P) resources encode H ⟨⟨.running c,w,es⟩,stack⟩,none⟩ := by
    simp [PV_LIB_A_WeakOwnerFree10.step,PV_LIB_A_WeakOwnerFree9.step,
      v2ProvenanceStep,PV_LIB_A_GenericDropMachine9.step,
      PV_LIB_A_GenericDropMachine9.select248,PV_LIB_A_GenericDropMachine9.selectCell,
      PV_LIB_A_GenericDropMachine9.selectDrop,PV_LIB_A_DeferredActions.step,
      sourceStep,sourceSelect,PV_THR2_Catch316Segment.select,completed,waiting]
  rw [base,PV_THR2_OwnInitInterpreterBridged.agreement]
  · have operators : PV_THR2_OperatorInterpreter.step
        (PV_LIB_A_UnwindMatch.carrier (PV_THR2_AggregateCompletion.carrier C) K) K
        (v2ProvenancePrograms P) H ⟨⟨.running c,w,es⟩,stack⟩ =
        PV_THR2_OwnUniformBindings.step
        (PV_LIB_A_UnwindMatch.carrier (PV_THR2_AggregateCompletion.carrier C) K) K
        (v2ProvenancePrograms P) H ⟨⟨.running c,w,es⟩,stack⟩ := by
      simp only [PV_THR2_OperatorInterpreter.step,operator]
    rw [operators,PV_THR2_OwnUniformNeutral.step]
    · simp [PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,waiting,
        PV_THR2_Execution.compatible _ _ _ _ _ _ dynamic interpreted]
    · intro d hd
      cases hd
      exact registration
  · intro d hd
    cases hd
    exact allocation

#print axioms ordinary
end PV_LIB_A_DestructorStep10
