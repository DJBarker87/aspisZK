import PV_LIB_A_OwnerStore
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_OwnerStoreActions
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_A_OwnerStore
/-- The writer layer can act only on an issued native poll. All source
instructions, including14320 registration and14756 allocation dispatch, retain
their OWNER-aware interpretation and the SAME resource environment. -/
theorem nonwaiting (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (waiting : c.frame.waiting = none) :
    PV_LIB_A_OwnerStore.step C K P resources encode H values ⟨⟨.running c,w,es⟩,stack⟩ =
      PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H
        ⟨⟨.running c,w,es⟩,stack⟩ := by
  apply agreement
  intro d running
  cases running
  unfold PV_THR2_SourceStoreNative.select
  cases hc : c.frame.completed <;> simp only [hc,waiting] <;> rfl

/-- Completed frames cannot reissue a native writer; every completion arm is
administered by the retained OWNER-aware interpreter. -/
theorem completed (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (result : Aeneas.Std.Result Data)
    (done : c.frame.completed = some result) :
    PV_LIB_A_OwnerStore.step C K P resources encode H values ⟨⟨.running c,w,es⟩,stack⟩ =
      PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H
        ⟨⟨.running c,w,es⟩,stack⟩ := by
  apply agreement
  intro d running
  cases running
  simp only [PV_THR2_SourceStoreNative.select,done]
#print axioms nonwaiting
#print axioms completed
end PV_LIB_A_OwnerStoreActions
