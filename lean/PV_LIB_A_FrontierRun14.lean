import PV_LIB_A_Continuation12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_FrontierRun14
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_LIB_StoreActionTable PV_THR2_SourceStoreLibrary PV_LIB_A_PrefixMachine11

/-- Lift a proved corrected-machine segment only at its exact source frontier.
This retains every other stop and phase. It is a control rule, not a source or
native adequacy hypothesis at any row boundary. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (nodes : List PV_STX2_SliceSyntax.Node) (cost : Config → OWNER → Nat)
    (finish : Config → OWNER → List PV_RJ4IDB.NativeEvent → List Config → State)
    (certificate : ∀ (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config),
      PV_THR2_IntrinsicAtContinuation.Ready nodes c →
      advance C K P resources encode H values (cost c w) ⟨⟨⟨.running c,w,es⟩,stack⟩,none⟩ =
        ⟨finish c w es stack,none⟩) (q : State) :
    advance C K P resources encode H values (PV_THR2_IntrinsicAtContinuation.steps nodes cost q) ⟨q,none⟩ =
      ⟨PV_THR2_IntrinsicAtContinuation.after nodes finish q,none⟩ := by
  classical
  rcases q with ⟨⟨status,w,es⟩,stack⟩
  cases status with
  | running c =>
    by_cases h : PV_THR2_IntrinsicAtContinuation.Ready nodes c
    · simpa only [PV_THR2_IntrinsicAtContinuation.steps,PV_THR2_IntrinsicAtContinuation.after,if_pos h]
        using certificate c w es stack h
    · simp only [PV_THR2_IntrinsicAtContinuation.steps,PV_THR2_IntrinsicAtContinuation.after,if_neg h,PV_LIB_A_PrefixMachine11.advance]
  | returned r s => rfl
  | fault f s => rfl
  | undefined site s => rfl

#print axioms run
end PV_LIB_A_FrontierRun14
