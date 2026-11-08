import PV_LIB_A_PureCalls
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_PureValues
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame PV_FN_W4_NativeFootprint
open PV_FN_THREAD_f170

/-- Existing exact source constructors transported into the delivered local.
The source fact is reused literally. No success-only graph is installed. -/
theorem source_local278 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (H : Backend E) (source : PV_THR2_LibrarySemantics_OkOr278Source H)
    (e : Entry) (w : OWNER) (es : List E) (v : Data)
    (returned : (PV_THR2_OwnUniformResourceHandler.lift H
      (.child (PV_W1_NativeLeaves.entry278 e e.arguments).callee
        e.store.nextActivation e.arguments) w).answer = .returned (.ok v)) :
    ∀ observed, (statusStore (PV_LIB_NativeGraph.internalModel C
      (PV_W1_NativeLeaves.entry278 e e.arguments) H w es
      (D (PV_W1_NativeLeaves.entry278 e e.arguments) w)).current.status).cells
      ⟨e.caller,e.destination,[]⟩ = some observed →
    (∀ ty, e.arguments.head? = some (SourceTlsValue.optionNone ty).encode →
      ∃ outTy, observed = (SourceTlsValue.resultErr outTy).encode) ∧
    (∀ ty p, e.arguments.head? = some (SourceTlsValue.optionSome ty p).encode →
      ∃ outTy, observed = (SourceTlsValue.resultOk outTy p).encode) := by
  exact PV_LIB_A_PureCalls.delivered_value C
    (PV_W1_ArgumentEffects.afterEffects C (PV_W1_NativeLeaves.entry278 e e.arguments) w
      (D (PV_W1_NativeLeaves.entry278 e e.arguments) w)) _ es v _ returned
    (source e w v returned)
#print axioms source_local278

/-- Existing exact source constructors transported into the delivered local.
The source fact is reused literally. No success-only graph is installed. -/
theorem source_local279 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (H : Backend E) (source : PV_THR2_LibrarySemantics_Branch279Source H)
    (e : Entry) (w : OWNER) (es : List E) (v : Data)
    (returned : (PV_THR2_OwnUniformResourceHandler.lift H
      (.child (PV_W1_NativeLeaves.entry279 e e.arguments).callee
        e.store.nextActivation e.arguments) w).answer = .returned (.ok v)) :
    ∀ observed, (statusStore (PV_LIB_NativeGraph.internalModel C
      (PV_W1_NativeLeaves.entry279 e e.arguments) H w es
      (D (PV_W1_NativeLeaves.entry279 e e.arguments) w)).current.status).cells
      ⟨e.caller,e.destination,[]⟩ = some observed →
    (∀ ty, e.arguments.head? = some (SourceTlsValue.resultErr ty).encode →
      ∃ outTy residualTy, observed = (SourceTlsValue.controlBreak outTy residualTy).encode) ∧
    (∀ ty p, e.arguments.head? = some (SourceTlsValue.resultOk ty p).encode →
      ∃ outTy, observed = (SourceTlsValue.controlContinue outTy p).encode) := by
  exact PV_LIB_A_PureCalls.delivered_value C
    (PV_W1_ArgumentEffects.afterEffects C (PV_W1_NativeLeaves.entry279 e e.arguments) w
      (D (PV_W1_NativeLeaves.entry279 e e.arguments) w)) _ es v _ returned
    (source e w v returned)
#print axioms source_local279
end PV_LIB_A_PureValues
