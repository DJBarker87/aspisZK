import PV_LIB_A_PurePoll
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_Residual280
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame PV_FN_W4_NativeFootprint
open PV_FN_THREAD_f170
/-- ONE exact-function named source fact under thread-16. Pinned result.rs
from_residual maps Err(e) to Err(From::from(e)); AccessError's conversion is
identity and its emitted constructor has no payload fields. No backend action.
RESIDUAL280_SEMANTICS.json pins both toolchains. This is a lower semantics
obligation, not source/native adequacy or a new endpoint/T premise. -/
def PV_THR2_LibrarySemantics_FromResidual280Values {E : Type} (H : Backend E) : Prop :=
  (∀ e w, let d := PV_W1_NativeLeaves.entry280 e e.arguments
    (PV_THR2_OwnUniformResourceHandler.lift H
      (.child d.callee d.store.nextActivation d.arguments) w).world = w) ∧
  (∀ e w ty v, let d := PV_W1_NativeLeaves.entry280 e e.arguments
    e.arguments = [(SourceTlsValue.resultErr ty).encode] →
    (PV_THR2_OwnUniformResourceHandler.lift H
      (.child d.callee d.store.nextActivation d.arguments) w).answer = .returned (.ok v) →
    ∃ outTy, v = (SourceTlsValue.resultErr outTy).encode)

def model {E : Type} (C : Carrier OWNER Data) (D : Effects) (H : Backend E)
    (e : Entry) (w : OWNER) (es : List E) :=
  PV_LIB_A_NativeLeaves.model280 C e H w e.arguments es
    (D (PV_W1_NativeLeaves.entry280 e e.arguments) w)
def law {E : Type} (C : Carrier OWNER Data) (D : Effects) (H : Backend E)
    (e : Entry) (w : OWNER) (es : List E) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model C D H e w es

theorem certified {E : Type} (C : Carrier OWNER Data) (D : Effects) (H : Backend E)
    (facts : PV_THR2_LibrarySemantics_FromResidual280Values H)
    (e : Entry) (w : OWNER) (es : List E) (pre : PV_W1_NativeLeaves.Pre e w) :
    law C D H e w es (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
      (PV_W1_NativeLeaves.entry280 e e.arguments) H w es
      (D (PV_W1_NativeLeaves.entry280 e e.arguments) w))) ∧
    PV_W1_NativeLeaves.Post280 C e H w e.arguments es
      (D (PV_W1_NativeLeaves.entry280 e e.arguments) w) ∧
    (PV_THR2_OwnUniformResourceHandler.lift H
      (.child (PV_W1_NativeLeaves.entry280 e e.arguments).callee
        e.store.nextActivation e.arguments) w).world = w :=
  ⟨rfl,PV_W1_NativeLeaves.f280 C e H w e.arguments es _ pre,facts.1 e w⟩

theorem source_local {E : Type} (C : Carrier OWNER Data) (D : Effects) (H : Backend E)
    (facts : PV_THR2_LibrarySemantics_FromResidual280Values H)
    (e : Entry) (w : OWNER) (es : List E) (ty v : Data)
    (args : e.arguments = [(SourceTlsValue.resultErr ty).encode])
    (returned : (PV_THR2_OwnUniformResourceHandler.lift H
      (.child (PV_W1_NativeLeaves.entry280 e e.arguments).callee
        e.store.nextActivation e.arguments) w).answer = .returned (.ok v)) :
    ∀ observed, (statusStore (PV_LIB_NativeGraph.internalModel C
      (PV_W1_NativeLeaves.entry280 e e.arguments) H w es
      (D (PV_W1_NativeLeaves.entry280 e e.arguments) w)).current.status).cells
      ⟨e.caller,e.destination,[]⟩ = some observed →
      ∃ outTy, observed = (SourceTlsValue.resultErr outTy).encode := by
  exact PV_LIB_A_PureCalls.delivered_value C
    (PV_W1_ArgumentEffects.afterEffects C (PV_W1_NativeLeaves.entry280 e e.arguments) w
      (D (PV_W1_NativeLeaves.entry280 e e.arguments) w)) _ es v _ returned
    (facts.2 e w ty v args returned)

def okBackend {E : Type} (ty : Data) (p : Address) : Backend E := fun _ w =>
  ⟨.returned (.ok (SourceTlsValue.resultOk ty p).encode),w,[]⟩
/-- Exact CLOSED280 alone admits the wrong source Result constructor. -/
theorem old_contract_allows_ok {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (w : OWNER) (es : List E) (ty outTy : Data) (p : Address) (changes : Address → Option Data)
    (pre : PV_W1_NativeLeaves.Pre e w) :
    PV_W1_NativeLeaves.Post280 C e (okBackend (E := E) outTy p) w
      [(SourceTlsValue.resultErr ty).encode] es changes ∧
    (PV_THR2_OwnUniformResourceHandler.lift (okBackend (E := E) outTy p)
      (.child (PV_W1_NativeLeaves.entry280 e [(SourceTlsValue.resultErr ty).encode]).callee
        e.store.nextActivation [(SourceTlsValue.resultErr ty).encode]) w).answer =
      .returned (.ok (SourceTlsValue.resultOk outTy p).encode) :=
  ⟨PV_W1_NativeLeaves.f280 C e _ w _ es changes pre,rfl⟩
theorem constructors_distinct (base : Control) (ty outTy : Data) (p : Address) :
    (SourceTlsValue.resultOk ty p).encode ≠ (SourceTlsValue.resultErr outTy).encode := by
  intro equal
  have tags := congrArg (PV_THR2_ThreadFields.control base).variant equal
  change some 0 = some 1 at tags
  cases tags
#print axioms certified
#print axioms source_local
#print axioms old_contract_allows_ok
#print axioms constructors_distinct
end PV_LIB_A_Residual280
