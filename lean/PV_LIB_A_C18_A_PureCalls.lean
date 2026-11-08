import PV_LIB_A_NativeLeaves
import PV_THR2_LibrarySemantics_TLSSourceValuesFacts
import PV_THR2_LibrarySemantics_TLSPureWorldFacts
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_PureCalls
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame PV_FN_W4_NativeFootprint
open PV_FN_W4_NativeContract PV_FN_THREAD_f170_Row
/-- Actual source operands are evaluated before the native graph is built.
A malformed operand remains none. No actual returned value is chosen. -/

def internalModel277 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (H : Backend E) (s : Store Data) (w : OWNER) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (es : List E) (stack : List Config) :=
  (evaluated C s w a native277Call).map fun (vs,t) =>
    let e := entry t a parents loops native277Rest native277Call vs stack
    PV_LIB_NativeGraph.internalModel C e H w es (D e w)
def model277 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (H : Backend E) (s : Store Data) (w : OWNER) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (es : List E) (stack : List Config) :=
  (internalModel277 C D H s w a parents loops es stack).map PV_LIB.observe
def law277 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (H : Backend E) (s : Store Data) (w : OWNER) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (es : List E) (stack : List Config)
    (out : Option (PV_LIB.MachineObservation OWNER E)) : Prop :=
  out = model277 C D H s w a parents loops es stack

theorem certified277 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (library : PV_THR2_LibrarySemantics_AsRef277 C D)
    (H : Backend E) (s : Store Data) (w : OWNER) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (es : List E) (stack : List Config)
    (wf : PV_W1_OwnerWellFormed.OwnerWellFormed w s.nextActivation) :
    law277 C D H s w a parents loops es stack
      ((internalModel277 C D H s w a parents loops es stack).map PV_LIB.observe) ∧
    (match evaluated C s w a native277Call with
    | none => True
    | some (vs,t) =>
      let e := entry t a parents loops native277Rest native277Call vs stack
      PV_W1_ArgumentEffects.Post C e H w es (D e w) ∧
        PV_W1_ArgumentEffects.finalStore C e w (D e w) = t) :=
  ⟨rfl,PV_FN_THREAD_f170_ActualNativeFrames.f277
    C D library s a parents loops H w es stack wf⟩
#print axioms certified277

def internalModel278 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (H : Backend E) (s : Store Data) (w : OWNER) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (es : List E) (stack : List Config) :=
  (evaluated C s w a native278Call).map fun (vs,t) =>
    let e := entry t a parents loops native278Rest native278Call vs stack
    PV_LIB_NativeGraph.internalModel C e H w es (D e w)
def model278 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (H : Backend E) (s : Store Data) (w : OWNER) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (es : List E) (stack : List Config) :=
  (internalModel278 C D H s w a parents loops es stack).map PV_LIB.observe
def law278 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (H : Backend E) (s : Store Data) (w : OWNER) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (es : List E) (stack : List Config)
    (out : Option (PV_LIB.MachineObservation OWNER E)) : Prop :=
  out = model278 C D H s w a parents loops es stack

theorem certified278 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (library : PV_THR2_LibrarySemantics_OkOr278 C D)
    (H : Backend E) (s : Store Data) (w : OWNER) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (es : List E) (stack : List Config)
    (wf : PV_W1_OwnerWellFormed.OwnerWellFormed w s.nextActivation) :
    law278 C D H s w a parents loops es stack
      ((internalModel278 C D H s w a parents loops es stack).map PV_LIB.observe) ∧
    (match evaluated C s w a native278Call with
    | none => True
    | some (vs,t) =>
      let e := entry t a parents loops native278Rest native278Call vs stack
      PV_W1_ArgumentEffects.Post C e H w es (D e w) ∧
        PV_W1_ArgumentEffects.finalStore C e w (D e w) = t) :=
  ⟨rfl,PV_FN_THREAD_f170_ActualNativeFrames.f278
    C D library s a parents loops H w es stack wf⟩
#print axioms certified278

def internalModel279 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (H : Backend E) (s : Store Data) (w : OWNER) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (es : List E) (stack : List Config) :=
  (evaluated C s w a native279Call).map fun (vs,t) =>
    let e := entry t a parents loops native279Rest native279Call vs stack
    PV_LIB_NativeGraph.internalModel C e H w es (D e w)
def model279 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (H : Backend E) (s : Store Data) (w : OWNER) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (es : List E) (stack : List Config) :=
  (internalModel279 C D H s w a parents loops es stack).map PV_LIB.observe
def law279 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (H : Backend E) (s : Store Data) (w : OWNER) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (es : List E) (stack : List Config)
    (out : Option (PV_LIB.MachineObservation OWNER E)) : Prop :=
  out = model279 C D H s w a parents loops es stack

theorem certified279 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (library : PV_THR2_LibrarySemantics_Branch279 C D)
    (H : Backend E) (s : Store Data) (w : OWNER) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (es : List E) (stack : List Config)
    (wf : PV_W1_OwnerWellFormed.OwnerWellFormed w s.nextActivation) :
    law279 C D H s w a parents loops es stack
      ((internalModel279 C D H s w a parents loops es stack).map PV_LIB.observe) ∧
    (match evaluated C s w a native279Call with
    | none => True
    | some (vs,t) =>
      let e := entry t a parents loops native279Rest native279Call vs stack
      PV_W1_ArgumentEffects.Post C e H w es (D e w) ∧
        PV_W1_ArgumentEffects.finalStore C e w (D e w) = t) :=
  ⟨rfl,PV_FN_THREAD_f170_ActualNativeFrames.f279
    C D library s a parents loops H w es stack wf⟩
#print axioms certified279

def internalModel280 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (H : Backend E) (s : Store Data) (w : OWNER) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (es : List E) (stack : List Config) :=
  (evaluated C s w a native280Call).map fun (vs,t) =>
    let e := entry t a parents loops native280Rest native280Call vs stack
    PV_LIB_NativeGraph.internalModel C e H w es (D e w)
def model280 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (H : Backend E) (s : Store Data) (w : OWNER) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (es : List E) (stack : List Config) :=
  (internalModel280 C D H s w a parents loops es stack).map PV_LIB.observe
def law280 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (H : Backend E) (s : Store Data) (w : OWNER) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (es : List E) (stack : List Config)
    (out : Option (PV_LIB.MachineObservation OWNER E)) : Prop :=
  out = model280 C D H s w a parents loops es stack

theorem certified280 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (library : PV_THR2_LibrarySemantics_FromResidual280 C D)
    (H : Backend E) (s : Store Data) (w : OWNER) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (es : List E) (stack : List Config)
    (wf : PV_W1_OwnerWellFormed.OwnerWellFormed w s.nextActivation) :
    law280 C D H s w a parents loops es stack
      ((internalModel280 C D H s w a parents loops es stack).map PV_LIB.observe) ∧
    (match evaluated C s w a native280Call with
    | none => True
    | some (vs,t) =>
      let e := entry t a parents loops native280Rest native280Call vs stack
      PV_W1_ArgumentEffects.Post C e H w es (D e w) ∧
        PV_W1_ArgumentEffects.finalStore C e w (D e w) = t) :=
  ⟨rfl,PV_FN_THREAD_f170_ActualNativeFrames.f280
    C D library s a parents loops H w es stack wf⟩
#print axioms certified280

/-- All-answer world facets are used literally; no pending-world frame
hypothesis is added. These concern backend replies at the actual entry. -/
theorem worlds {E : Type} (H : Backend E)
    (facts : PV_FN_THREAD_f170.DocumentedValueFacts H) (e : Entry) (w : OWNER) :
    (PV_THR2_OwnUniformResourceHandler.lift H
      (.child (PV_W1_NativeLeaves.entry277 e e.arguments).callee e.store.nextActivation e.arguments) w).world = w ∧
    (PV_THR2_OwnUniformResourceHandler.lift H
      (.child (PV_W1_NativeLeaves.entry278 e e.arguments).callee e.store.nextActivation e.arguments) w).world = w ∧
    (PV_THR2_OwnUniformResourceHandler.lift H
      (.child (PV_W1_NativeLeaves.entry279 e e.arguments).callee e.store.nextActivation e.arguments) w).world = w :=
  ⟨facts.asRef277World e w,facts.okOr278World e w,facts.branch279World e w⟩
#print axioms worlds

/-- Connect any exact provider value property to the actual delivered local.
This is return administration, and says nothing about the resumed caller. -/
theorem delivered_value {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (r : Reply OWNER E Data) (es : List E) (v : Data) (Q : Data → Prop)
    (returned : r.answer = .returned (.ok v)) (value : Q v) :
    ∀ observed, (statusStore (deliver C e r es).current.status).cells
      ⟨e.caller,e.destination,[]⟩ = some observed → Q observed := by
  intro observed selected
  have full := PV_W1_LeafBoundary.full_reply C e r es
  have destination : (statusStore (deliver C e r es).current.status).cells
      ⟨e.caller,e.destination,[]⟩ = some v := by
    rw [full.1]
    simp only [expectedStatus,returned,statusStore,PV_THR2_StaticReply.returnedStore,write_same]
  have same := Option.some.inj (destination.symm.trans selected)
  exact same ▸ value
#print axioms delivered_value

/-- Source constructor evidence is attached to the actual returned local;
malformed operands and nonreturned answers remain in model277. -/
theorem asRef_source_local {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (H : Backend E) (source : PV_THR2_LibrarySemantics_AsRef277Source C H)
    (e : Entry) (w : OWNER) (es : List E) (v : Data)
    (returned : (PV_THR2_OwnUniformResourceHandler.lift H
      (.child (PV_W1_NativeLeaves.entry277 e e.arguments).callee
        e.store.nextActivation e.arguments) w).answer = .returned (.ok v)) :
    ∀ observed, (statusStore (PV_LIB_NativeGraph.internalModel C
      (PV_W1_NativeLeaves.entry277 e e.arguments) H w es
      (D (PV_W1_NativeLeaves.entry277 e e.arguments) w)).current.status).cells
      ⟨e.caller,e.destination,[]⟩ = some observed →
      (∃ ty, observed = (PV_FN_THREAD_f170.SourceTlsValue.optionNone ty).encode) ∨
      ∃ ty p original, e.arguments.head? = some original ∧
        C.dereference w original = some p ∧
        observed = (PV_FN_THREAD_f170.SourceTlsValue.optionSome ty p).encode := by
  exact delivered_value C
    (PV_W1_ArgumentEffects.afterEffects C (PV_W1_NativeLeaves.entry277 e e.arguments) w
      (D (PV_W1_NativeLeaves.entry277 e e.arguments) w)) _ es v _ returned
    (source e w v returned)
#print axioms asRef_source_local
end PV_LIB_A_PureCalls
