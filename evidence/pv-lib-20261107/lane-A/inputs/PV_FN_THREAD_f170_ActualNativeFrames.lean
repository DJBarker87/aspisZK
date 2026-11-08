import PV_THR2_LibrarySemantics_TLSFrames
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f170_ActualNativeFrames
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame PV_FN_W4_NativeFootprint
open PV_FN_W4_NativeContract PV_FN_THREAD_f170_Row

/-- The identity of the pure leaf's final Store is DERIVED from its exact
library semantics, never selected as an arbitrary native delta. -/
theorem pureStore (C : Carrier OWNER Data) (e : Entry) (w : OWNER)
    (changes : Address → Option Data)
    (library : Confined C e w changes (fun _ => False)) :
    PV_W1_ArgumentEffects.finalStore C e w changes = e.store := by
  exact congrArg (fun f => ({e.store with cells := f} : Store Data))
    (funext (fun q => library q (fun h => h)))
#print axioms pureStore

/-- Actual source arguments, exact CLOSED277 instantiation and native Store
containment. Operand failure is kept; no successful read or alias is assumed. -/
theorem f277 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (library : PV_THR2_LibrarySemantics_AsRef277 C D)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (H : Backend E) (w : OWNER) (es : List E) (stack : List Config)
    (wf : PV_W1_OwnerWellFormed.OwnerWellFormed w s.nextActivation) :
    match evaluated C s w a native277Call with
    | none => True
    | some (vs,t) =>
      let e := entry t a parents loops native277Rest native277Call vs stack
      PV_W1_ArgumentEffects.Post C e H w es (D e w) ∧
        PV_W1_ArgumentEffects.finalStore C e w (D e w) = t := by
  cases actual : evaluated C s w a native277Call with
  | none => trivial
  | some pair =>
    rcases pair with ⟨vs,t⟩
    let e := entry t a parents loops native277Rest native277Call vs stack
    have pre : PV_W1_NativeLeaves.Pre e w := by
      change PV_W1_OwnerWellFormed.OwnerWellFormed w t.nextActivation
      rw [counter C s t w a native277Call vs actual]
      exact wf
    have closed := PV_W1_NativeLeaves.f277 C e H w vs es (D e w) pre
    refine ⟨closed.1,?_⟩
    exact pureStore C e w (D e w) (library e w vs)
#print axioms f277

/-- Actual source arguments, exact CLOSED278 instantiation and native Store
containment. Operand failure is kept; no successful read or alias is assumed. -/
theorem f278 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (library : PV_THR2_LibrarySemantics_OkOr278 C D)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (H : Backend E) (w : OWNER) (es : List E) (stack : List Config)
    (wf : PV_W1_OwnerWellFormed.OwnerWellFormed w s.nextActivation) :
    match evaluated C s w a native278Call with
    | none => True
    | some (vs,t) =>
      let e := entry t a parents loops native278Rest native278Call vs stack
      PV_W1_ArgumentEffects.Post C e H w es (D e w) ∧
        PV_W1_ArgumentEffects.finalStore C e w (D e w) = t := by
  cases actual : evaluated C s w a native278Call with
  | none => trivial
  | some pair =>
    rcases pair with ⟨vs,t⟩
    let e := entry t a parents loops native278Rest native278Call vs stack
    have pre : PV_W1_NativeLeaves.Pre e w := by
      change PV_W1_OwnerWellFormed.OwnerWellFormed w t.nextActivation
      rw [counter C s t w a native278Call vs actual]
      exact wf
    have closed := PV_W1_NativeLeaves.f278 C e H w vs es (D e w) pre
    refine ⟨closed.1,?_⟩
    exact pureStore C e w (D e w) (library e w vs)
#print axioms f278

/-- Actual source arguments, exact CLOSED279 instantiation and native Store
containment. Operand failure is kept; no successful read or alias is assumed. -/
theorem f279 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (library : PV_THR2_LibrarySemantics_Branch279 C D)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (H : Backend E) (w : OWNER) (es : List E) (stack : List Config)
    (wf : PV_W1_OwnerWellFormed.OwnerWellFormed w s.nextActivation) :
    match evaluated C s w a native279Call with
    | none => True
    | some (vs,t) =>
      let e := entry t a parents loops native279Rest native279Call vs stack
      PV_W1_ArgumentEffects.Post C e H w es (D e w) ∧
        PV_W1_ArgumentEffects.finalStore C e w (D e w) = t := by
  cases actual : evaluated C s w a native279Call with
  | none => trivial
  | some pair =>
    rcases pair with ⟨vs,t⟩
    let e := entry t a parents loops native279Rest native279Call vs stack
    have pre : PV_W1_NativeLeaves.Pre e w := by
      change PV_W1_OwnerWellFormed.OwnerWellFormed w t.nextActivation
      rw [counter C s t w a native279Call vs actual]
      exact wf
    have closed := PV_W1_NativeLeaves.f279 C e H w vs es (D e w) pre
    refine ⟨closed.1,?_⟩
    exact pureStore C e w (D e w) (library e w vs)
#print axioms f279

/-- Actual source arguments, exact CLOSED280 instantiation and native Store
containment. Operand failure is kept; no successful read or alias is assumed. -/
theorem f280 {E : Type} (C : Carrier OWNER Data) (D : Effects)
    (library : PV_THR2_LibrarySemantics_FromResidual280 C D)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (H : Backend E) (w : OWNER) (es : List E) (stack : List Config)
    (wf : PV_W1_OwnerWellFormed.OwnerWellFormed w s.nextActivation) :
    match evaluated C s w a native280Call with
    | none => True
    | some (vs,t) =>
      let e := entry t a parents loops native280Rest native280Call vs stack
      PV_W1_ArgumentEffects.Post C e H w es (D e w) ∧
        PV_W1_ArgumentEffects.finalStore C e w (D e w) = t := by
  cases actual : evaluated C s w a native280Call with
  | none => trivial
  | some pair =>
    rcases pair with ⟨vs,t⟩
    let e := entry t a parents loops native280Rest native280Call vs stack
    have pre : PV_W1_NativeLeaves.Pre e w := by
      change PV_W1_OwnerWellFormed.OwnerWellFormed w t.nextActivation
      rw [counter C s t w a native280Call vs actual]
      exact wf
    have closed := PV_W1_NativeLeaves.f280 C e H w vs es (D e w) pre
    refine ⟨closed.1,?_⟩
    exact pureStore C e w (D e w) (library e w vs)
#print axioms f280
end PV_FN_THREAD_f170_ActualNativeFrames
