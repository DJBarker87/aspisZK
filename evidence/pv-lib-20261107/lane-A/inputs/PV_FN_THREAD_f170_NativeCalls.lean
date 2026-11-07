import PV_THR2_FnOnceDispatch
import PV_FN_THREAD_f170_Entry
import PV_FN_THREAD_f207_Prefix
import PV_FN_THREAD_f170_Row
import PV_FN_W4_NativeContract
import PV_W1_NativeLeaves
import PV_W1_TLSLeaves
import PV_W1_DropLeaf
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f170_NativeCalls
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame
open PV_FN_W4_NativeContract PV_FN_THREAD_f170_Row

/-- CLOSED f277 at its actual source-selected argument values. The native
entry Pre follows from operand-counter preservation and the caller invariant.
All argument-reachable Store changes remain explicit. -/
theorem f277 {E : Type} (C : Carrier OWNER Data) (s : Store Data) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (H : Backend E) (w : OWNER)
    (es : List E) (stack : List Config) (changes : Address → Option Data)
    (wf : PV_W1_OwnerWellFormed.OwnerWellFormed w s.nextActivation) :
    match evaluated C s w a native277Call with
    | none => True
    | some (vs,t) => PV_W1_ArgumentEffects.Post C
        (entry t a parents loops native277Rest native277Call vs stack) H w es changes := by
  cases actual : evaluated C s w a native277Call with
  | none => trivial
  | some pair =>
    rcases pair with ⟨vs,t⟩
    have pre : PV_W1_NativeLeaves.Pre
        (entry t a parents loops native277Rest native277Call vs stack) w := by
      change PV_W1_OwnerWellFormed.OwnerWellFormed w t.nextActivation
      rw [counter C s t w a native277Call vs actual]
      exact wf
    exact (PV_W1_NativeLeaves.f277 C
      (entry t a parents loops native277Rest native277Call vs stack) H w vs es changes pre).1
#print axioms f277

/-- CLOSED f278 at its actual source-selected argument values. The native
entry Pre follows from operand-counter preservation and the caller invariant.
All argument-reachable Store changes remain explicit. -/
theorem f278 {E : Type} (C : Carrier OWNER Data) (s : Store Data) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (H : Backend E) (w : OWNER)
    (es : List E) (stack : List Config) (changes : Address → Option Data)
    (wf : PV_W1_OwnerWellFormed.OwnerWellFormed w s.nextActivation) :
    match evaluated C s w a native278Call with
    | none => True
    | some (vs,t) => PV_W1_ArgumentEffects.Post C
        (entry t a parents loops native278Rest native278Call vs stack) H w es changes := by
  cases actual : evaluated C s w a native278Call with
  | none => trivial
  | some pair =>
    rcases pair with ⟨vs,t⟩
    have pre : PV_W1_NativeLeaves.Pre
        (entry t a parents loops native278Rest native278Call vs stack) w := by
      change PV_W1_OwnerWellFormed.OwnerWellFormed w t.nextActivation
      rw [counter C s t w a native278Call vs actual]
      exact wf
    exact (PV_W1_NativeLeaves.f278 C
      (entry t a parents loops native278Rest native278Call vs stack) H w vs es changes pre).1
#print axioms f278

/-- CLOSED f279 at its actual source-selected argument values. The native
entry Pre follows from operand-counter preservation and the caller invariant.
All argument-reachable Store changes remain explicit. -/
theorem f279 {E : Type} (C : Carrier OWNER Data) (s : Store Data) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (H : Backend E) (w : OWNER)
    (es : List E) (stack : List Config) (changes : Address → Option Data)
    (wf : PV_W1_OwnerWellFormed.OwnerWellFormed w s.nextActivation) :
    match evaluated C s w a native279Call with
    | none => True
    | some (vs,t) => PV_W1_ArgumentEffects.Post C
        (entry t a parents loops native279Rest native279Call vs stack) H w es changes := by
  cases actual : evaluated C s w a native279Call with
  | none => trivial
  | some pair =>
    rcases pair with ⟨vs,t⟩
    have pre : PV_W1_NativeLeaves.Pre
        (entry t a parents loops native279Rest native279Call vs stack) w := by
      change PV_W1_OwnerWellFormed.OwnerWellFormed w t.nextActivation
      rw [counter C s t w a native279Call vs actual]
      exact wf
    exact (PV_W1_NativeLeaves.f279 C
      (entry t a parents loops native279Rest native279Call vs stack) H w vs es changes pre).1
#print axioms f279

/-- CLOSED f280 at its actual source-selected argument values. The native
entry Pre follows from operand-counter preservation and the caller invariant.
All argument-reachable Store changes remain explicit. -/
theorem f280 {E : Type} (C : Carrier OWNER Data) (s : Store Data) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (H : Backend E) (w : OWNER)
    (es : List E) (stack : List Config) (changes : Address → Option Data)
    (wf : PV_W1_OwnerWellFormed.OwnerWellFormed w s.nextActivation) :
    match evaluated C s w a native280Call with
    | none => True
    | some (vs,t) => PV_W1_ArgumentEffects.Post C
        (entry t a parents loops native280Rest native280Call vs stack) H w es changes := by
  cases actual : evaluated C s w a native280Call with
  | none => trivial
  | some pair =>
    rcases pair with ⟨vs,t⟩
    have pre : PV_W1_NativeLeaves.Pre
        (entry t a parents loops native280Rest native280Call vs stack) w := by
      change PV_W1_OwnerWellFormed.OwnerWellFormed w t.nextActivation
      rw [counter C s t w a native280Call vs actual]
      exact wf
    exact (PV_W1_NativeLeaves.f280 C
      (entry t a parents loops native280Rest native280Call vs stack) H w vs es changes pre).1
#print axioms f280

/-- The initializer's exact argument is the source-created None. The source
prologue preserves nextActivation, so the native Pre is the entry invariant. -/
def initializerEntry (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (stack : List Config) : Entry :=
  ⟨PV_FN_THREAD_f170.beforeDynamic s a b,a,parents,[],PV_THR2_F170.live.body.drop 14,
    (PV_THR2_KeyValues.castToken b).2,[PV_FN_THREAD_f170.arg],7,stack⟩

theorem initializer {E : Type} (C : Carrier OWNER Data) (s : Store Data) (a : Nat)
    (parents : List Frame) (H : Backend E) (w : OWNER) (es : List E)
    (stack : List Config) (b : Bool)
    (wf : PV_W1_OwnerWellFormed.OwnerWellFormed w s.nextActivation) :
    PV_W1_TLSLeaves.Post b C (initializerEntry s a parents b stack) H w
      [PV_FN_THREAD_f170.arg] es := by
  cases b with
  | false => exact PV_W1_TLSLeaves.f469 C _ H w _ es wf
  | true => exact PV_W1_TLSLeaves.f468 C _ H w _ es wf

def dropType : Data := match PV_THR2_F170.node35 with
  | .leaf (.drop _ _ ty _ _) => ty
  | _ => .null

def dropEntry (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (stack : List Config) : Entry :=
  ⟨s,a,parents,loops,PV_THR2_F170.block40.drop 10 ++ PV_THR2_F170.live.body.drop 26,
    dropType,[],0,stack⟩

/-- Drop's actual local2 value, with its own full native reply and explicit
argument-reachable effects. A failed source read remains a failed source read. -/
theorem dropCallback {E : Type} (C : Carrier OWNER Data) (s : Store Data) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame) (H : Backend E) (w : OWNER)
    (stack : List Config) (changes : Address → Option Data)
    (wf : PV_W1_OwnerWellFormed.OwnerWellFormed w s.nextActivation) :
    match read C s w a (.local 2) with
    | none => True
    | some value => PV_W1_DropLeaf.Post C (dropEntry s a parents loops stack) H w value changes := by
  cases actual : read C s w a (.local 2) with
  | none => trivial
  | some value => exact PV_W1_DropLeaf.contract C _ H w value changes wf

/-- The getter branch uses the existing FnOnce source_request forwarding law;
its tuple reference is exactly the unary Cell::get argument, at the same fresh
activation. No callback success or receiver-read premise is added. -/
theorem getter {E : Type} (C : Carrier OWNER Data) (e : Entry) (H : Backend E)
    (w : OWNER) (p : Address) (es : List E) (wf : PV_W1_ClosedLeaves.Pre e w) :
    PV_THR2_FnOnceDispatch.request (.child PV_THR2_RunTlsCallable.descriptors.1 e.store.nextActivation
      [PV_THR2_F2Call.descriptors.2,PV_FN_THREAD_f207.tuple p]) =
      .child PV_THR2_F2Call.descriptors.2 e.store.nextActivation
        [PV_STX2_TypedReferences.reference p .null] ∧
    PV_W1_ClosedLeaves.Post18 C e H w [PV_STX2_TypedReferences.reference p .null] es :=
  ⟨PV_THR2_FnOnceDispatch.source_request _ p,PV_W1_ClosedLeaves.f18 C e H w _ es wf⟩

#print axioms initializer
#print axioms dropCallback
#print axioms getter
end PV_FN_THREAD_f170_NativeCalls
