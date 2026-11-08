import PV_FN_W4_StoreCounter
import PV_FN_W4_CallBoundary
import PV_W1_ArgumentEffects
set_option autoImplicit false
noncomputable section
namespace PV_FN_W4_NativeContract
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_W1_OwnerNativeFrame

def evaluated (C : Carrier OWNER Data) (s : Store Data) (w : OWNER) (a : Nat)
    (call : PV_FN_W4_CallBoundary.Call) :=
  (operands C w a call.args s).orElse
    (fun _ => operands (PV_THR2_AggregateCompletion.carrier C) w a call.args s)

def entry (t : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (call : PV_FN_W4_CallBoundary.Call)
    (vs : List Data) (stack : List Config) : PV_W1_LeafBoundary.Entry :=
  ⟨t,a,parents,loops,rest,PV_FN_W4_CallBoundary.token call,vs,call.destination,stack⟩

theorem counter (C : Carrier OWNER Data) (s t : Store Data) (w : OWNER) (a : Nat)
    (call : PV_FN_W4_CallBoundary.Call) (vs : List Data)
    (h : evaluated C s w a call = some (vs,t)) : t.nextActivation = s.nextActivation := by
  unfold evaluated at h
  cases first : operands C w a call.args s with
  | none =>
    simp only [first,Option.orElse_none] at h
    exact PV_FN_W4_StoreCounter.operandsCounter (PV_THR2_AggregateCompletion.carrier C) s t w a call.args vs h
  | some pair =>
    simp only [first,Option.orElse_some,Option.some.injEq] at h
    cases h
    exact PV_FN_W4_StoreCounter.operandsCounter C s t w a call.args vs first

/-- Actual W1 contract at a source-selected native call. There is no supplied
receiver, read, old-store identity, native registry-frame or callee Pre premise.
Use ONLY for named LEAF rows: BODY calls still require their own CLOSED contract.
The explicit argument-reachable changes survive every native answer branch. -/
theorem atActualCall {E : Type} (C : Carrier OWNER Data) (s : Store Data)
    (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (call : PV_FN_W4_CallBoundary.Call)
    (H : Backend E) (w : OWNER) (es : List E) (stack : List Config)
    (changes : Address → Option Data)
    (pre : PV_W1_OwnerWellFormed.OwnerWellFormed w s.nextActivation) :
    match evaluated C s w a call with
    | none => True
    | some (vs,t) => PV_W1_ArgumentEffects.Post C (entry t a parents loops rest call vs stack) H w es changes := by
  cases h : evaluated C s w a call with
  | none => trivial
  | some pair =>
    rcases pair with ⟨vs,t⟩
    apply PV_W1_ArgumentEffects.full_reply
    change PV_W1_OwnerWellFormed.OwnerWellFormed w t.nextActivation
    rw [counter C s t w a call vs h]
    exact pre
#print axioms counter
#print axioms atActualCall
end PV_FN_W4_NativeContract
