import PV_THR2_HandlerExecutionAgreement
import PV_THR2_TableIntrinsic
set_option autoImplicit false
namespace PV_THR2_InterpreterAgreement
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_IntrinsicState
/-- Symbolic local native agreement on the actual running frame, including
pending, every failure reply, full world/events and suspended callers. -/
def NativeAgree {W E : Type}
    (left right : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : State W E) : Prop :=
  ∀ c, q.current.status = .running c →
    PV_THR2_HandlerExecutionAgreement.Agree left right c q.current.world
/-- The higher-order intrinsic selection and return administration do not
consult native replies. Reuse the ordinary instruction-shape agreement once. -/
theorem handler_step {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (left right : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : State W E) (same : NativeAgree left right q) :
    PV_THR2_IntrinsicState.step B K P left q = PV_THR2_IntrinsicState.step B K P right q := by
  unfold PV_THR2_IntrinsicState.step
  cases status : q.current.status with
  | running c =>
    simp only
    cases selected : PV_THR2_Catch316Segment.select c with
    | some segment => simp only
    | none =>
      simp only [PV_THR2_HandlerExecutionAgreement.step B K P left right c q.current.world (same c status)]
  | returned r store => cases r <;> rfl
  | fault f store => cases f <;> rfl
  | undefined site store => rfl
/-- Combined table AND handler agreement. The existing slice3 table lemma is
consumed BY NAME; the native equality concerns only the saved request. -/
theorem step_eq {W E : Type} (B : Carrier W Data) (K : Control)
    (leftP rightP : Data → Option PV_STX2_SliceSyntax.Program)
    (leftH rightH : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : State W E)
    (table : PV_THR2_TableIntrinsic.Agree leftP rightP q)
    (native : NativeAgree leftH rightH q) :
    PV_THR2_IntrinsicState.step B K leftP leftH q = PV_THR2_IntrinsicState.step B K rightP rightH q := by
  rw [PV_THR2_TableIntrinsic.step B K leftP rightP leftH q table]
  exact handler_step B K rightP leftH rightH q native
/-- ONE induction over the retained finite trace transports table and native
handler simultaneously. Its local agreements are INTERNAL obligations discharged
on that composition, never hypotheses of the privacy endpoint or closure.
No source proof, store normalization or exclusion-certificate walk is repeated. -/
theorem run {W E : Type} (B : Carrier W Data) (K : Control)
    (leftP rightP : Data → Option PV_STX2_SliceSyntax.Program)
    (leftH rightH : PV_STX2_Native.Request Data → W → Reply W E Data)
    (n : Nat) (q : State W E)
    (same : ∀ k, k < n →
      PV_THR2_TableIntrinsic.Agree leftP rightP (PV_THR2_IntrinsicState.advance B K leftP leftH k q) ∧
      NativeAgree leftH rightH (PV_THR2_IntrinsicState.advance B K leftP leftH k q)) :
    PV_THR2_IntrinsicState.advance B K rightP rightH n q = PV_THR2_IntrinsicState.advance B K leftP leftH n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    have first := same 0 (Nat.zero_lt_succ n)
    change PV_THR2_TableIntrinsic.Agree leftP rightP q ∧ NativeAgree leftH rightH q at first
    have equal := step_eq B K leftP rightP leftH rightH q first.1 first.2
    rw [PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.advance,← equal]
    apply ih
    intro k hk
    exact same (k+1) (by omega)
#print axioms NativeAgree
#print axioms handler_step
#print axioms step_eq
#print axioms run
end PV_THR2_InterpreterAgreement
