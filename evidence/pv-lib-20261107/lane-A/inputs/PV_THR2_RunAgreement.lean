import PV_FN_THREAD_f6PrefixTransport
set_option autoImplicit false
noncomputable section
namespace PV_THR2_RunAgreement
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_FN_THREAD_f6Interfaces

/-- Agreement only on the actual requests issued before the saved entry returns.
The equalities concern full replies, including world, events and pending. -/
def BeforeAgreement {E : Type} (N M : Machine E) (x : Entry E) : Prop :=
  ∀ n, BeforeReturn N x n →
    PV_THR2_TableIntrinsic.Agree N.programs M.programs (run N x n) ∧
    PV_THR2_InterpreterAgreement.NativeAgree N.handler M.handler (run N x n)

/-- Tail-recursive advance can expose its last step without reducing a run. -/
theorem advance_last {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (n : Nat) (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance B K P H (n+1) q =
      PV_THR2_IntrinsicState.step B K P H
        (PV_THR2_IntrinsicState.advance B K P H n q) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    exact ih (PV_THR2_IntrinsicState.step B K P H q)

/-- ONE induction on steps gives identity at every prefix through first return.
No agreement is demanded on the resumed caller. Carrier/control are fixed; only
issued callee resolution and issued native requests need per-instance proofs. -/
theorem prefix_identity {E : Type} (M N : Machine E) (x : Entry E)
    (carrier : M.carrier = N.carrier) (control : M.control = N.control)
    (agreement : BeforeAgreement N M x) :
    M.carrier = N.carrier ∧ M.control = N.control ∧
      ∀ n, BeforeReturn N x n → run M x n = run N x n := by
  refine ⟨carrier,control,?_⟩
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro before
    have earlier : BeforeReturn N x n := by
      intro k hk
      exact before k (Nat.lt_trans hk (Nat.lt_succ_self n))
    have previous := ih earlier
    have same := agreement n earlier
    have next := PV_THR2_InterpreterAgreement.step_eq N.carrier N.control
      N.programs M.programs N.handler M.handler (run N x n) same.1 same.2
    unfold PV_FN_THREAD_f6Interfaces.run at previous ⊢
    rw [advance_last,advance_last,previous,carrier,control]
    exact next.symm

#print axioms BeforeAgreement
#print axioms advance_last
#print axioms prefix_identity
end PV_THR2_RunAgreement
