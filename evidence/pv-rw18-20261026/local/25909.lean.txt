import R1Z.ProverRw18ContextInduction
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18ContextBounded
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open ProverRw18InlineContext
variable [ExternalTypes] [ExternalFuns]

theorem body_native (lambda : Q) (iterator : Iter) (out power : Q) :
    ProverRw18InlineContext.body lambda iterator out power = (do
      let flow ← PV_RW_NativeForSource.body (ProverRw18ContextInduction.step lambda) iterator (out,power)
      ok (ProverRw18ContextStep.project flow)) := by
  rw [ProverRw18ContextStep.body,PV_RW_IteratorStateSource.control]
  rfl

theorem bounded (lambda : Q) (fuel : Nat) (iterator : Iter) (out power : Q) :
    ProverRw18InlineContext.bounded lambda fuel iterator out power = (do
      let final ← PV_RW_NativeForSource.bounded (ProverRw18ContextInduction.step lambda)
        fuel iterator (out,power)
      ok final.1) := by
  induction fuel generalizing iterator out power with
  | zero => rfl
  | succ fuel ih =>
    rw [ProverRw18InlineContext.bounded,PV_RW_NativeForSource.bounded,body_native]
    simp only [bind_assoc_eq]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro flow _
    cases flow with
    | done final => rfl
    | cont state =>
      rcases state with ⟨next,out1,power1⟩
      exact ih next out1 power1

#print axioms body_native
#print axioms bounded
end R1Z.ProverRw18ContextBounded
