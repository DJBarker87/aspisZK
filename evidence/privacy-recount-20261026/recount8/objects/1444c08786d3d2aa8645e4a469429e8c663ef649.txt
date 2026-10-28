import R1Z.ProverRw18InlineContext
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18ContextStep
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open ProverRw18InlineContext
variable [ExternalTypes] [ExternalFuns]

def project (flow : ControlFlow (Iter × Q × Q) (Q × Q)) :
    ControlFlow (Iter × Q × Q) Q :=
  match flow with
  | .done final => .done final.1
  | .cont state => .cont state

theorem body (lambda : Q) (iterator : Iter) (out power : Q) :
    ProverRw18InlineContext.body lambda iterator out power = (do
      let flow ← PV_RW_IteratorStateSource.body lambda iterator (out,power)
      ok (project flow)) := by
  unfold ProverRw18InlineContext.body PV_RW_IteratorStateSource.body
    PV_RW_IteratorStateSource.iterator_state_step.iterator_state_step
  cases h : core.slice.iter.IteratorSliceIter.next iterator with
  | fail error => rfl
  | div => rfl
  | ok pair =>
    rcases pair with ⟨head,next⟩
    cases head with
    | none => rfl
    | some value =>
      simp [bind_tc_ok,bind_assoc_eq,project]

#print axioms body
end R1Z.ProverRw18ContextStep
