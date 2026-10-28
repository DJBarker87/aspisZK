import R1Z.ProverRw18ContextStep
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18ContextBranch
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open ProverRw18InlineContext
variable [ExternalTypes] [ExternalFuns]

theorem some (lambda : Q) (values : Slice U32) (i : Nat)
    (active : i < values.val.length) (out power : Q) :
    run lambda (⟨values,i⟩ : Iter) out power = (do
      let scaled ← aspis_core.field.QM31.mul_m31 power values.val[i]
      let out1 ← aspis_core.field.QM31.add out scaled
      let power1 ← aspis_core.field.QM31.mul power lambda
      run lambda (⟨values,i+1⟩ : Iter) out1 power1) := by
  rw [unfold_run]
  unfold ProverRw18InlineContext.body
  have next := PV_RW_IteratorSource.next_some values i active
  rw [PV_RW_IteratorSource.exact] at next
  rw [next]
  simp [bind_tc_ok,bind_assoc_eq]

theorem none (lambda : Q) (values : Slice U32) (i : Nat)
    (stopped : values.val.length ≤ i) (out power : Q) :
    run lambda (⟨values,i⟩ : Iter) out power = ok out := by
  rw [unfold_run]
  unfold ProverRw18InlineContext.body
  have next := PV_RW_IteratorSource.next_none values i stopped
  rw [PV_RW_IteratorSource.exact] at next
  rw [next]
  rfl

#print axioms some
#print axioms none
end R1Z.ProverRw18ContextBranch
