import R1Z.ProverRw18FieldReference
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18FieldFiniteSum
open Aeneas Aeneas.Std ProverRw18FieldMeaning
open scoped BigOperators

theorem eval_ofFn (n : Nat) (values : Fin n → U32) (lambda : K) :
    ProverRw18FieldModel.eval (List.ofFn values) lambda=
      ∑ i : Fin n, lambda^i.val*((values i).val : K) := by
  induction n with
  | zero => simp [ProverRw18FieldModel.eval]
  | succ n ih =>
    rw [List.ofFn_succ,ProverRw18FieldModel.eval,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,one_mul,Fin.val_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc,← pow_succ']

#print axioms eval_ofFn
end R1Z.ProverRw18FieldFiniteSum
