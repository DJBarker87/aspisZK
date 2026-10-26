import R0P.LogUpCompress
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18GenericPolynomial
open scoped BigOperators
variable {F : Type} [Field F]

def horner : List F → F → F
  | [], _ => 0
  | value::values, lambda => value+lambda*horner values lambda

theorem ofFn (n : Nat) (values : Fin n → F) (lambda : F) :
    horner (List.ofFn values) lambda=∑ i : Fin n, lambda^i.val*values i := by
  induction n with
  | zero => simp [horner]
  | succ n ih =>
    rw [List.ofFn_succ,horner,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,one_mul,Fin.val_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc,← pow_succ']

theorem copy (tag : F) (values : Fin 16 → F) (lambda : F) :
    tag+lambda*horner (List.ofFn values) lambda=(R0P.compressPoly (tag,values)).eval lambda := by
  rw [ofFn,R0P.compressPoly_eval]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [R0P.copy_powers_eq,← mul_assoc,← pow_succ']

#print axioms ofFn
#print axioms copy
end R1Z.ProverRw18GenericPolynomial
