import FIv_EqualityValue
import R0P.SemDecision
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_EqualityProduct
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
open FIv_NativeArray (value)
open scoped BigOperators

theorem product (left right : Array NQ 10#usize) (n start : Nat) :
    FIv_EqualityLoop.tail left right start n=
      ∏ j : Fin n,(value left (start+j.val)*value right (start+j.val)+
        (1-value left (start+j.val))*(1-value right (start+j.val))) := by
  induction n generalizing start with
  | zero => simp only [FIv_EqualityLoop.tail,Fin.prod_univ_zero]
  | succ n ih =>
    rw [FIv_EqualityShape.step,Fin.prod_univ_succ,ih]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [Nat.add_assoc,Nat.add_comm 1 j.val]

theorem model (left right : Array NQ 10#usize) :
    FIv_EqualityValue.weight left right=R0P.SemSource.eqValue
      (fun j : Fin 10=>value left j.val) (fun j : Fin 10=>value right j.val) := by
  rw [FIv_EqualityValue.weight,product]
  unfold R0P.SemSource.eqValue
  apply Finset.prod_congr rfl
  intro j _
  simp only [Nat.zero_add]
  ring

#print axioms product
#print axioms model
end AspisR1.FIv_EqualityProduct
end
