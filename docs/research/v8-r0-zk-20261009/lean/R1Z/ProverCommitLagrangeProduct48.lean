import R1Z.ProverCommitInterpolationSchedule48
import Mathlib.LinearAlgebra.Lagrange
/-! The owned omitted-node product, normalized by its denominator, is the
standard Lagrange basis. Bounds stay symbolic. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitLagrangeProduct48
open Polynomial
open ProverCommitInterpolationSchedule48
open scoped BigOperators
variable {K : Type} [Field K]

theorem normalized_product (i start n : Nat) :
    C ((denProd i start n : K)⁻¹)*(polyProd i start n : K[X])=
      ∏ k : Fin n, if i=start+k.val then 1 else
        Lagrange.basisDivisor (i : K) ((start+k.val : Nat) : K) := by
  induction n generalizing start with
  | zero => simp only [denProd,polyProd,inv_one,map_one,mul_one,Fin.prod_univ_zero]
  | succ n ih =>
    rw [denProd,polyProd,Fin.prod_univ_succ]
    have tails : (∏ k : Fin n, if i=start+(Fin.succ k).val then (1 : K[X]) else
        Lagrange.basisDivisor (i : K) ((start+(Fin.succ k).val : Nat) : K))=
        ∏ k : Fin n, if i=(start+1)+k.val then 1 else
          Lagrange.basisDivisor (i : K) (((start+1)+k.val : Nat) : K) := by
      apply Finset.prod_congr rfl
      intro k hk
      have he : start+(Fin.succ k).val=(start+1)+k.val := by
        change start+(k.val+1)=(start+1)+k.val
        omega
      rw [he]
    rw [tails,← ih (start+1)]
    simp only [Fin.val_zero,Nat.add_zero]
    by_cases h : i=start
    · simp only [if_pos h,one_mul]
    · simp only [if_neg h,mul_inv_rev,map_mul,Lagrange.basisDivisor]
      ring

theorem normalized_basis (i : Fin 28) :
    C ((denProd i.val 0 28 : K)⁻¹)*(polyProd i.val 0 28 : K[X])=
      Lagrange.basis Finset.univ (fun j : Fin 28 => (j.val : K)) i := by
  rw [normalized_product,Lagrange.basis]
  have he : (∏ k : Fin 28, if i.val=k.val then (1 : K[X]) else
      Lagrange.basisDivisor (i.val : K) (k.val : K))=
      ∏ k ∈ (Finset.univ : Finset (Fin 28)).erase i,
        if i.val=k.val then 1 else Lagrange.basisDivisor (i.val : K) (k.val : K) := by
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin 28))
      (fun k => if i.val=k.val then (1 : K[X]) else Lagrange.basisDivisor (i.val : K) (k.val : K)) (Finset.mem_univ i)]
    simp only [if_true,one_mul]
  simp only [Nat.zero_add]
  rw [he]
  apply Finset.prod_congr rfl
  intro k hk
  rw [if_neg (fun h => (Finset.mem_erase.mp hk).1 (Fin.ext h.symm))]

#print axioms normalized_product
#print axioms normalized_basis
end R1Z.ProverCommitLagrangeProduct48
