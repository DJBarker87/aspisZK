import AspisV8R19.FullCoefficientBoundary

/-! Exact-field coefficient-kernel evaluation. No Rust execution or
correction existence is asserted by this file. -/
set_option autoImplicit false
namespace AspisR19.R370KernelEvaluation
open BetaUniformCorrection FullCoefficientBoundary
open scoped BigOperators
variable {F : Type*} [CommRing F]

def kernelEval (n : Nat) (quarter alpha : F)
    (q w : Fin n × Fin 4 → F) : F :=
  ∑ k : Fin 7, coefficient (sourceKernel n k.val quarter) q w * alpha^k.val

def firstFold (n : Nat) (alpha : F) (q : Fin n × Fin 4 → F) (d : Fin n) : F :=
  ∑ s : Fin 4, q (d,s) * alpha^s.val

def dualFold (n : Nat) (alpha : F) (w : Fin n × Fin 4 → F) (d : Fin n) : F :=
  ∑ t : Fin 4, w (d,t) * alpha^((4-t.val)%4)

theorem diagonal_eval (quarter alpha : F) (s t : Fin 4) :
    (∑ k : Fin 7, (if s.val+(4-t.val)%4=k.val then quarter else 0)*alpha^k.val) =
      quarter*alpha^s.val*alpha^((4-t.val)%4) := by
  let e : Fin 7 := ⟨s.val+(4-t.val)%4, by have h := Nat.mod_lt (4-t.val) (by omega : 0<4); omega⟩
  rw [Finset.sum_eq_single e]
  · simp [e,pow_add,mul_assoc]
  · intro k _ hne
    have h : s.val+(4-t.val)%4 ≠ k.val := by
      intro he
      apply hne
      apply Fin.ext
      exact he.symm
    simp [h]
  · simp

theorem kernel_eval_pairing (n : Nat) (quarter alpha : F)
    (q w : Fin n × Fin 4 → F) :
    kernelEval n quarter alpha q w =
      quarter * ∑ d : Fin n, firstFold n alpha q d * dualFold n alpha w d := by
  simp only [kernelEval,coefficient_blocks,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Eq.trans ?_ (by
    simp only [firstFold,dualFold,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring)
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  calc
    _ = (∑ k : Fin 7, (if s.val+(4-t.val)%4=k.val then quarter else 0)*alpha^k.val)*q (d,s)*w (d,t) := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = quarter*alpha^s.val*alpha^((4-t.val)%4)*q (d,s)*w (d,t) := by
      rw [diagonal_eval]

theorem kernel_eval_zero_of_first_fold (n : Nat) (quarter alpha : F)
    (q w : Fin n × Fin 4 → F)
    (hq : ∀ d, firstFold n alpha q d=0) :
    kernelEval n quarter alpha q w=0 := by
  rw [kernel_eval_pairing]
  simp [hq]

#print axioms diagonal_eval
#print axioms kernel_eval_pairing
#print axioms kernel_eval_zero_of_first_fold
end AspisR19.R370KernelEvaluation
