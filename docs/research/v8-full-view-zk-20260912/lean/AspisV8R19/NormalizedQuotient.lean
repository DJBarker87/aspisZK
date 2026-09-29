import AspisV8R19.NormalizedQuerySection
import AspisV8R19.HighRepairInvariant

/-! A normalized scalar direction supplies a four-slot quotient that is
raw-zero on the roots and fold-zero everywhere. G-core, code image, legal
mask support, and source-executable normalization remain separate. -/
namespace AspisR19.NormalizedQuotient
open NormalizedQuerySection HighRepairInvariant AspisCircleTensorBinding
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

def slotFactor (alpha : F) (s k : Fin 4) : F :=
  (if k=s then 1 else 0) - alpha^s.val*(if k=0 then 1 else 0)

def quotient (t : Fin 22 → F) (ht : Function.Injective t) (alpha : F)
    (d : Fin 32) (s : Fin 4) (i : Index 32) : F :=
  normalized t ht d i.1 * slotFactor alpha s i.2

theorem quotient_high (t : Fin 22 → F) (ht : Function.Injective t) (alpha : F)
    (d : Fin 32) (s : Fin 4) (i : Index 32) (hi : 22 ≤ i.1.val) :
    quotient t ht alpha d s i = column alpha d s i := by
  rw [quotient,normalized_high t ht d i.1 hi]
  simp only [slotFactor,column,unit,Prod.ext_iff]
  by_cases hd : i.1=d <;> by_cases hs : i.2=s <;> by_cases h0 : i.2=0 <;>
    simp [hd,hs,h0]

omit [NeZero (2 : F)] in
theorem slot_fold (alpha : F) (s : Fin 4) :
    ∑ k : Fin 4, alpha^k.val * slotFactor alpha s k = 0 := by
  simp [slotFactor,mul_sub,Finset.sum_sub_distrib,mul_ite]

theorem quotient_fold (t : Fin 22 → F) (ht : Function.Injective t) (alpha : F)
    (d : Fin 32) (s : Fin 4) (i : Fin 32) :
    ∑ k : Fin 4, alpha^k.val * quotient t ht alpha d s (i,k) = 0 := by
  have h : ∀ k : Fin 4, alpha^k.val * quotient t ht alpha d s (i,k) =
      normalized t ht d i * (alpha^k.val * slotFactor alpha s k) := by
    intro k; unfold quotient; ring
  simp only [h,← Finset.mul_sum,slot_fold,mul_zero]

theorem quotient_eval (t : Fin 22 → F) (ht : Function.Injective t) (alpha : F)
    (d : Fin 32) (s k : Fin 4) (x : F) :
    evaluate (fun i => quotient t ht alpha d s (i,k)) x =
      evaluate (normalized t ht d) x * slotFactor alpha s k := by
  simp only [evaluate,quotient,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _; ring

theorem quotient_root (t : Fin 22 → F) (ht : Function.Injective t) (alpha : F)
    (d : Fin 32) (s k : Fin 4) (j : Fin 22) :
    evaluate (fun i => quotient t ht alpha d s (i,k)) (t j) = 0 := by
  rw [quotient_eval,normalized_root,zero_mul]

theorem quotient_raw_zero (t : Fin 22 → F) (ht : Function.Injective t) (alpha : F)
    (d : Fin 32) (s : Fin 4) (j : Fin 22) (x y : F) :
    let a := evaluate (fun i => quotient t ht alpha d s (i,0)) (t j)
    let b := evaluate (fun i => quotient t ht alpha d s (i,1)) (t j)
    let c := evaluate (fun i => quotient t ht alpha d s (i,2)) (t j)
    let e := evaluate (fun i => quotient t ht alpha d s (i,3)) (t j)
    a+b*y+c*x+e*x*y=0 ∧ a-b*y+c*x-e*x*y=0 ∧
    a-b*y-c*x+e*x*y=0 ∧ a+b*y-c*x-e*x*y=0 := by
  simp only [quotient_root]; simp

theorem quotient_final_zero (t : Fin 22 → F) (ht : Function.Injective t) (alpha : F)
    (d : Fin 32) (s : Fin 4) (z x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    let a := evaluate (fun i => quotient t ht alpha d s (i,0)) z
    let b := evaluate (fun i => quotient t ht alpha d s (i,1)) z
    let c := evaluate (fun i => quotient t ht alpha d s (i,2)) z
    let e := evaluate (fun i => quotient t ht alpha d s (i,3)) z
    AspisV8R16.foldFour x y alpha
      (a+b*y+c*x+e*x*y) (a-b*y+c*x-e*x*y)
      (a-b*y-c*x+e*x*y) (a+b*y-c*x-e*x*y) = 0 := by
  dsimp only
  rw [AspisV8R16.fold_channels x y alpha _ _ _ _ (NeZero.ne 2) hx hy]
  simp only [quotient_eval]
  have h := slot_fold alpha s
  rw [show (∑ k : Fin 4, alpha^k.val * slotFactor alpha s k) =
    slotFactor alpha s 0 + alpha*slotFactor alpha s 1 +
      alpha^2*slotFactor alpha s 2 + alpha^3*slotFactor alpha s 3 by
        simp [Fin.sum_univ_succ]; ring] at h
  linear_combination evaluate (normalized t ht d) z * h

theorem evaluate_fold_zero (q : Index 32 → F) (alpha : F)
    (hq : ∀ i, ∑ k : Fin 4, alpha^k.val * q (i,k)=0) (z : F) :
    ∑ k : Fin 4, alpha^k.val * evaluate (fun i => q (i,k)) z = 0 := by
  simp only [evaluate,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  simp only [← mul_assoc,← Finset.sum_mul,hq,mul_zero,zero_mul]

theorem final_zero_of_coefficients (q : Index 32 → F) (alpha : F)
    (hq : ∀ i, ∑ k : Fin 4, alpha^k.val * q (i,k)=0)
    (z x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    let a := evaluate (fun i => q (i,0)) z
    let b := evaluate (fun i => q (i,1)) z
    let c := evaluate (fun i => q (i,2)) z
    let d := evaluate (fun i => q (i,3)) z
    AspisV8R16.foldFour x y alpha
      (a+b*y+c*x+d*x*y) (a-b*y+c*x-d*x*y)
      (a-b*y-c*x+d*x*y) (a+b*y-c*x-d*x*y)=0 := by
  dsimp only
  rw [AspisV8R16.fold_channels x y alpha _ _ _ _ (NeZero.ne 2) hx hy]
  simpa [Fin.sum_univ_succ,add_assoc] using evaluate_fold_zero q alpha hq z

#print axioms evaluate_fold_zero
#print axioms final_zero_of_coefficients
#print axioms quotient_high
#print axioms slot_fold
#print axioms quotient_fold
#print axioms quotient_eval
#print axioms quotient_root
#print axioms quotient_raw_zero
#print axioms quotient_final_zero
end
end AspisR19.NormalizedQuotient
