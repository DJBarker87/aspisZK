import AspisV8R19.R716SelectedColumnFold
import AspisV8R19.R714SelectedActiveNonzero
import AspisV8R19.R574SparseGCorePolynomial
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R717SelectedCoreImage
open AspisV8R17 R710SelectedActivePolynomial R716SelectedColumnFold
open AspisR19 R370KernelEvaluation R574SparseGCorePolynomial
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2:F)]

def chordLinear (half a b c : F) (r : Nat) : (Nat → F) →ₗ[F] F where
  toFun := fun q => sourceChord half q a b c r
  map_add' := by
    intro q s
    simpa only [Pi.add_def,one_mul] using sourceChord_linear half q s 1 1 a b c r
  map_smul' := by
    intro t q
    simpa only [Pi.smul_def,smul_eq_mul,zero_mul,add_zero] using sourceChord_linear half q q t 0 a b c r

def combination (alpha : F) (x : J → F) (r : Nat) : F :=
  ∑ j, x j * direction alpha j r

lemma combination_chord (half alpha a b c : F) (x : J → F) (i : J) :
    sourceChord half (combination alpha x) a b c (R707FullActiveDeterminant.rowCode i) =
      (sourceMinor half alpha a b c).mulVec x i := by
  have h := map_sum (chordLinear half a b c (R707FullActiveDeterminant.rowCode i))
    (fun j => x j • direction alpha j) Finset.univ
  simp only [map_smul] at h
  change sourceChord half (∑ j, x j • direction alpha j) a b c
    (R707FullActiveDeterminant.rowCode i) = _ at h
  rw [show (∑ j, x j • direction alpha j) = combination alpha x by
    funext r; simp [combination,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]] at h
  rw [h]
  simp only [Matrix.mulVec,dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  change x j * sourceChord half (direction alpha j) a b c _ =
    sourceChord half (direction alpha j) a b c _ * x j
  ring

lemma combination_fold (alpha : F) (x : J → F) (d : Fin 256) :
    firstFold 256 alpha (fun i => combination alpha x (4*i.1.val+i.2.val)) d=0 := by
  simp only [firstFold,combination,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc,← Finset.mul_sum]
  have hz : ∀ j : J, (∑ s : Fin 4, direction alpha j (4*d.val+s.val)*alpha^s.val)=0 := by
    intro j
    exact firstFold_pairDir alpha j d
  simp only [hz,mul_zero,Finset.sum_const_zero]

lemma combination_top (alpha : F) (x : J → F) :
    combination alpha x 1020=0 ∧ combination alpha x 1021=0 ∧
    combination alpha x 1022=0 ∧ combination alpha x 1023=0 := by
  have hz (r : Nat) (hr : r=1020 ∨ r=1021 ∨ r=1022 ∨ r=1023) : combination alpha x r=0 := by
    unfold combination
    apply Finset.sum_eq_zero
    intro j _
    have h := direction_top_zero alpha j
    rcases hr with rfl | rfl | rfl | rfl <;> simp [h]
  exact ⟨hz _ (Or.inl rfl),hz _ (Or.inr (Or.inl rfl)),hz _ (Or.inr (Or.inr (Or.inl rfl))),hz _ (Or.inr (Or.inr (Or.inr rfl)))⟩

theorem selected_core_image (half alpha u v : F) (target : J → F)
    (good : MvPolynomial.eval (activeAssignment alpha u v) (polyMinor half).det ≠ 0) :
    ∃ x : J → F,
      (∀ i, sourceChord half (combination alpha x) (1+u*v) (u*v-1) (-(u+v))
        (R707FullActiveDeterminant.rowCode i)=target i) ∧
      (∀ d : Fin 256, firstFold 256 alpha (fun i => combination alpha x (4*i.1.val+i.2.val)) d=0) ∧
      combination alpha x 1020=0 ∧ combination alpha x 1021=0 ∧
      combination alpha x 1022=0 ∧ combination alpha x 1023=0 := by
  have hd : (sourceMinor half alpha (1+u*v) (u*v-1) (-(u+v))).det ≠ 0 := by
    rw [← determinant_eval]
    exact good
  have hs := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))
  obtain ⟨x,hx⟩ := hs target
  refine ⟨x,?_,combination_fold alpha x,combination_top alpha x⟩
  intro i
  rw [combination_chord]
  exact congrFun hx i

#print axioms combination_chord
#print axioms combination_fold
#print axioms combination_top
#print axioms selected_core_image
end
end AspisV8R19.R717SelectedCoreImage
