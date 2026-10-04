import AspisV8R19.R717SelectedCoreImage
import AspisV8R19.R682FullQueryNormalization
import AspisV8R19.R683QueryCoreCoinImage
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R720QueryActiveCoreImage
open scoped BigOperators
open AspisV8R17 AspisV8R16 AspisR19
open AspisV8R19.R710SelectedActivePolynomial
open AspisV8R19.R717SelectedCoreImage AspisV8R19.R716SelectedColumnFold
open AspisV8R19.R682FullQueryNormalization AspisV8R19.R683QueryCoreCoinImage
open AspisV8R19.R698ActiveCoreLayout AspisV8R19.R707FullActiveDeterminant
open AspisV8R19.R662FullIndexedMaskPreservation AspisV8R19.R574SparseGCorePolynomial
open HighRepairInvariant
noncomputable section
variable {F : Type*} [Field F] [NeZero (2:F)]

def combinationQ (alpha : F) (x : J → F) : Index 256 → F :=
  fun i => combination alpha x (4*i.1.val+i.2.val)

lemma flatten_combinationQ (alpha : F) (x : J → F) (r : Nat) (hr : r < 1024) :
    flattenFull (combinationQ alpha x) r = combination alpha x r := by
  unfold flattenFull combinationQ
  rw [dif_pos hr]
  simp only [Nat.div_add_mod]

lemma rowCode_ge_91 (i : J) : 91 ≤ rowCode i := by
  cases i with
  | inr u => cases u; simp [rowCode]
  | inl i =>
    change 91 ≤ i.val.val
    have hb := highActive_bounds i.val i.property
    by_contra hn
    have hvals : i.val.val = 88 ∨ i.val.val = 89 ∨ i.val.val = 90 := by omega
    rcases hvals with h | h | h
    · have hi : i.val = (88:Fin 1024) := Fin.ext h
      have hm : (88:Fin 1024) ∈ highActive := hi ▸ i.property
      exact (by decide : (88:Fin 1024) ∉ highActive) hm
    · have hi : i.val = (89:Fin 1024) := Fin.ext h
      have hm : (89:Fin 1024) ∈ highActive := hi ▸ i.property
      exact (by decide : (89:Fin 1024) ∉ highActive) hm
    · have hi : i.val = (90:Fin 1024) := Fin.ext h
      have hm : (90:Fin 1024) ∈ highActive := hi ▸ i.property
      exact (by decide : (90:Fin 1024) ∉ highActive) hm

lemma sourceChord_low_preserved (half a b c : F) (q v : Nat → F)
    (hsame : ∀ r, 88 ≤ r → q r = v r) (r : Nat) (hr : 91 ≤ r) :
    sourceChord half q a b c r = sourceChord half v a b c r := by
  have hdiff : ∀ n, 88 ≤ n → (fun z => q z-v z) n = 0 := by
    intro n hn
    change q n-v n = 0
    rw [hsame n hn,sub_self]
  have hz := HighQueryGCore.sourceChord_support half (fun z => q z-v z) 44 hdiff a b c r (by omega)
  have hfun : (fun z => q z-v z) = (fun z => (1:F)*q z+(-1:F)*v z) := by
    funext z
    ring
  rw [hfun,sourceChord_linear] at hz
  apply sub_eq_zero.mp
  simpa only [one_mul, neg_one_mul, sub_eq_add_neg] using hz

lemma direction_ge_1020 (alpha : F) (j : J) (r : Nat) (hr : 1020 ≤ r) :
    direction alpha j r = 0 := by
  let b := 22 + (columnIndex j).val / 3
  have hdiv : (columnIndex j).val / 3 < 233 := by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 3)).mpr
    omega
  have hb : b < 255 := by dsimp [b]; omega
  have hbase : base j = 4*b := by simp [b, base_block]
  have hs := slot_bounds j
  have hzero : unitVector (F:=F) (4*b) r = 0 := by
    simp [unitVector]
    omega
  have hslotzero : unitVector (F:=F) (4*b+slot j) r = 0 := by
    simp [unitVector]
    omega
  simp [direction,hbase,hzero,hslotzero]

lemma combination_ge_1020 (alpha : F) (x : J → F) (r : Nat) (hr : 1020 ≤ r) :
    combination alpha x r = 0 := by
  unfold combination
  apply Finset.sum_eq_zero
  intro j _
  rw [direction_ge_1020 alpha j r hr,mul_zero]

lemma flatten_same_high_combination (alpha : F) (x : J → F)
    (v : Index 256 → F)
    (hsame : ∀ i : Index 256, 22 ≤ i.1.val → v i = combinationQ alpha x i)
    (r : Nat) (hr : 88 ≤ r) :
    flattenFull v r = combination alpha x r := by
  by_cases hlt : r < 1024
  · rw [flatten_same_high v (combinationQ alpha x) (fun i hi => hsame i hi) r hr]
    exact flatten_combinationQ alpha x r hlt
  · rw [flattenFull,dif_neg hlt]
    exact (combination_ge_1020 alpha x r (by omega)).symm

lemma combinationQ_top (alpha : F) (x : J → F) :
    flattenFull (combinationQ alpha x) 1020 = 0 ∧
    flattenFull (combinationQ alpha x) 1021 = 0 ∧
    flattenFull (combinationQ alpha x) 1022 = 0 ∧
    flattenFull (combinationQ alpha x) 1023 = 0 := by
  rw [flatten_combinationQ alpha x 1020 (by omega),flatten_combinationQ alpha x 1021 (by omega),
    flatten_combinationQ alpha x 1022 (by omega),flatten_combinationQ alpha x 1023 (by omega)]
  exact combination_top alpha x

#print axioms flatten_combinationQ
#print axioms rowCode_ge_91
#print axioms sourceChord_low_preserved
#print axioms flatten_same_high_combination
#print axioms combinationQ_top
end
end AspisV8R19.R720QueryActiveCoreImage
