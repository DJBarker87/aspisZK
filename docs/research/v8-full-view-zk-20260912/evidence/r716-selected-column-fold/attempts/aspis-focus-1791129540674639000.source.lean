import AspisV8R19.R710SelectedActivePolynomial
import AspisV8R19.R370KernelEvaluation
import Mathlib.Tactic

set_option autoImplicit false
namespace AspisV8R19.R716SelectedColumnFold
open scoped BigOperators
open AspisV8R17
open AspisV8R19.R710SelectedActivePolynomial
open AspisR19.R370KernelEvaluation

noncomputable section
variable {F : Type*} [CommRing F]

def direction (alpha : F) (j : J) (r : Nat) : F :=
  unitVector (base j + slot j) r - alpha^(slot j) * unitVector (base j) r

def pairDir (alpha : F) (j : J) : Fin 256 × Fin 4 → F :=
  fun i => direction alpha j (4*i.1.val+i.2.val)

lemma slot_bounds (j : J) : 1 ≤ slot j ∧ slot j < 4 := by
  unfold slot
  have h := (columnIndex j).isLt
  have hm := Nat.mod_lt (columnIndex j).val (by omega : 0 < 3)
  omega

lemma base_block (j : J) : base j = 4 * (22 + (columnIndex j).val / 3) := rfl

lemma block_direction_fold (alpha : F) (b slot : Nat) (hb : b < 256)
    (hs : 1 ≤ slot) (hs' : slot < 4) (d : Fin 256) :
    ∑ s : Fin 4,
      (unitVector (4*b+slot) (4*d.val+s.val) - alpha^slot*unitVector (4*b) (4*d.val+s.val)) * alpha^s.val = 0 := by
  by_cases hdb : d.val = b
  · have hslot : slot = 1 ∨ slot = 2 ∨ slot = 3 := by omega
    rcases hslot with hslot | hslot | hslot
    · rw [Fin.sum_univ_four]
      simp [unitVector, hdb, hslot]
      ring
    · rw [Fin.sum_univ_four]
      simp [unitVector, hdb, hslot]
      ring
    · rw [Fin.sum_univ_four]
      simp [unitVector, hdb, hslot]
      ring
  · have hzero (s : Fin 4) : 4*d.val+s.val ≠ 4*b := by omega
    have hslotzero (s : Fin 4) : 4*d.val+s.val ≠ 4*b+slot := by omega
    simp [unitVector, hzero, hslotzero]

lemma firstFold_pairDir (alpha : F) (j : J) (d : Fin 256) :
    firstFold 256 alpha (pairDir alpha j) d = 0 := by
  let b := 22 + (columnIndex j).val / 3
  have hdiv : (columnIndex j).val / 3 < 233 := by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 3)).mpr
    omega
  have hb : b < 256 := by dsimp [b]; omega
  have hbase : base j = 4*b := by simp [b, base_block]
  have hs := slot_bounds j
  change (∑ s : Fin 4, direction alpha j (4*d.val+s.val) * alpha^s.val) = 0
  simpa [direction, hbase] using block_direction_fold alpha b (slot j) hb hs.1 hs.2 d

lemma direction_top_zero (alpha : F) (j : J) :
    direction alpha j 1020 = 0 ∧ direction alpha j 1021 = 0 ∧
    direction alpha j 1022 = 0 ∧ direction alpha j 1023 = 0 := by
  let b := 22 + (columnIndex j).val / 3
  have hdiv : (columnIndex j).val / 3 < 233 := by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 3)).mpr
    omega
  have hb : b < 255 := by dsimp [b]; omega
  have hbase : base j = 4*b := by simp [b, base_block]
  have hs := slot_bounds j
  have hzero (n : Nat) (hn : 1020 ≤ n) : unitVector (4*b) n = 0 := by
    simp [unitVector]
    omega
  have hslotzero (n : Nat) (hn : 1020 ≤ n) : unitVector (4*b+slot j) n = 0 := by
    simp [unitVector]
    omega
  constructor
  · simp [direction, hbase, hzero 1020 (by omega), hslotzero 1020 (by omega)]
  constructor
  · simp [direction, hbase, hzero 1021 (by omega), hslotzero 1021 (by omega)]
  constructor
  · simp [direction, hbase, hzero 1022 (by omega), hslotzero 1022 (by omega)]
  · simp [direction, hbase, hzero 1023 (by omega), hslotzero 1023 (by omega)]

#print axioms firstFold_pairDir
#print axioms direction_top_zero
end
end AspisV8R19.R716SelectedColumnFold
