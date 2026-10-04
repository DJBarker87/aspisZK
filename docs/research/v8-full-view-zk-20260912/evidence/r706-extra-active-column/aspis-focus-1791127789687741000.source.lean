import AspisV8R19.R702ActiveScalarEmbedding
import Mathlib.Tactic

set_option autoImplicit false
namespace AspisV8R19.R706ExtraActiveColumn
open AspisV8R19.R702ActiveScalarEmbedding
open AspisV8R19.R698ActiveCoreLayout
open AspisR19.SparseGPolynomial AspisV8R17

abbrev I := Fin 1024
abbrev High := R702ActiveScalarEmbedding.High

variable {F : Type*} [CommRing F]

def extraQ (r : Nat) : F := if r = 1018 then 1 else if r = 1016 then -1 else 0

lemma extraQ_1018 : extraQ (F:=F) 1018 = 1 := by simp [extraQ]
lemma extraQ_1016 : extraQ (F:=F) 1016 = -1 := by simp [extraQ]
lemma extraQ_top :
    extraQ (F:=F) 1020 = 0 ∧ extraQ (F:=F) 1021 = 0 ∧
    extraQ (F:=F) 1022 = 0 ∧ extraQ (F:=F) 1023 = 0 := by
  simp [extraQ]

lemma high_not_1016 (i : High) : i.val.val ≠ 1016 := by
  intro h
  have ha : highRow ⟨232, by omega⟩ (0 : Fin 4) ∈ activeCode := by
    have he : highRow ⟨232, by omega⟩ (0 : Fin 4) = i.val := by
      apply Fin.ext
      simpa [highRow] using h.symm
    rw [he]
    exact (Finset.mem_filter.mp i.property).1
  have hs := (block254_active_slots (0 : Fin 4)).mp ha
  omega

lemma high_not_1018 (i : High) : i.val.val ≠ 1018 := by
  intro h
  have ha : highRow ⟨232, by omega⟩ (2 : Fin 4) ∈ activeCode := by
    have he : highRow ⟨232, by omega⟩ (2 : Fin 4) = i.val := by
      apply Fin.ext
      simpa [highRow] using h.symm
    rw [he]
    exact (Finset.mem_filter.mp i.property).1
  have hs := (block254_active_slots (2 : Fin 4)).mp ha
  omega

lemma extraQ_high_zero (i : High) : extraQ (F:=F) i.val.val = 0 := by
  simp [extraQ, high_not_1018 i, high_not_1016 i]

def precedingHigh : High := ⟨⟨1019, by omega⟩, by decide⟩

lemma precedingHigh_code : precedingHigh.val.val = 1019 := rfl
lemma precedingHigh_column : selectedColumn precedingHigh = (698 : Fin 699) := by decide

lemma scalar_chord_extra_high (half : F) (i : High) :
    sourceChord half (extraQ (F:=F)) 2 0 0 i.val.val = 0 := by
  by_cases hnt : Nontrivial F
  · letI : Nontrivial F := hnt
    rw [source_scalar half 2 (extraQ (F:=F)) i.val.val i.val.isLt]
    rw [extraQ_high_zero]
    ring
  · haveI : Subsingleton F := not_nontrivial_iff_subsingleton.mp hnt
    exact Subsingleton.elim _ _

#print axioms extraQ_1018
#print axioms extraQ_top
#print axioms extraQ_high_zero
#print axioms precedingHigh_column
#print axioms scalar_chord_extra_high
end AspisV8R19.R706ExtraActiveColumn
