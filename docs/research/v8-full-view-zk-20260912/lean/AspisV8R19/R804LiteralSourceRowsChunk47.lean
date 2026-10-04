import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk27
import AspisV8R19.R799ActiveSourceCellsChunk28
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk47
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk47
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow972 (j : Fin 222) : M := if j.val = 187 then 1073741826 else if j.val = 188 then 1073741826 else if j.val = 189 then 1073741772 else if j.val = 190 then 1073741483 else 0

theorem literalSourceMatrix_row972 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨189, by decide⟩ : Fin 214)) = literalRow972 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 187
  · have hj : j = (⟨187, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow972]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨242, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 972 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk27.cell_d242_s0_row972_col187
  by_cases h1 : j.val = 188
  · have hj : j = (⟨188, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow972, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨242, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 972 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk27.cell_d242_s1_row972_col188
  by_cases h2 : j.val = 189
  · have hj : j = (⟨189, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow972, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨243, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 972 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk27.cell_d243_s0_row972_col189
  by_cases h3 : j.val = 190
  · have hj : j = (⟨190, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow972, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨243, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 972 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk27.cell_d243_s1_row972_col190
  · simp [literalRow972, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk47.row972_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row972

def literalRow974 (j : Fin 222) : M := if j.val = 189 then 2147483612 else if j.val = 190 then 2147483409 else 0

theorem literalSourceMatrix_row974 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨190, by decide⟩ : Fin 214)) = literalRow974 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 189
  · have hj : j = (⟨189, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow974]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨243, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 974 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk27.cell_d243_s0_row974_col189
  by_cases h1 : j.val = 190
  · have hj : j = (⟨190, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow974, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨243, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 974 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk27.cell_d243_s1_row974_col190
  · simp [literalRow974, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk47.row974_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row974

def literalRow976 (j : Fin 222) : M := if j.val = 189 then 1342177280 else if j.val = 190 then 1342177280 else if j.val = 191 then 1073741772 else if j.val = 192 then 1073741483 else if j.val = 193 then 536870913 else if j.val = 194 then 536870913 else if j.val = 197 then 1342177280 else if j.val = 198 then 1342177280 else 0

theorem literalSourceMatrix_row976 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨191, by decide⟩ : Fin 214)) = literalRow976 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 189
  · have hj : j = (⟨189, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow976]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨243, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 976 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk27.cell_d243_s0_row976_col189
  by_cases h1 : j.val = 190
  · have hj : j = (⟨190, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow976, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨243, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 976 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk27.cell_d243_s1_row976_col190
  by_cases h2 : j.val = 191
  · have hj : j = (⟨191, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow976, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨244, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 976 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk27.cell_d244_s0_row976_col191
  by_cases h3 : j.val = 192
  · have hj : j = (⟨192, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow976, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨244, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 976 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk27.cell_d244_s1_row976_col192
  by_cases h4 : j.val = 193
  · have hj : j = (⟨193, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow976, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨245, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 976 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk27.cell_d245_s0_row976_col193
  by_cases h5 : j.val = 194
  · have hj : j = (⟨194, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow976, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨245, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 976 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk27.cell_d245_s1_row976_col194
  by_cases h6 : j.val = 197
  · have hj : j = (⟨197, by decide⟩ : Fin 222) := Fin.ext h6
    subst j
    simp [literalRow976, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨247, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 976 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk27.cell_d247_s0_row976_col197
  by_cases h7 : j.val = 198
  · have hj : j = (⟨198, by decide⟩ : Fin 222) := Fin.ext h7
    subst j
    simp [literalRow976, h0, h1, h2, h3, h4, h5, h6]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨247, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 976 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk27.cell_d247_s1_row976_col198
  · simp [literalRow976, h0, h1, h2, h3, h4, h5, h6, h7]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk47.row976_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
    · exact h6 hbad
    · exact h7 hbad
#print axioms literalSourceMatrix_row976

def literalRow978 (j : Fin 222) : M := if j.val = 191 then 2147483612 else if j.val = 192 then 2147483409 else 0

theorem literalSourceMatrix_row978 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨192, by decide⟩ : Fin 214)) = literalRow978 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 191
  · have hj : j = (⟨191, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow978]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨244, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 978 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk27.cell_d244_s0_row978_col191
  by_cases h1 : j.val = 192
  · have hj : j = (⟨192, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow978, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨244, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 978 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk28.cell_d244_s1_row978_col192
  · simp [literalRow978, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk47.row978_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row978

end
end AspisV8R19.R804LiteralSourceRowsChunk47
