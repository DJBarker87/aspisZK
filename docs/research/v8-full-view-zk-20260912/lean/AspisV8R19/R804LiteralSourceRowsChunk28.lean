import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk12
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk28
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk28
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow353 (j : Fin 222) : M := if j.val = 112 then 671088640 else if j.val = 113 then 42 else if j.val = 114 then 1073743541 else if j.val = 116 then 536870913 else if j.val = 119 then 1342177280 else 0

theorem literalSourceMatrix_row353 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨113, by decide⟩ : Fin 214)) = literalRow353 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 112
  · have hj : j = (⟨112, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow353]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨87, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 353 = (671088640 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk12.cell_d87_s2_row353_col112
  by_cases h1 : j.val = 113
  · have hj : j = (⟨113, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow353, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨88, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 353 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk12.cell_d88_s0_row353_col113
  by_cases h2 : j.val = 114
  · have hj : j = (⟨114, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow353, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨88, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 353 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk12.cell_d88_s2_row353_col114
  by_cases h3 : j.val = 116
  · have hj : j = (⟨116, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow353, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 353 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk12.cell_d89_s2_row353_col116
  by_cases h4 : j.val = 119
  · have hj : j = (⟨119, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow353, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨91, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 353 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk12.cell_d91_s2_row353_col119
  · simp [literalRow353, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk28.row353_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
#print axioms literalSourceMatrix_row353

def literalRow355 (j : Fin 222) : M := if j.val = 113 then 5 else if j.val = 114 then 7 else 0

theorem literalSourceMatrix_row355 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨114, by decide⟩ : Fin 214)) = literalRow355 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 113
  · have hj : j = (⟨113, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow355]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨88, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 355 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk12.cell_d88_s0_row355_col113
  by_cases h1 : j.val = 114
  · have hj : j = (⟨114, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow355, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨88, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 355 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk12.cell_d88_s2_row355_col114
  · simp [literalRow355, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk28.row355_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row355

def literalRow357 (j : Fin 222) : M := if j.val = 114 then 1073741826 else if j.val = 115 then 42 else if j.val = 116 then 1073743541 else 0

theorem literalSourceMatrix_row357 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨115, by decide⟩ : Fin 214)) = literalRow357 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 114
  · have hj : j = (⟨114, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow357]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨88, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 357 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk12.cell_d88_s2_row357_col114
  by_cases h1 : j.val = 115
  · have hj : j = (⟨115, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow357, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨89, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 357 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk12.cell_d89_s0_row357_col115
  by_cases h2 : j.val = 116
  · have hj : j = (⟨116, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow357, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 357 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk12.cell_d89_s2_row357_col116
  · simp [literalRow357, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk28.row357_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row357

def literalRow359 (j : Fin 222) : M := if j.val = 115 then 5 else if j.val = 116 then 7 else 0

theorem literalSourceMatrix_row359 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨116, by decide⟩ : Fin 214)) = literalRow359 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 115
  · have hj : j = (⟨115, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow359]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨89, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 359 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk12.cell_d89_s0_row359_col115
  by_cases h1 : j.val = 116
  · have hj : j = (⟨116, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow359, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨89, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 359 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk12.cell_d89_s2_row359_col116
  · simp [literalRow359, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk28.row359_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row359

end
end AspisV8R19.R804LiteralSourceRowsChunk28
