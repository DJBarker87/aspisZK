import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk07
import AspisV8R19.R799ActiveSourceCellsChunk08
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk22
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk22
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow303 (j : Fin 222) : M := if j.val = 88 then 5 else if j.val = 89 then 7 else 0

theorem literalSourceMatrix_row303 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨89, by decide⟩ : Fin 214)) = literalRow303 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 88
  · have hj : j = (⟨88, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow303]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨75, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 303 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk07.cell_d75_s0_row303_col88
  by_cases h1 : j.val = 89
  · have hj : j = (⟨89, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow303, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 303 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk07.cell_d75_s2_row303_col89
  · simp [literalRow303, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk22.row303_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row303

def literalRow305 (j : Fin 222) : M := if j.val = 89 then 1342177280 else if j.val = 90 then 42 else if j.val = 91 then 1073743541 else if j.val = 92 then 536870913 else if j.val = 96 then 1342177280 else 0

theorem literalSourceMatrix_row305 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨90, by decide⟩ : Fin 214)) = literalRow305 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 89
  · have hj : j = (⟨89, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow305]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 305 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk08.cell_d75_s2_row305_col89
  by_cases h1 : j.val = 90
  · have hj : j = (⟨90, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow305, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨76, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 305 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk08.cell_d76_s0_row305_col90
  by_cases h2 : j.val = 91
  · have hj : j = (⟨91, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow305, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨76, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 305 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk08.cell_d76_s2_row305_col91
  by_cases h3 : j.val = 92
  · have hj : j = (⟨92, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow305, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨77, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 305 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk08.cell_d77_s2_row305_col92
  by_cases h4 : j.val = 96
  · have hj : j = (⟨96, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow305, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨79, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 305 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk08.cell_d79_s2_row305_col96
  · simp [literalRow305, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk22.row305_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
#print axioms literalSourceMatrix_row305

def literalRow307 (j : Fin 222) : M := if j.val = 90 then 5 else if j.val = 91 then 7 else 0

theorem literalSourceMatrix_row307 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨91, by decide⟩ : Fin 214)) = literalRow307 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 90
  · have hj : j = (⟨90, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow307]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨76, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 307 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk08.cell_d76_s0_row307_col90
  by_cases h1 : j.val = 91
  · have hj : j = (⟨91, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow307, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨76, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 307 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk08.cell_d76_s2_row307_col91
  · simp [literalRow307, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk22.row307_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row307

def literalRow311 (j : Fin 222) : M := if j.val = 92 then 7 else 0

theorem literalSourceMatrix_row311 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨92, by decide⟩ : Fin 214)) = literalRow311 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 92
  · have hj : j = (⟨92, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow311]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨77, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 311 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk08.cell_d77_s2_row311_col92
  · simp [literalRow311, h0]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk22.row311_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    exact h0 hm
#print axioms literalSourceMatrix_row311

end
end AspisV8R19.R804LiteralSourceRowsChunk22
