import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk07
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk21
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk21
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow295 (j : Fin 222) : M := if j.val = 84 then 5 else if j.val = 85 then 7 else 0

theorem literalSourceMatrix_row295 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨85, by decide⟩ : Fin 214)) = literalRow295 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 84
  · have hj : j = (⟨84, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow295]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨73, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 295 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk07.cell_d73_s0_row295_col84
  by_cases h1 : j.val = 85
  · have hj : j = (⟨85, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow295, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 295 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk07.cell_d73_s2_row295_col85
  · simp [literalRow295, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk21.row295_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row295

def literalRow297 (j : Fin 222) : M := if j.val = 85 then 536870913 else if j.val = 86 then 42 else if j.val = 87 then 1073743541 else if j.val = 89 then 536870913 else 0

theorem literalSourceMatrix_row297 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨86, by decide⟩ : Fin 214)) = literalRow297 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 85
  · have hj : j = (⟨85, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow297]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨73, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 297 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk07.cell_d73_s2_row297_col85
  by_cases h1 : j.val = 86
  · have hj : j = (⟨86, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow297, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨74, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 297 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk07.cell_d74_s0_row297_col86
  by_cases h2 : j.val = 87
  · have hj : j = (⟨87, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow297, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨74, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 297 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk07.cell_d74_s2_row297_col87
  by_cases h3 : j.val = 89
  · have hj : j = (⟨89, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow297, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 297 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk07.cell_d75_s2_row297_col89
  · simp [literalRow297, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk21.row297_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row297

def literalRow299 (j : Fin 222) : M := if j.val = 86 then 5 else if j.val = 87 then 7 else 0

theorem literalSourceMatrix_row299 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨87, by decide⟩ : Fin 214)) = literalRow299 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 86
  · have hj : j = (⟨86, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow299]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨74, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 299 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk07.cell_d74_s0_row299_col86
  by_cases h1 : j.val = 87
  · have hj : j = (⟨87, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow299, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨74, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 299 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk07.cell_d74_s2_row299_col87
  · simp [literalRow299, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk21.row299_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row299

def literalRow301 (j : Fin 222) : M := if j.val = 87 then 1073741826 else if j.val = 88 then 42 else if j.val = 89 then 1073743541 else 0

theorem literalSourceMatrix_row301 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨88, by decide⟩ : Fin 214)) = literalRow301 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 87
  · have hj : j = (⟨87, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow301]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨74, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 301 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk07.cell_d74_s2_row301_col87
  by_cases h1 : j.val = 88
  · have hj : j = (⟨88, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow301, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨75, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 301 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk07.cell_d75_s0_row301_col88
  by_cases h2 : j.val = 89
  · have hj : j = (⟨89, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow301, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨75, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 301 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk07.cell_d75_s2_row301_col89
  · simp [literalRow301, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk21.row301_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row301

end
end AspisV8R19.R804LiteralSourceRowsChunk21
