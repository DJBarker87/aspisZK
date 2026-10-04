import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk02
import AspisV8R19.R799ActiveSourceCellsChunk03
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk15
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk15
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow245 (j : Fin 222) : M := if j.val = 60 then 1073741826 else if j.val = 61 then 42 else if j.val = 62 then 1073743541 else 0

theorem literalSourceMatrix_row245 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨61, by decide⟩ : Fin 214)) = literalRow245 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 60
  · have hj : j = (⟨60, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow245]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨60, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 245 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk02.cell_d60_s2_row245_col60
  by_cases h1 : j.val = 61
  · have hj : j = (⟨61, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow245, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨61, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 245 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk02.cell_d61_s0_row245_col61
  by_cases h2 : j.val = 62
  · have hj : j = (⟨62, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow245, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨61, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 245 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk02.cell_d61_s2_row245_col62
  · simp [literalRow245, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk15.row245_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row245

def literalRow247 (j : Fin 222) : M := if j.val = 61 then 5 else if j.val = 62 then 7 else 0

theorem literalSourceMatrix_row247 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨62, by decide⟩ : Fin 214)) = literalRow247 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 61
  · have hj : j = (⟨61, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow247]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨61, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 247 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk03.cell_d61_s0_row247_col61
  by_cases h1 : j.val = 62
  · have hj : j = (⟨62, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow247, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨61, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 247 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk03.cell_d61_s2_row247_col62
  · simp [literalRow247, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk15.row247_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row247

def literalRow249 (j : Fin 222) : M := if j.val = 62 then 536870913 else if j.val = 63 then 42 else if j.val = 64 then 1073743541 else 0

theorem literalSourceMatrix_row249 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨63, by decide⟩ : Fin 214)) = literalRow249 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 62
  · have hj : j = (⟨62, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow249]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨61, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 249 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk03.cell_d61_s2_row249_col62
  by_cases h1 : j.val = 63
  · have hj : j = (⟨63, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow249, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨62, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 249 = (42 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk03.cell_d62_s0_row249_col63
  by_cases h2 : j.val = 64
  · have hj : j = (⟨64, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow249, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨62, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 249 = (1073743541 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk03.cell_d62_s2_row249_col64
  · simp [literalRow249, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk15.row249_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row249

def literalRow251 (j : Fin 222) : M := if j.val = 63 then 5 else if j.val = 64 then 7 else 0

theorem literalSourceMatrix_row251 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨64, by decide⟩ : Fin 214)) = literalRow251 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 63
  · have hj : j = (⟨63, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow251]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨62, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 251 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk03.cell_d62_s0_row251_col63
  by_cases h1 : j.val = 64
  · have hj : j = (⟨64, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow251, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨62, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 251 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk03.cell_d62_s2_row251_col64
  · simp [literalRow251, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk15.row251_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row251

end
end AspisV8R19.R804LiteralSourceRowsChunk15
