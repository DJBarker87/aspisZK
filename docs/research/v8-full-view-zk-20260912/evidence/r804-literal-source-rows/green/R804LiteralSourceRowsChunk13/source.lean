import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R797ActiveSourceCellsChunk10
import AspisV8R19.R799ActiveSourceCellsChunk01
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk13
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk13
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow228 (j : Fin 222) : M := if j.val = 51 then 1073741826 else if j.val = 52 then 1073741826 else if j.val = 53 then 1073741772 else if j.val = 54 then 1073741483 else 0

theorem literalSourceMatrix_row228 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨53, by decide⟩ : Fin 214)) = literalRow228 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 51
  · have hj : j = (⟨51, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow228]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨56, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 228 = (1073741826 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk10.cell_d56_s0_row228_col51
  by_cases h1 : j.val = 52
  · have hj : j = (⟨52, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow228, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨56, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 228 = (1073741826 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk10.cell_d56_s1_row228_col52
  by_cases h2 : j.val = 53
  · have hj : j = (⟨53, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow228, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨57, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 228 = (1073741772 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk10.cell_d57_s0_row228_col53
  by_cases h3 : j.val = 54
  · have hj : j = (⟨54, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow228, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨57, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 228 = (1073741483 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk10.cell_d57_s1_row228_col54
  · simp [literalRow228, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk13.row228_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row228

def literalRow230 (j : Fin 222) : M := if j.val = 53 then 2147483612 else if j.val = 54 then 2147483409 else 0

theorem literalSourceMatrix_row230 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨54, by decide⟩ : Fin 214)) = literalRow230 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 53
  · have hj : j = (⟨53, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow230]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨57, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 230 = (2147483612 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk10.cell_d57_s0_row230_col53
  by_cases h1 : j.val = 54
  · have hj : j = (⟨54, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow230, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨57, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 230 = (2147483409 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk10.cell_d57_s1_row230_col54
  · simp [literalRow230, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk13.row230_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row230

def literalRow232 (j : Fin 222) : M := if j.val = 53 then 536870913 else if j.val = 54 then 536870913 else if j.val = 55 then 1073741772 else if j.val = 56 then 1073741483 else if j.val = 57 then 536870913 else if j.val = 58 then 536870913 else 0

theorem literalSourceMatrix_row232 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨55, by decide⟩ : Fin 214)) = literalRow232 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 53
  · have hj : j = (⟨53, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow232]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨57, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 232 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk10.cell_d57_s0_row232_col53
  by_cases h1 : j.val = 54
  · have hj : j = (⟨54, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow232, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨57, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 232 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk10.cell_d57_s1_row232_col54
  by_cases h2 : j.val = 55
  · have hj : j = (⟨55, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow232, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨58, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 232 = (1073741772 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk10.cell_d58_s0_row232_col55
  by_cases h3 : j.val = 56
  · have hj : j = (⟨56, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow232, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨58, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 232 = (1073741483 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk10.cell_d58_s1_row232_col56
  by_cases h4 : j.val = 57
  · have hj : j = (⟨57, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow232, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨59, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 232 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk10.cell_d59_s0_row232_col57
  by_cases h5 : j.val = 58
  · have hj : j = (⟨58, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow232, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨59, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 232 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk10.cell_d59_s1_row232_col58
  · simp [literalRow232, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk13.row232_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
#print axioms literalSourceMatrix_row232

def literalRow234 (j : Fin 222) : M := if j.val = 55 then 2147483612 else if j.val = 56 then 2147483409 else 0

theorem literalSourceMatrix_row234 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨56, by decide⟩ : Fin 214)) = literalRow234 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 55
  · have hj : j = (⟨55, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow234]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨58, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 234 = (2147483612 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk10.cell_d58_s0_row234_col55
  by_cases h1 : j.val = 56
  · have hj : j = (⟨56, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow234, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨58, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 234 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk01.cell_d58_s1_row234_col56
  · simp [literalRow234, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk13.row234_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row234

end
end AspisV8R19.R804LiteralSourceRowsChunk13
