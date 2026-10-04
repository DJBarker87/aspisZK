import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R797ActiveSourceCellsChunk00
import AspisV8R19.R797ActiveSourceCellsChunk01
import AspisV8R19.R799ActiveSourceCellsChunk00
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk01
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk01
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow124 (j : Fin 222) : M := if j.val = 3 then 1073741826 else if j.val = 4 then 1073741826 else if j.val = 5 then 1073741772 else if j.val = 6 then 1073741483 else 0

theorem literalSourceMatrix_row124 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨5, by decide⟩ : Fin 214)) = literalRow124 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 3
  · have hj : j = (⟨3, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow124]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨30, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 124 = (1073741826 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk00.cell_d30_s0_row124_col3
  by_cases h1 : j.val = 4
  · have hj : j = (⟨4, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow124, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨30, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 124 = (1073741826 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk00.cell_d30_s1_row124_col4
  by_cases h2 : j.val = 5
  · have hj : j = (⟨5, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow124, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨31, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 124 = (1073741772 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk00.cell_d31_s0_row124_col5
  by_cases h3 : j.val = 6
  · have hj : j = (⟨6, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow124, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨31, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 124 = (1073741483 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk00.cell_d31_s1_row124_col6
  · simp [literalRow124, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk01.row124_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row124

def literalRow126 (j : Fin 222) : M := if j.val = 5 then 2147483612 else if j.val = 6 then 2147483409 else 0

theorem literalSourceMatrix_row126 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨6, by decide⟩ : Fin 214)) = literalRow126 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 5
  · have hj : j = (⟨5, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow126]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨31, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 126 = (2147483612 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk01.cell_d31_s0_row126_col5
  by_cases h1 : j.val = 6
  · have hj : j = (⟨6, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow126, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨31, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 126 = (2147483409 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk01.cell_d31_s1_row126_col6
  · simp [literalRow126, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk01.row126_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row126

def literalRow128 (j : Fin 222) : M := if j.val = 5 then 167772160 else if j.val = 6 then 167772160 else if j.val = 7 then 1073741772 else if j.val = 8 then 1073741483 else if j.val = 9 then 536870913 else if j.val = 10 then 536870913 else if j.val = 13 then 1342177280 else if j.val = 14 then 1342177280 else if j.val = 21 then 671088640 else if j.val = 22 then 671088640 else if j.val = 35 then 335544320 else if j.val = 65 then 167772160 else 0

theorem literalSourceMatrix_row128 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨7, by decide⟩ : Fin 214)) = literalRow128 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 5
  · have hj : j = (⟨5, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow128]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨31, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 128 = (167772160 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk01.cell_d31_s0_row128_col5
  by_cases h1 : j.val = 6
  · have hj : j = (⟨6, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow128, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨31, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 128 = (167772160 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk01.cell_d31_s1_row128_col6
  by_cases h2 : j.val = 7
  · have hj : j = (⟨7, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow128, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨32, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 128 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk00.cell_d32_s0_row128_col7
  by_cases h3 : j.val = 8
  · have hj : j = (⟨8, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow128, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨32, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 128 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk00.cell_d32_s1_row128_col8
  by_cases h4 : j.val = 9
  · have hj : j = (⟨9, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow128, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨33, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 128 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk01.cell_d33_s0_row128_col9
  by_cases h5 : j.val = 10
  · have hj : j = (⟨10, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow128, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨33, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 128 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk01.cell_d33_s1_row128_col10
  by_cases h6 : j.val = 13
  · have hj : j = (⟨13, by decide⟩ : Fin 222) := Fin.ext h6
    subst j
    simp [literalRow128, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨35, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 128 = (1342177280 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk01.cell_d35_s0_row128_col13
  by_cases h7 : j.val = 14
  · have hj : j = (⟨14, by decide⟩ : Fin 222) := Fin.ext h7
    subst j
    simp [literalRow128, h0, h1, h2, h3, h4, h5, h6]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨35, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 128 = (1342177280 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk01.cell_d35_s1_row128_col14
  by_cases h8 : j.val = 21
  · have hj : j = (⟨21, by decide⟩ : Fin 222) := Fin.ext h8
    subst j
    simp [literalRow128, h0, h1, h2, h3, h4, h5, h6, h7]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨39, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 128 = (671088640 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk01.cell_d39_s0_row128_col21
  by_cases h9 : j.val = 22
  · have hj : j = (⟨22, by decide⟩ : Fin 222) := Fin.ext h9
    subst j
    simp [literalRow128, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨39, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 128 = (671088640 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk01.cell_d39_s1_row128_col22
  by_cases h10 : j.val = 35
  · have hj : j = (⟨35, by decide⟩ : Fin 222) := Fin.ext h10
    subst j
    simp [literalRow128, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨47, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 128 = (335544320 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk00.cell_d47_s1_row128_col35
  by_cases h11 : j.val = 65
  · have hj : j = (⟨65, by decide⟩ : Fin 222) := Fin.ext h11
    subst j
    simp [literalRow128, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨63, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 128 = (167772160 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk01.cell_d63_s0_row128_col65
  · simp [literalRow128, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk01.row128_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad | hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
    · exact h6 hbad
    · exact h7 hbad
    · exact h8 hbad
    · exact h9 hbad
    · exact h10 hbad
    · exact h11 hbad
#print axioms literalSourceMatrix_row128

def literalRow130 (j : Fin 222) : M := if j.val = 7 then 2147483612 else if j.val = 8 then 2147483409 else if j.val = 221 then 335544320 else 0

theorem literalSourceMatrix_row130 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨8, by decide⟩ : Fin 214)) = literalRow130 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 7
  · have hj : j = (⟨7, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow130]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨32, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 130 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk00.cell_d32_s0_row130_col7
  by_cases h1 : j.val = 8
  · have hj : j = (⟨8, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow130, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨32, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 130 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk00.cell_d32_s1_row130_col8
  by_cases h2 : j.val = 221
  · have hj : j = (⟨221, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow130, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨47, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 130 = (335544320 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk00.cell_d47_s2_row130_col221
  · simp [literalRow130, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk01.row130_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row130

end
end AspisV8R19.R804LiteralSourceRowsChunk01
