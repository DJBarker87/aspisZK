import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R797ActiveSourceCellsChunk06
import AspisV8R19.R797ActiveSourceCellsChunk07
import AspisV8R19.R799ActiveSourceCellsChunk01
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk09
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk09
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow196 (j : Fin 222) : M := if j.val = 36 then 1073741826 else if j.val = 37 then 1073741772 else if j.val = 38 then 1073741483 else 0

theorem literalSourceMatrix_row196 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨37, by decide⟩ : Fin 214)) = literalRow196 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 36
  · have hj : j = (⟨36, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow196]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨48, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 196 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk01.cell_d48_s1_row196_col36
  by_cases h1 : j.val = 37
  · have hj : j = (⟨37, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow196, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨49, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 196 = (1073741772 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk06.cell_d49_s0_row196_col37
  by_cases h2 : j.val = 38
  · have hj : j = (⟨38, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow196, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨49, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 196 = (1073741483 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk06.cell_d49_s1_row196_col38
  · simp [literalRow196, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk09.row196_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row196

def literalRow198 (j : Fin 222) : M := if j.val = 37 then 2147483612 else if j.val = 38 then 2147483409 else 0

theorem literalSourceMatrix_row198 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨38, by decide⟩ : Fin 214)) = literalRow198 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 37
  · have hj : j = (⟨37, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow198]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨49, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 198 = (2147483612 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk06.cell_d49_s0_row198_col37
  by_cases h1 : j.val = 38
  · have hj : j = (⟨38, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow198, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨49, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 198 = (2147483409 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk06.cell_d49_s1_row198_col38
  · simp [literalRow198, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk09.row198_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row198

def literalRow200 (j : Fin 222) : M := if j.val = 37 then 536870913 else if j.val = 38 then 536870913 else if j.val = 39 then 1073741772 else if j.val = 40 then 1073741483 else if j.val = 41 then 536870913 else if j.val = 42 then 536870913 else 0

theorem literalSourceMatrix_row200 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨39, by decide⟩ : Fin 214)) = literalRow200 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 37
  · have hj : j = (⟨37, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow200]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨49, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 200 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk06.cell_d49_s0_row200_col37
  by_cases h1 : j.val = 38
  · have hj : j = (⟨38, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow200, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨49, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 200 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk06.cell_d49_s1_row200_col38
  by_cases h2 : j.val = 39
  · have hj : j = (⟨39, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow200, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨50, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 200 = (1073741772 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk06.cell_d50_s0_row200_col39
  by_cases h3 : j.val = 40
  · have hj : j = (⟨40, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow200, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨50, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 200 = (1073741483 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk06.cell_d50_s1_row200_col40
  by_cases h4 : j.val = 41
  · have hj : j = (⟨41, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow200, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨51, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 200 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk07.cell_d51_s0_row200_col41
  by_cases h5 : j.val = 42
  · have hj : j = (⟨42, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow200, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨51, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 200 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk07.cell_d51_s1_row200_col42
  · simp [literalRow200, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk09.row200_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
#print axioms literalSourceMatrix_row200

def literalRow202 (j : Fin 222) : M := if j.val = 39 then 2147483612 else if j.val = 40 then 2147483409 else 0

theorem literalSourceMatrix_row202 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨40, by decide⟩ : Fin 214)) = literalRow202 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 39
  · have hj : j = (⟨39, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow202]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨50, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 202 = (2147483612 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk07.cell_d50_s0_row202_col39
  by_cases h1 : j.val = 40
  · have hj : j = (⟨40, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow202, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨50, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 202 = (2147483409 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk07.cell_d50_s1_row202_col40
  · simp [literalRow202, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk09.row202_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row202

end
end AspisV8R19.R804LiteralSourceRowsChunk09
