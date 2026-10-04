import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R797ActiveSourceCellsChunk07
import AspisV8R19.R797ActiveSourceCellsChunk08
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk10
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk10
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow204 (j : Fin 222) : M := if j.val = 39 then 1073741826 else if j.val = 40 then 1073741826 else if j.val = 41 then 1073741772 else if j.val = 42 then 1073741483 else 0

theorem literalSourceMatrix_row204 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨41, by decide⟩ : Fin 214)) = literalRow204 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 39
  · have hj : j = (⟨39, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow204]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨50, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 204 = (1073741826 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk07.cell_d50_s0_row204_col39
  by_cases h1 : j.val = 40
  · have hj : j = (⟨40, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow204, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨50, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 204 = (1073741826 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk07.cell_d50_s1_row204_col40
  by_cases h2 : j.val = 41
  · have hj : j = (⟨41, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow204, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨51, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 204 = (1073741772 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk07.cell_d51_s0_row204_col41
  by_cases h3 : j.val = 42
  · have hj : j = (⟨42, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow204, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨51, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 204 = (1073741483 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk07.cell_d51_s1_row204_col42
  · simp [literalRow204, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk10.row204_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row204

def literalRow206 (j : Fin 222) : M := if j.val = 41 then 2147483612 else if j.val = 42 then 2147483409 else 0

theorem literalSourceMatrix_row206 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨42, by decide⟩ : Fin 214)) = literalRow206 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 41
  · have hj : j = (⟨41, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow206]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨51, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 206 = (2147483612 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk07.cell_d51_s0_row206_col41
  by_cases h1 : j.val = 42
  · have hj : j = (⟨42, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow206, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨51, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 206 = (2147483409 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk07.cell_d51_s1_row206_col42
  · simp [literalRow206, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk10.row206_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row206

def literalRow208 (j : Fin 222) : M := if j.val = 41 then 1342177280 else if j.val = 42 then 1342177280 else if j.val = 43 then 1073741772 else if j.val = 44 then 1073741483 else if j.val = 45 then 536870913 else if j.val = 46 then 536870913 else if j.val = 49 then 1342177280 else if j.val = 50 then 1342177280 else 0

theorem literalSourceMatrix_row208 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨43, by decide⟩ : Fin 214)) = literalRow208 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 41
  · have hj : j = (⟨41, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow208]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨51, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 208 = (1342177280 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk07.cell_d51_s0_row208_col41
  by_cases h1 : j.val = 42
  · have hj : j = (⟨42, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow208, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨51, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 208 = (1342177280 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk07.cell_d51_s1_row208_col42
  by_cases h2 : j.val = 43
  · have hj : j = (⟨43, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow208, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨52, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 208 = (1073741772 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk07.cell_d52_s0_row208_col43
  by_cases h3 : j.val = 44
  · have hj : j = (⟨44, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow208, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨52, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 208 = (1073741483 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk07.cell_d52_s1_row208_col44
  by_cases h4 : j.val = 45
  · have hj : j = (⟨45, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow208, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨53, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 208 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk07.cell_d53_s0_row208_col45
  by_cases h5 : j.val = 46
  · have hj : j = (⟨46, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow208, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨53, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 208 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk07.cell_d53_s1_row208_col46
  by_cases h6 : j.val = 49
  · have hj : j = (⟨49, by decide⟩ : Fin 222) := Fin.ext h6
    subst j
    simp [literalRow208, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨55, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 208 = (1342177280 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk08.cell_d55_s0_row208_col49
  by_cases h7 : j.val = 50
  · have hj : j = (⟨50, by decide⟩ : Fin 222) := Fin.ext h7
    subst j
    simp [literalRow208, h0, h1, h2, h3, h4, h5, h6]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨55, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 208 = (1342177280 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk08.cell_d55_s1_row208_col50
  · simp [literalRow208, h0, h1, h2, h3, h4, h5, h6, h7]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk10.row208_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
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
#print axioms literalSourceMatrix_row208

def literalRow210 (j : Fin 222) : M := if j.val = 43 then 2147483612 else if j.val = 44 then 2147483409 else 0

theorem literalSourceMatrix_row210 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨44, by decide⟩ : Fin 214)) = literalRow210 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 43
  · have hj : j = (⟨43, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow210]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨52, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 210 = (2147483612 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk08.cell_d52_s0_row210_col43
  by_cases h1 : j.val = 44
  · have hj : j = (⟨44, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow210, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨52, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 210 = (2147483409 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk08.cell_d52_s1_row210_col44
  · simp [literalRow210, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk10.row210_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row210

end
end AspisV8R19.R804LiteralSourceRowsChunk10
