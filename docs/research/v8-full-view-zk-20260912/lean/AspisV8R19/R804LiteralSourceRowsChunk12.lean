import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R797ActiveSourceCellsChunk09
import AspisV8R19.R797ActiveSourceCellsChunk10
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk12
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk12
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow220 (j : Fin 222) : M := if j.val = 47 then 1073741826 else if j.val = 48 then 1073741826 else if j.val = 49 then 1073741772 else if j.val = 50 then 1073741483 else 0

theorem literalSourceMatrix_row220 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨49, by decide⟩ : Fin 214)) = literalRow220 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 47
  · have hj : j = (⟨47, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow220]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨54, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 220 = (1073741826 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk09.cell_d54_s0_row220_col47
  by_cases h1 : j.val = 48
  · have hj : j = (⟨48, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow220, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨54, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 220 = (1073741826 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk09.cell_d54_s1_row220_col48
  by_cases h2 : j.val = 49
  · have hj : j = (⟨49, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow220, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨55, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 220 = (1073741772 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk09.cell_d55_s0_row220_col49
  by_cases h3 : j.val = 50
  · have hj : j = (⟨50, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow220, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨55, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 220 = (1073741483 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk09.cell_d55_s1_row220_col50
  · simp [literalRow220, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk12.row220_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row220

def literalRow222 (j : Fin 222) : M := if j.val = 49 then 2147483612 else if j.val = 50 then 2147483409 else 0

theorem literalSourceMatrix_row222 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨50, by decide⟩ : Fin 214)) = literalRow222 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 49
  · have hj : j = (⟨49, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow222]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨55, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 222 = (2147483612 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk09.cell_d55_s0_row222_col49
  by_cases h1 : j.val = 50
  · have hj : j = (⟨50, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow222, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨55, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 222 = (2147483409 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk09.cell_d55_s1_row222_col50
  · simp [literalRow222, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk12.row222_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row222

def literalRow224 (j : Fin 222) : M := if j.val = 49 then 671088640 else if j.val = 50 then 671088640 else if j.val = 51 then 1073741772 else if j.val = 52 then 1073741483 else if j.val = 53 then 536870913 else if j.val = 54 then 536870913 else if j.val = 57 then 1342177280 else if j.val = 58 then 1342177280 else if j.val = 65 then 671088640 else 0

theorem literalSourceMatrix_row224 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨51, by decide⟩ : Fin 214)) = literalRow224 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 49
  · have hj : j = (⟨49, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow224]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨55, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 224 = (671088640 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk09.cell_d55_s0_row224_col49
  by_cases h1 : j.val = 50
  · have hj : j = (⟨50, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow224, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨55, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 224 = (671088640 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk09.cell_d55_s1_row224_col50
  by_cases h2 : j.val = 51
  · have hj : j = (⟨51, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow224, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨56, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 224 = (1073741772 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk09.cell_d56_s0_row224_col51
  by_cases h3 : j.val = 52
  · have hj : j = (⟨52, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow224, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨56, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 224 = (1073741483 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk09.cell_d56_s1_row224_col52
  by_cases h4 : j.val = 53
  · have hj : j = (⟨53, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow224, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨57, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 224 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk09.cell_d57_s0_row224_col53
  by_cases h5 : j.val = 54
  · have hj : j = (⟨54, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow224, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨57, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 224 = (536870913 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk09.cell_d57_s1_row224_col54
  by_cases h6 : j.val = 57
  · have hj : j = (⟨57, by decide⟩ : Fin 222) := Fin.ext h6
    subst j
    simp [literalRow224, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨59, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 224 = (1342177280 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk09.cell_d59_s0_row224_col57
  by_cases h7 : j.val = 58
  · have hj : j = (⟨58, by decide⟩ : Fin 222) := Fin.ext h7
    subst j
    simp [literalRow224, h0, h1, h2, h3, h4, h5, h6]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨59, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 224 = (1342177280 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk09.cell_d59_s1_row224_col58
  by_cases h8 : j.val = 65
  · have hj : j = (⟨65, by decide⟩ : Fin 222) := Fin.ext h8
    subst j
    simp [literalRow224, h0, h1, h2, h3, h4, h5, h6, h7]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨63, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 224 = (671088640 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk10.cell_d63_s0_row224_col65
  · simp [literalRow224, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk12.row224_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
    · exact h6 hbad
    · exact h7 hbad
    · exact h8 hbad
#print axioms literalSourceMatrix_row224

def literalRow226 (j : Fin 222) : M := if j.val = 51 then 2147483612 else if j.val = 52 then 2147483409 else 0

theorem literalSourceMatrix_row226 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨52, by decide⟩ : Fin 214)) = literalRow226 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 51
  · have hj : j = (⟨51, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow226]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨56, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 226 = (2147483612 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk10.cell_d56_s0_row226_col51
  by_cases h1 : j.val = 52
  · have hj : j = (⟨52, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow226, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨56, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 226 = (2147483409 : M)
    exact AspisV8R19.R797ActiveSourceCellsChunk10.cell_d56_s1_row226_col52
  · simp [literalRow226, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk12.row226_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row226

end
end AspisV8R19.R804LiteralSourceRowsChunk12
