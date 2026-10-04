import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk22
import AspisV8R19.R799ActiveSourceCellsChunk23
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk42
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk42
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow926 (j : Fin 222) : M := if j.val = 168 then 2147483612 else if j.val = 169 then 2147483409 else 0

theorem literalSourceMatrix_row926 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨169, by decide⟩ : Fin 214)) = literalRow926 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 168
  · have hj : j = (⟨168, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow926]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨231, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 926 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk22.cell_d231_s0_row926_col168
  by_cases h1 : j.val = 169
  · have hj : j = (⟨169, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow926, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨231, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 926 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk22.cell_d231_s1_row926_col169
  · simp [literalRow926, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk42.row926_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row926

def literalRow928 (j : Fin 222) : M := if j.val = 168 then 671088640 else if j.val = 169 then 671088640 else if j.val = 170 then 1073741772 else if j.val = 171 then 1073741483 else if j.val = 172 then 536870913 else if j.val = 173 then 536870913 else if j.val = 176 then 1342177280 else if j.val = 177 then 1342177280 else if j.val = 182 then 671088640 else 0

theorem literalSourceMatrix_row928 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨170, by decide⟩ : Fin 214)) = literalRow928 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 168
  · have hj : j = (⟨168, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow928]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨231, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 928 = (671088640 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk22.cell_d231_s0_row928_col168
  by_cases h1 : j.val = 169
  · have hj : j = (⟨169, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow928, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨231, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 928 = (671088640 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk22.cell_d231_s1_row928_col169
  by_cases h2 : j.val = 170
  · have hj : j = (⟨170, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow928, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨232, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 928 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk22.cell_d232_s0_row928_col170
  by_cases h3 : j.val = 171
  · have hj : j = (⟨171, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow928, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨232, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 928 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk22.cell_d232_s1_row928_col171
  by_cases h4 : j.val = 172
  · have hj : j = (⟨172, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow928, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨233, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 928 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk22.cell_d233_s0_row928_col172
  by_cases h5 : j.val = 173
  · have hj : j = (⟨173, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow928, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨233, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 928 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk23.cell_d233_s1_row928_col173
  by_cases h6 : j.val = 176
  · have hj : j = (⟨176, by decide⟩ : Fin 222) := Fin.ext h6
    subst j
    simp [literalRow928, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨235, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 928 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk23.cell_d235_s0_row928_col176
  by_cases h7 : j.val = 177
  · have hj : j = (⟨177, by decide⟩ : Fin 222) := Fin.ext h7
    subst j
    simp [literalRow928, h0, h1, h2, h3, h4, h5, h6]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨235, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 928 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk23.cell_d235_s1_row928_col177
  by_cases h8 : j.val = 182
  · have hj : j = (⟨182, by decide⟩ : Fin 222) := Fin.ext h8
    subst j
    simp [literalRow928, h0, h1, h2, h3, h4, h5, h6, h7]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨239, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 928 = (671088640 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk23.cell_d239_s1_row928_col182
  · simp [literalRow928, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk42.row928_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
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
#print axioms literalSourceMatrix_row928

def literalRow930 (j : Fin 222) : M := if j.val = 170 then 2147483612 else if j.val = 171 then 2147483409 else 0

theorem literalSourceMatrix_row930 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨171, by decide⟩ : Fin 214)) = literalRow930 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 170
  · have hj : j = (⟨170, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow930]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨232, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 930 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk23.cell_d232_s0_row930_col170
  by_cases h1 : j.val = 171
  · have hj : j = (⟨171, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow930, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨232, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 930 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk23.cell_d232_s1_row930_col171
  · simp [literalRow930, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk42.row930_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row930

def literalRow932 (j : Fin 222) : M := if j.val = 170 then 1073741826 else if j.val = 171 then 1073741826 else if j.val = 172 then 1073741772 else if j.val = 173 then 1073741483 else 0

theorem literalSourceMatrix_row932 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨172, by decide⟩ : Fin 214)) = literalRow932 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 170
  · have hj : j = (⟨170, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow932]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨232, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 932 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk23.cell_d232_s0_row932_col170
  by_cases h1 : j.val = 171
  · have hj : j = (⟨171, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow932, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨232, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 932 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk23.cell_d232_s1_row932_col171
  by_cases h2 : j.val = 172
  · have hj : j = (⟨172, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow932, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨233, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 932 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk23.cell_d233_s0_row932_col172
  by_cases h3 : j.val = 173
  · have hj : j = (⟨173, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow932, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨233, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 932 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk23.cell_d233_s1_row932_col173
  · simp [literalRow932, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk42.row932_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row932

end
end AspisV8R19.R804LiteralSourceRowsChunk42
