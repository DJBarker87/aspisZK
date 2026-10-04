import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk28
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk48
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk48
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow980 (j : Fin 222) : M := if j.val = 191 then 1073741826 else if j.val = 192 then 1073741826 else if j.val = 193 then 1073741772 else if j.val = 194 then 1073741483 else 0

theorem literalSourceMatrix_row980 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨193, by decide⟩ : Fin 214)) = literalRow980 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 191
  · have hj : j = (⟨191, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow980]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨244, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 980 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk28.cell_d244_s0_row980_col191
  by_cases h1 : j.val = 192
  · have hj : j = (⟨192, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow980, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨244, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 980 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk28.cell_d244_s1_row980_col192
  by_cases h2 : j.val = 193
  · have hj : j = (⟨193, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow980, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨245, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 980 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk28.cell_d245_s0_row980_col193
  by_cases h3 : j.val = 194
  · have hj : j = (⟨194, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow980, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨245, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 980 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk28.cell_d245_s1_row980_col194
  · simp [literalRow980, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk48.row980_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row980

def literalRow982 (j : Fin 222) : M := if j.val = 193 then 2147483612 else if j.val = 194 then 2147483409 else 0

theorem literalSourceMatrix_row982 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨194, by decide⟩ : Fin 214)) = literalRow982 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 193
  · have hj : j = (⟨193, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow982]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨245, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 982 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk28.cell_d245_s0_row982_col193
  by_cases h1 : j.val = 194
  · have hj : j = (⟨194, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow982, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨245, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 982 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk28.cell_d245_s1_row982_col194
  · simp [literalRow982, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk48.row982_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row982

def literalRow984 (j : Fin 222) : M := if j.val = 193 then 536870913 else if j.val = 194 then 536870913 else if j.val = 195 then 1073741772 else if j.val = 196 then 1073741483 else if j.val = 197 then 536870913 else if j.val = 198 then 536870913 else 0

theorem literalSourceMatrix_row984 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨195, by decide⟩ : Fin 214)) = literalRow984 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 193
  · have hj : j = (⟨193, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow984]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨245, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 984 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk28.cell_d245_s0_row984_col193
  by_cases h1 : j.val = 194
  · have hj : j = (⟨194, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow984, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨245, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 984 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk28.cell_d245_s1_row984_col194
  by_cases h2 : j.val = 195
  · have hj : j = (⟨195, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow984, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨246, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 984 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk28.cell_d246_s0_row984_col195
  by_cases h3 : j.val = 196
  · have hj : j = (⟨196, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow984, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨246, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 984 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk28.cell_d246_s1_row984_col196
  by_cases h4 : j.val = 197
  · have hj : j = (⟨197, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow984, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨247, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 984 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk28.cell_d247_s0_row984_col197
  by_cases h5 : j.val = 198
  · have hj : j = (⟨198, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow984, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨247, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 984 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk28.cell_d247_s1_row984_col198
  · simp [literalRow984, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk48.row984_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
#print axioms literalSourceMatrix_row984

def literalRow986 (j : Fin 222) : M := if j.val = 195 then 2147483612 else if j.val = 196 then 2147483409 else 0

theorem literalSourceMatrix_row986 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨196, by decide⟩ : Fin 214)) = literalRow986 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 195
  · have hj : j = (⟨195, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow986]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨246, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 986 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk28.cell_d246_s0_row986_col195
  by_cases h1 : j.val = 196
  · have hj : j = (⟨196, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow986, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨246, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 986 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk28.cell_d246_s1_row986_col196
  · simp [literalRow986, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk48.row986_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row986

end
end AspisV8R19.R804LiteralSourceRowsChunk48
