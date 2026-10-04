import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk25
import AspisV8R19.R799ActiveSourceCellsChunk26
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk45
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk45
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow954 (j : Fin 222) : M := if j.val = 180 then 2147483612 else if j.val = 181 then 2147483409 else 0

theorem literalSourceMatrix_row954 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨181, by decide⟩ : Fin 214)) = literalRow954 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 180
  · have hj : j = (⟨180, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow954]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨238, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 954 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk25.cell_d238_s0_row954_col180
  by_cases h1 : j.val = 181
  · have hj : j = (⟨181, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow954, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨238, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 954 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk25.cell_d238_s1_row954_col181
  · simp [literalRow954, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk45.row954_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row954

def literalRow958 (j : Fin 222) : M := if j.val = 182 then 2147483409 else 0

theorem literalSourceMatrix_row958 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨182, by decide⟩ : Fin 214)) = literalRow958 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 182
  · have hj : j = (⟨182, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow958]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨239, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 958 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk25.cell_d239_s1_row958_col182
  · simp [literalRow958, h0]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk45.row958_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    exact h0 hm
#print axioms literalSourceMatrix_row958

def literalRow960 (j : Fin 222) : M := if j.val = 182 then 335544320 else if j.val = 183 then 1073741772 else if j.val = 184 then 1073741483 else if j.val = 185 then 536870913 else if j.val = 186 then 536870913 else if j.val = 189 then 1342177280 else if j.val = 190 then 1342177280 else if j.val = 197 then 671088640 else if j.val = 198 then 671088640 else 0

theorem literalSourceMatrix_row960 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨183, by decide⟩ : Fin 214)) = literalRow960 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 182
  · have hj : j = (⟨182, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow960]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨239, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 960 = (335544320 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk25.cell_d239_s1_row960_col182
  by_cases h1 : j.val = 183
  · have hj : j = (⟨183, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow960, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨240, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 960 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk25.cell_d240_s0_row960_col183
  by_cases h2 : j.val = 184
  · have hj : j = (⟨184, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow960, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨240, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 960 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk25.cell_d240_s1_row960_col184
  by_cases h3 : j.val = 185
  · have hj : j = (⟨185, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow960, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨241, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 960 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk25.cell_d241_s0_row960_col185
  by_cases h4 : j.val = 186
  · have hj : j = (⟨186, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow960, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨241, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 960 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk25.cell_d241_s1_row960_col186
  by_cases h5 : j.val = 189
  · have hj : j = (⟨189, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow960, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨243, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 960 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk25.cell_d243_s0_row960_col189
  by_cases h6 : j.val = 190
  · have hj : j = (⟨190, by decide⟩ : Fin 222) := Fin.ext h6
    subst j
    simp [literalRow960, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨243, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 960 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk25.cell_d243_s1_row960_col190
  by_cases h7 : j.val = 197
  · have hj : j = (⟨197, by decide⟩ : Fin 222) := Fin.ext h7
    subst j
    simp [literalRow960, h0, h1, h2, h3, h4, h5, h6]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨247, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 960 = (671088640 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk25.cell_d247_s0_row960_col197
  by_cases h8 : j.val = 198
  · have hj : j = (⟨198, by decide⟩ : Fin 222) := Fin.ext h8
    subst j
    simp [literalRow960, h0, h1, h2, h3, h4, h5, h6, h7]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨247, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 960 = (671088640 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk26.cell_d247_s1_row960_col198
  · simp [literalRow960, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk45.row960_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
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
#print axioms literalSourceMatrix_row960

def literalRow962 (j : Fin 222) : M := if j.val = 183 then 2147483612 else if j.val = 184 then 2147483409 else 0

theorem literalSourceMatrix_row962 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨184, by decide⟩ : Fin 214)) = literalRow962 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 183
  · have hj : j = (⟨183, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow962]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨240, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 962 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk26.cell_d240_s0_row962_col183
  by_cases h1 : j.val = 184
  · have hj : j = (⟨184, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow962, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨240, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 962 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk26.cell_d240_s1_row962_col184
  · simp [literalRow962, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk45.row962_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row962

end
end AspisV8R19.R804LiteralSourceRowsChunk45
