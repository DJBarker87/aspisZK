import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk30
import AspisV8R19.R799ActiveSourceCellsChunk31
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk51
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk51
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow1004 (j : Fin 222) : M := if j.val = 203 then 1073741826 else if j.val = 204 then 1073741826 else if j.val = 205 then 1073741772 else if j.val = 206 then 1073741483 else 0

theorem literalSourceMatrix_row1004 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨205, by decide⟩ : Fin 214)) = literalRow1004 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 203
  · have hj : j = (⟨203, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow1004]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨250, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1004 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk30.cell_d250_s0_row1004_col203
  by_cases h1 : j.val = 204
  · have hj : j = (⟨204, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow1004, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨250, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1004 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk30.cell_d250_s1_row1004_col204
  by_cases h2 : j.val = 205
  · have hj : j = (⟨205, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow1004, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨251, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1004 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk30.cell_d251_s0_row1004_col205
  by_cases h3 : j.val = 206
  · have hj : j = (⟨206, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow1004, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨251, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1004 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk31.cell_d251_s1_row1004_col206
  · simp [literalRow1004, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk51.row1004_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row1004

def literalRow1006 (j : Fin 222) : M := if j.val = 205 then 2147483612 else if j.val = 206 then 2147483409 else 0

theorem literalSourceMatrix_row1006 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨206, by decide⟩ : Fin 214)) = literalRow1006 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 205
  · have hj : j = (⟨205, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow1006]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨251, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1006 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk31.cell_d251_s0_row1006_col205
  by_cases h1 : j.val = 206
  · have hj : j = (⟨206, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow1006, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨251, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1006 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk31.cell_d251_s1_row1006_col206
  · simp [literalRow1006, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk51.row1006_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row1006

def literalRow1008 (j : Fin 222) : M := if j.val = 205 then 1342177280 else if j.val = 206 then 1342177280 else if j.val = 207 then 1073741772 else if j.val = 208 then 2147481246 else if j.val = 209 then 536870913 else 0

theorem literalSourceMatrix_row1008 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨207, by decide⟩ : Fin 214)) = literalRow1008 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 205
  · have hj : j = (⟨205, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow1008]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨251, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1008 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk31.cell_d251_s0_row1008_col205
  by_cases h1 : j.val = 206
  · have hj : j = (⟨206, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow1008, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨251, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1008 = (1342177280 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk31.cell_d251_s1_row1008_col206
  by_cases h2 : j.val = 207
  · have hj : j = (⟨207, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow1008, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨252, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1008 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk31.cell_d252_s0_row1008_col207
  by_cases h3 : j.val = 208
  · have hj : j = (⟨208, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow1008, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨252, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1008 = (2147481246 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk31.cell_d252_s2_row1008_col208
  by_cases h4 : j.val = 209
  · have hj : j = (⟨209, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow1008, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨253, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1008 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk31.cell_d253_s0_row1008_col209
  · simp [literalRow1008, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk51.row1008_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
#print axioms literalSourceMatrix_row1008

def literalRow1011 (j : Fin 222) : M := if j.val = 207 then 5 else if j.val = 208 then 7 else 0

theorem literalSourceMatrix_row1011 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨208, by decide⟩ : Fin 214)) = literalRow1011 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 207
  · have hj : j = (⟨207, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow1011]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨252, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1011 = (5 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk31.cell_d252_s0_row1011_col207
  by_cases h1 : j.val = 208
  · have hj : j = (⟨208, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow1011, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨252, by decide⟩) (⟨2, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1011 = (7 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk31.cell_d252_s2_row1011_col208
  · simp [literalRow1011, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk51.row1011_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row1011

end
end AspisV8R19.R804LiteralSourceRowsChunk51
