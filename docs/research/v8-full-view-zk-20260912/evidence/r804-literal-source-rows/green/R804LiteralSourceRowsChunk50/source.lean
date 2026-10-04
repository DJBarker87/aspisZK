import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk29
import AspisV8R19.R799ActiveSourceCellsChunk30
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk50
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk50
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow996 (j : Fin 222) : M := if j.val = 199 then 1073741826 else if j.val = 200 then 1073741826 else if j.val = 201 then 1073741772 else if j.val = 202 then 1073741483 else 0

theorem literalSourceMatrix_row996 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨201, by decide⟩ : Fin 214)) = literalRow996 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 199
  · have hj : j = (⟨199, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow996]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨248, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 996 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk29.cell_d248_s0_row996_col199
  by_cases h1 : j.val = 200
  · have hj : j = (⟨200, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow996, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨248, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 996 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk30.cell_d248_s1_row996_col200
  by_cases h2 : j.val = 201
  · have hj : j = (⟨201, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow996, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨249, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 996 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk30.cell_d249_s0_row996_col201
  by_cases h3 : j.val = 202
  · have hj : j = (⟨202, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow996, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨249, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 996 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk30.cell_d249_s1_row996_col202
  · simp [literalRow996, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk50.row996_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row996

def literalRow998 (j : Fin 222) : M := if j.val = 201 then 2147483612 else if j.val = 202 then 2147483409 else 0

theorem literalSourceMatrix_row998 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨202, by decide⟩ : Fin 214)) = literalRow998 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 201
  · have hj : j = (⟨201, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow998]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨249, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 998 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk30.cell_d249_s0_row998_col201
  by_cases h1 : j.val = 202
  · have hj : j = (⟨202, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow998, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨249, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 998 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk30.cell_d249_s1_row998_col202
  · simp [literalRow998, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk50.row998_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row998

def literalRow1000 (j : Fin 222) : M := if j.val = 201 then 536870913 else if j.val = 202 then 536870913 else if j.val = 203 then 1073741772 else if j.val = 204 then 1073741483 else if j.val = 205 then 536870913 else if j.val = 206 then 536870913 else 0

theorem literalSourceMatrix_row1000 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨203, by decide⟩ : Fin 214)) = literalRow1000 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 201
  · have hj : j = (⟨201, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow1000]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨249, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1000 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk30.cell_d249_s0_row1000_col201
  by_cases h1 : j.val = 202
  · have hj : j = (⟨202, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow1000, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨249, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1000 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk30.cell_d249_s1_row1000_col202
  by_cases h2 : j.val = 203
  · have hj : j = (⟨203, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow1000, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨250, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1000 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk30.cell_d250_s0_row1000_col203
  by_cases h3 : j.val = 204
  · have hj : j = (⟨204, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow1000, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨250, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1000 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk30.cell_d250_s1_row1000_col204
  by_cases h4 : j.val = 205
  · have hj : j = (⟨205, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow1000, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨251, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1000 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk30.cell_d251_s0_row1000_col205
  by_cases h5 : j.val = 206
  · have hj : j = (⟨206, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow1000, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨251, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1000 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk30.cell_d251_s1_row1000_col206
  · simp [literalRow1000, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk50.row1000_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
#print axioms literalSourceMatrix_row1000

def literalRow1002 (j : Fin 222) : M := if j.val = 203 then 2147483612 else if j.val = 204 then 2147483409 else 0

theorem literalSourceMatrix_row1002 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨204, by decide⟩ : Fin 214)) = literalRow1002 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 203
  · have hj : j = (⟨203, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow1002]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨250, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1002 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk30.cell_d250_s0_row1002_col203
  by_cases h1 : j.val = 204
  · have hj : j = (⟨204, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow1002, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨250, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 1002 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk30.cell_d250_s1_row1002_col204
  · simp [literalRow1002, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk50.row1002_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row1002

end
end AspisV8R19.R804LiteralSourceRowsChunk50
