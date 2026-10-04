import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk13
import AspisV8R19.R799ActiveSourceCellsChunk14
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk30
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk30
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow372 (j : Fin 222) : M := if j.val = 120 then 1073741826 else if j.val = 121 then 1073741772 else if j.val = 122 then 1073741483 else 0

theorem literalSourceMatrix_row372 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨121, by decide⟩ : Fin 214)) = literalRow372 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 120
  · have hj : j = (⟨120, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow372]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨92, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 372 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk13.cell_d92_s1_row372_col120
  by_cases h1 : j.val = 121
  · have hj : j = (⟨121, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow372, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨93, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 372 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk13.cell_d93_s0_row372_col121
  by_cases h2 : j.val = 122
  · have hj : j = (⟨122, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow372, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨93, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 372 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk13.cell_d93_s1_row372_col122
  · simp [literalRow372, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk30.row372_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row372

def literalRow374 (j : Fin 222) : M := if j.val = 121 then 2147483612 else if j.val = 122 then 2147483409 else 0

theorem literalSourceMatrix_row374 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨122, by decide⟩ : Fin 214)) = literalRow374 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 121
  · have hj : j = (⟨121, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow374]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨93, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 374 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk13.cell_d93_s0_row374_col121
  by_cases h1 : j.val = 122
  · have hj : j = (⟨122, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow374, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨93, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 374 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk13.cell_d93_s1_row374_col122
  · simp [literalRow374, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk30.row374_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row374

def literalRow376 (j : Fin 222) : M := if j.val = 121 then 536870913 else if j.val = 122 then 536870913 else if j.val = 123 then 1073741772 else if j.val = 124 then 1073741483 else if j.val = 125 then 536870913 else if j.val = 126 then 536870913 else 0

theorem literalSourceMatrix_row376 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨123, by decide⟩ : Fin 214)) = literalRow376 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 121
  · have hj : j = (⟨121, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow376]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨93, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 376 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk13.cell_d93_s0_row376_col121
  by_cases h1 : j.val = 122
  · have hj : j = (⟨122, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow376, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨93, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 376 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk13.cell_d93_s1_row376_col122
  by_cases h2 : j.val = 123
  · have hj : j = (⟨123, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow376, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨94, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 376 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk13.cell_d94_s0_row376_col123
  by_cases h3 : j.val = 124
  · have hj : j = (⟨124, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow376, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨94, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 376 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk13.cell_d94_s1_row376_col124
  by_cases h4 : j.val = 125
  · have hj : j = (⟨125, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow376, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨95, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 376 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk14.cell_d95_s0_row376_col125
  by_cases h5 : j.val = 126
  · have hj : j = (⟨126, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow376, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨95, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 376 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk14.cell_d95_s1_row376_col126
  · simp [literalRow376, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk30.row376_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
#print axioms literalSourceMatrix_row376

def literalRow378 (j : Fin 222) : M := if j.val = 123 then 2147483612 else if j.val = 124 then 2147483409 else 0

theorem literalSourceMatrix_row378 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨124, by decide⟩ : Fin 214)) = literalRow378 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 123
  · have hj : j = (⟨123, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow378]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨94, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 378 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk14.cell_d94_s0_row378_col123
  by_cases h1 : j.val = 124
  · have hj : j = (⟨124, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow378, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨94, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 378 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk14.cell_d94_s1_row378_col124
  · simp [literalRow378, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk30.row378_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row378

end
end AspisV8R19.R804LiteralSourceRowsChunk30
