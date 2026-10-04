import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk23
import AspisV8R19.R799ActiveSourceCellsChunk24
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk43
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk43
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow934 (j : Fin 222) : M := if j.val = 172 then 2147483612 else if j.val = 173 then 2147483409 else 0

theorem literalSourceMatrix_row934 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨173, by decide⟩ : Fin 214)) = literalRow934 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 172
  · have hj : j = (⟨172, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow934]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨233, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 934 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk23.cell_d233_s0_row934_col172
  by_cases h1 : j.val = 173
  · have hj : j = (⟨173, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow934, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨233, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 934 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk23.cell_d233_s1_row934_col173
  · simp [literalRow934, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk43.row934_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row934

def literalRow936 (j : Fin 222) : M := if j.val = 172 then 536870913 else if j.val = 173 then 536870913 else if j.val = 174 then 1073741772 else if j.val = 175 then 1073741483 else if j.val = 176 then 536870913 else if j.val = 177 then 536870913 else 0

theorem literalSourceMatrix_row936 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨174, by decide⟩ : Fin 214)) = literalRow936 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 172
  · have hj : j = (⟨172, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow936]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨233, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 936 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk23.cell_d233_s0_row936_col172
  by_cases h1 : j.val = 173
  · have hj : j = (⟨173, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow936, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨233, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 936 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk23.cell_d233_s1_row936_col173
  by_cases h2 : j.val = 174
  · have hj : j = (⟨174, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow936, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨234, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 936 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk23.cell_d234_s0_row936_col174
  by_cases h3 : j.val = 175
  · have hj : j = (⟨175, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow936, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨234, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 936 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk23.cell_d234_s1_row936_col175
  by_cases h4 : j.val = 176
  · have hj : j = (⟨176, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow936, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨235, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 936 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk24.cell_d235_s0_row936_col176
  by_cases h5 : j.val = 177
  · have hj : j = (⟨177, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow936, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨235, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 936 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk24.cell_d235_s1_row936_col177
  · simp [literalRow936, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk43.row936_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
#print axioms literalSourceMatrix_row936

def literalRow938 (j : Fin 222) : M := if j.val = 174 then 2147483612 else if j.val = 175 then 2147483409 else 0

theorem literalSourceMatrix_row938 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨175, by decide⟩ : Fin 214)) = literalRow938 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 174
  · have hj : j = (⟨174, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow938]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨234, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 938 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk24.cell_d234_s0_row938_col174
  by_cases h1 : j.val = 175
  · have hj : j = (⟨175, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow938, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨234, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 938 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk24.cell_d234_s1_row938_col175
  · simp [literalRow938, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk43.row938_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row938

def literalRow940 (j : Fin 222) : M := if j.val = 174 then 1073741826 else if j.val = 175 then 1073741826 else if j.val = 176 then 1073741772 else if j.val = 177 then 1073741483 else 0

theorem literalSourceMatrix_row940 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨176, by decide⟩ : Fin 214)) = literalRow940 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 174
  · have hj : j = (⟨174, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow940]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨234, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 940 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk24.cell_d234_s0_row940_col174
  by_cases h1 : j.val = 175
  · have hj : j = (⟨175, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow940, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨234, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 940 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk24.cell_d234_s1_row940_col175
  by_cases h2 : j.val = 176
  · have hj : j = (⟨176, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow940, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨235, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 940 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk24.cell_d235_s0_row940_col176
  by_cases h3 : j.val = 177
  · have hj : j = (⟨177, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow940, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨235, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 940 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk24.cell_d235_s1_row940_col177
  · simp [literalRow940, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk43.row940_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row940

end
end AspisV8R19.R804LiteralSourceRowsChunk43
