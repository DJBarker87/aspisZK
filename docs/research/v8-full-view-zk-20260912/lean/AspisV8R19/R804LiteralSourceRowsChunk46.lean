import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk26
import AspisV8R19.R799ActiveSourceCellsChunk27
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk46
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk46
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow964 (j : Fin 222) : M := if j.val = 183 then 1073741826 else if j.val = 184 then 1073741826 else if j.val = 185 then 1073741772 else if j.val = 186 then 1073741483 else 0

theorem literalSourceMatrix_row964 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨185, by decide⟩ : Fin 214)) = literalRow964 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 183
  · have hj : j = (⟨183, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow964]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨240, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 964 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk26.cell_d240_s0_row964_col183
  by_cases h1 : j.val = 184
  · have hj : j = (⟨184, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow964, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨240, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 964 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk26.cell_d240_s1_row964_col184
  by_cases h2 : j.val = 185
  · have hj : j = (⟨185, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow964, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨241, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 964 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk26.cell_d241_s0_row964_col185
  by_cases h3 : j.val = 186
  · have hj : j = (⟨186, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow964, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨241, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 964 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk26.cell_d241_s1_row964_col186
  · simp [literalRow964, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk46.row964_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
#print axioms literalSourceMatrix_row964

def literalRow966 (j : Fin 222) : M := if j.val = 185 then 2147483612 else if j.val = 186 then 2147483409 else 0

theorem literalSourceMatrix_row966 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨186, by decide⟩ : Fin 214)) = literalRow966 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 185
  · have hj : j = (⟨185, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow966]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨241, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 966 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk26.cell_d241_s0_row966_col185
  by_cases h1 : j.val = 186
  · have hj : j = (⟨186, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow966, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨241, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 966 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk26.cell_d241_s1_row966_col186
  · simp [literalRow966, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk46.row966_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row966

def literalRow968 (j : Fin 222) : M := if j.val = 185 then 536870913 else if j.val = 186 then 536870913 else if j.val = 187 then 1073741772 else if j.val = 188 then 1073741483 else if j.val = 189 then 536870913 else if j.val = 190 then 536870913 else 0

theorem literalSourceMatrix_row968 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨187, by decide⟩ : Fin 214)) = literalRow968 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 185
  · have hj : j = (⟨185, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow968]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨241, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 968 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk26.cell_d241_s0_row968_col185
  by_cases h1 : j.val = 186
  · have hj : j = (⟨186, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow968, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨241, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 968 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk26.cell_d241_s1_row968_col186
  by_cases h2 : j.val = 187
  · have hj : j = (⟨187, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow968, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨242, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 968 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk26.cell_d242_s0_row968_col187
  by_cases h3 : j.val = 188
  · have hj : j = (⟨188, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow968, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨242, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 968 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk26.cell_d242_s1_row968_col188
  by_cases h4 : j.val = 189
  · have hj : j = (⟨189, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow968, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨243, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 968 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk26.cell_d243_s0_row968_col189
  by_cases h5 : j.val = 190
  · have hj : j = (⟨190, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow968, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨243, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 968 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk26.cell_d243_s1_row968_col190
  · simp [literalRow968, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk46.row968_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
#print axioms literalSourceMatrix_row968

def literalRow970 (j : Fin 222) : M := if j.val = 187 then 2147483612 else if j.val = 188 then 2147483409 else 0

theorem literalSourceMatrix_row970 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨188, by decide⟩ : Fin 214)) = literalRow970 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 187
  · have hj : j = (⟨187, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow970]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨242, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 970 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk26.cell_d242_s0_row970_col187
  by_cases h1 : j.val = 188
  · have hj : j = (⟨188, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow970, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨242, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 970 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk27.cell_d242_s1_row970_col188
  · simp [literalRow970, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk46.row970_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row970

end
end AspisV8R19.R804LiteralSourceRowsChunk46
