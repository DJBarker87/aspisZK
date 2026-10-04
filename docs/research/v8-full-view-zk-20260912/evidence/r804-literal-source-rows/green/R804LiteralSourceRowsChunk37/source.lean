import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R799ActiveSourceCellsChunk18
import AspisV8R19.R799ActiveSourceCellsChunk19
import AspisV8R19.R799LiteralSourceMatrix
import AspisV8R19.R800SelectedSupportChunk37
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R804LiteralSourceRow114
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R804LiteralSourceRowsChunk37
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R799LiteralSourceMatrix
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R804LiteralSourceRow114
noncomputable section
abbrev M := ZMod 2147483647
def literalRow882 (j : Fin 222) : M := if j.val = 149 then 2147483409 else 0

theorem literalSourceMatrix_row882 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨149, by decide⟩ : Fin 214)) = literalRow882 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 149
  · have hj : j = (⟨149, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow882]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨220, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 882 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk18.cell_d220_s1_row882_col149
  · simp [literalRow882, h0]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk37.row882_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    exact h0 hm
#print axioms literalSourceMatrix_row882

def literalRow884 (j : Fin 222) : M := if j.val = 149 then 1073741826 else if j.val = 150 then 1073741772 else if j.val = 151 then 1073741483 else 0

theorem literalSourceMatrix_row884 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨150, by decide⟩ : Fin 214)) = literalRow884 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 149
  · have hj : j = (⟨149, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow884]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨220, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 884 = (1073741826 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk18.cell_d220_s1_row884_col149
  by_cases h1 : j.val = 150
  · have hj : j = (⟨150, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow884, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨221, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 884 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk18.cell_d221_s0_row884_col150
  by_cases h2 : j.val = 151
  · have hj : j = (⟨151, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow884, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨221, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 884 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk18.cell_d221_s1_row884_col151
  · simp [literalRow884, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk37.row884_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
#print axioms literalSourceMatrix_row884

def literalRow886 (j : Fin 222) : M := if j.val = 150 then 2147483612 else if j.val = 151 then 2147483409 else 0

theorem literalSourceMatrix_row886 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨151, by decide⟩ : Fin 214)) = literalRow886 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 150
  · have hj : j = (⟨150, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow886]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨221, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 886 = (2147483612 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk18.cell_d221_s0_row886_col150
  by_cases h1 : j.val = 151
  · have hj : j = (⟨151, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow886, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨221, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 886 = (2147483409 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk18.cell_d221_s1_row886_col151
  · simp [literalRow886, h0, h1]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk37.row886_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
#print axioms literalSourceMatrix_row886

def literalRow888 (j : Fin 222) : M := if j.val = 150 then 536870913 else if j.val = 151 then 536870913 else if j.val = 152 then 1073741772 else if j.val = 153 then 1073741483 else if j.val = 154 then 536870913 else if j.val = 155 then 536870913 else 0

theorem literalSourceMatrix_row888 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨152, by decide⟩ : Fin 214)) = literalRow888 := by
  letI : Nontrivial M := ⟨⟨0, 1, by decide⟩⟩
  funext j
  by_cases h0 : j.val = 150
  · have hj : j = (⟨150, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow888]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨221, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 888 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk18.cell_d221_s0_row888_col150
  by_cases h1 : j.val = 151
  · have hj : j = (⟨151, by decide⟩ : Fin 222) := Fin.ext h1
    subst j
    simp [literalRow888, h0]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨221, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 888 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk18.cell_d221_s1_row888_col151
  by_cases h2 : j.val = 152
  · have hj : j = (⟨152, by decide⟩ : Fin 222) := Fin.ext h2
    subst j
    simp [literalRow888, h0, h1]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨222, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 888 = (1073741772 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk18.cell_d222_s0_row888_col152
  by_cases h3 : j.val = 153
  · have hj : j = (⟨153, by decide⟩ : Fin 222) := Fin.ext h3
    subst j
    simp [literalRow888, h0, h1, h2]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨222, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 888 = (1073741483 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk19.cell_d222_s1_row888_col153
  by_cases h4 : j.val = 154
  · have hj : j = (⟨154, by decide⟩ : Fin 222) := Fin.ext h4
    subst j
    simp [literalRow888, h0, h1, h2, h3]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨223, by decide⟩) (⟨0, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 888 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk19.cell_d223_s0_row888_col154
  by_cases h5 : j.val = 155
  · have hj : j = (⟨155, by decide⟩ : Fin 222) := Fin.ext h5
    subst j
    simp [literalRow888, h0, h1, h2, h3, h4]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨223, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 888 = (536870913 : M)
    exact AspisV8R19.R799ActiveSourceCellsChunk19.cell_d223_s1_row888_col155
  · simp [literalRow888, h0, h1, h2, h3, h4, h5]
    rw [literalSourceMatrix_active_entry]
    apply AspisV8R19.R800SelectedSupportChunk37.row888_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j
    intro hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hbad | hbad | hbad | hbad | hbad | hbad
    · exact h0 hbad
    · exact h1 hbad
    · exact h2 hbad
    · exact h3 hbad
    · exact h4 hbad
    · exact h5 hbad
#print axioms literalSourceMatrix_row888

end
end AspisV8R19.R804LiteralSourceRowsChunk37
