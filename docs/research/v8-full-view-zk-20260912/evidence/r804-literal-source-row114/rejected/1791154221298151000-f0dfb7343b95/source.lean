import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R797ActiveSourceCellsPreflight
import AspisV8R19.R748JointWitnessPointEntry
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace AspisV8R19.R804LiteralSourceRow114
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R800SelectedSupportPrototype
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R797ActiveSourceCellsPreflight
noncomputable section
abbrev M := ZMod 2147483647
def halfSelected : M := 1073741824
def quarterSelected : M := 536870912
def alphaSelected : M := 7
def uSelected : M := 2
def vSelected : M := 3
def kappaSelected : M := 5
def tauSelected : M := 0
def literalRow114 (j : Fin 222) : M :=
  if j.val = 0 then 2147483409 else if j.val = 220 then 1342177280 else 0

theorem literalSourceMatrix_row114 :
    (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected
      kappaSelected tauSelected z) (activePosition (⟨0, by decide⟩ : Fin 214)) = literalRow114 := by
  funext j
  by_cases h0 : j.val = 0
  · have hj : j = (⟨0, by decide⟩ : Fin 222) := Fin.ext h0
    subst j
    simp [literalRow114]
    rw [literalSourceMatrix_active_entry]
    change sourceChord halfSelected (direction alphaSelected (⟨28, by decide⟩) (⟨1, by decide⟩))
      (7 : M) (5 : M) (-5 : M) 114 = (2147483409 : M)
    exact cell_d28_s1_row114
  · by_cases h220 : j.val = 220
    · have hj : j = (⟨220, by decide⟩ : Fin 222) := Fin.ext h220
      subst j
      simp [literalRow114, h0]
      rw [literalSourceMatrix_active_entry]
      change sourceChord halfSelected (direction alphaSelected (⟨27, by decide⟩) (⟨2, by decide⟩))
        (7 : M) (5 : M) (-5 : M) 114 = (1342177280 : M)
      exact cell_d27_s2_row114
    · simp [literalRow114, h0, h220]
      rw [literalSourceMatrix_active_entry]
      exact row114_source_zero halfSelected alphaSelected (7 : M) (5 : M) (-5 : M) j (by simpa using And.intro h0 h220)

#print axioms literalSourceMatrix_row114
end
end AspisV8R19.R804LiteralSourceRow114
