import AspisV8R19.R790LiteralObservationChunk12
import AspisV8R19.R746SelectedJointMinor
import AspisV8R19.R707FullActiveDeterminant
import AspisV8R19.R698ActiveCoreLayout
import AspisV8R19.R702ActiveScalarEmbedding

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R790LiteralObservationChunk13
open AspisV8R17
open AspisV8R19.R698ActiveCoreLayout
open AspisV8R19.R702ActiveScalarEmbedding
open AspisV8R19.R707FullActiveDeterminant
open AspisV8R19.R710SelectedActivePolynomial
open AspisV8R19.R746SelectedJointMinor
abbrev Obs := R746SelectedJointMinor.ObservationRow

def obs_point_2 : Obs := Sum.inr (Sum.inl (⟨2, by decide⟩ : Fin 3))
theorem point_2_selectedColumns : selectedColumns obs_point_2 = (⟨23, by decide⟩, ⟨2, by decide⟩) := by decide
#print axioms point_2_selectedColumns
def obs_coeff_0 : Obs := Sum.inr (Sum.inr (⟨0, by decide⟩ : Fin 5))
theorem coeff_0_selectedColumns : selectedColumns obs_coeff_0 = (⟨24, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms coeff_0_selectedColumns
def obs_coeff_1 : Obs := Sum.inr (Sum.inr (⟨1, by decide⟩ : Fin 5))
theorem coeff_1_selectedColumns : selectedColumns obs_coeff_1 = (⟨24, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms coeff_1_selectedColumns
def obs_coeff_2 : Obs := Sum.inr (Sum.inr (⟨2, by decide⟩ : Fin 5))
theorem coeff_2_selectedColumns : selectedColumns obs_coeff_2 = (⟨24, by decide⟩, ⟨2, by decide⟩) := by decide
#print axioms coeff_2_selectedColumns
def obs_coeff_3 : Obs := Sum.inr (Sum.inr (⟨3, by decide⟩ : Fin 5))
theorem coeff_3_selectedColumns : selectedColumns obs_coeff_3 = (⟨27, by decide⟩, ⟨2, by decide⟩) := by decide
#print axioms coeff_3_selectedColumns
def obs_coeff_4 : Obs := Sum.inr (Sum.inr (⟨4, by decide⟩ : Fin 5))
theorem coeff_4_selectedColumns : selectedColumns obs_coeff_4 = (⟨47, by decide⟩, ⟨2, by decide⟩) := by decide
#print axioms coeff_4_selectedColumns
end AspisV8R19.R790LiteralObservationChunk13
