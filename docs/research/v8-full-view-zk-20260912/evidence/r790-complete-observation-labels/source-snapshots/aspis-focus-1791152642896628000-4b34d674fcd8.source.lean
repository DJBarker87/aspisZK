import AspisV8R19.R790LiteralObservationChunk11
import AspisV8R19.R746SelectedJointMinor
import AspisV8R19.R707FullActiveDeterminant
import AspisV8R19.R698ActiveCoreLayout
import AspisV8R19.R702ActiveScalarEmbedding

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R790LiteralObservationChunk12
open AspisV8R17
open AspisV8R19.R698ActiveCoreLayout
open AspisV8R19.R702ActiveScalarEmbedding
open AspisV8R19.R707FullActiveDeterminant
open AspisV8R19.R710SelectedActivePolynomial
open AspisV8R19.R746SelectedJointMinor
abbrev Obs := R746SelectedJointMinor.ObservationRow

def high_200 : High := ⟨⟨994, by decide⟩, by decide⟩
def obs_200 : Obs := Sum.inl (Sum.inl high_200)
theorem row_200_members_highActive : (⟨994, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_200_rowCode : rowCode (Sum.inl high_200 : High ⊕ Unit) = 994 := by decide
theorem row_200_selectedColumns : selectedColumns obs_200 = (⟨248, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_200_members_highActive
#print axioms row_200_rowCode
#print axioms row_200_selectedColumns
def high_201 : High := ⟨⟨996, by decide⟩, by decide⟩
def obs_201 : Obs := Sum.inl (Sum.inl high_201)
theorem row_201_members_highActive : (⟨996, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_201_rowCode : rowCode (Sum.inl high_201 : High ⊕ Unit) = 996 := by decide
theorem row_201_selectedColumns : selectedColumns obs_201 = (⟨249, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_201_members_highActive
#print axioms row_201_rowCode
#print axioms row_201_selectedColumns
def high_202 : High := ⟨⟨998, by decide⟩, by decide⟩
def obs_202 : Obs := Sum.inl (Sum.inl high_202)
theorem row_202_members_highActive : (⟨998, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_202_rowCode : rowCode (Sum.inl high_202 : High ⊕ Unit) = 998 := by decide
theorem row_202_selectedColumns : selectedColumns obs_202 = (⟨249, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_202_members_highActive
#print axioms row_202_rowCode
#print axioms row_202_selectedColumns
def high_203 : High := ⟨⟨1000, by decide⟩, by decide⟩
def obs_203 : Obs := Sum.inl (Sum.inl high_203)
theorem row_203_members_highActive : (⟨1000, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_203_rowCode : rowCode (Sum.inl high_203 : High ⊕ Unit) = 1000 := by decide
theorem row_203_selectedColumns : selectedColumns obs_203 = (⟨250, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_203_members_highActive
#print axioms row_203_rowCode
#print axioms row_203_selectedColumns
def high_204 : High := ⟨⟨1002, by decide⟩, by decide⟩
def obs_204 : Obs := Sum.inl (Sum.inl high_204)
theorem row_204_members_highActive : (⟨1002, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_204_rowCode : rowCode (Sum.inl high_204 : High ⊕ Unit) = 1002 := by decide
theorem row_204_selectedColumns : selectedColumns obs_204 = (⟨250, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_204_members_highActive
#print axioms row_204_rowCode
#print axioms row_204_selectedColumns
def high_205 : High := ⟨⟨1004, by decide⟩, by decide⟩
def obs_205 : Obs := Sum.inl (Sum.inl high_205)
theorem row_205_members_highActive : (⟨1004, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_205_rowCode : rowCode (Sum.inl high_205 : High ⊕ Unit) = 1004 := by decide
theorem row_205_selectedColumns : selectedColumns obs_205 = (⟨251, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_205_members_highActive
#print axioms row_205_rowCode
#print axioms row_205_selectedColumns
def high_206 : High := ⟨⟨1006, by decide⟩, by decide⟩
def obs_206 : Obs := Sum.inl (Sum.inl high_206)
theorem row_206_members_highActive : (⟨1006, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_206_rowCode : rowCode (Sum.inl high_206 : High ⊕ Unit) = 1006 := by decide
theorem row_206_selectedColumns : selectedColumns obs_206 = (⟨251, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_206_members_highActive
#print axioms row_206_rowCode
#print axioms row_206_selectedColumns
def high_207 : High := ⟨⟨1008, by decide⟩, by decide⟩
def obs_207 : Obs := Sum.inl (Sum.inl high_207)
theorem row_207_members_highActive : (⟨1008, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_207_rowCode : rowCode (Sum.inl high_207 : High ⊕ Unit) = 1008 := by decide
theorem row_207_selectedColumns : selectedColumns obs_207 = (⟨252, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_207_members_highActive
#print axioms row_207_rowCode
#print axioms row_207_selectedColumns
def high_208 : High := ⟨⟨1011, by decide⟩, by decide⟩
def obs_208 : Obs := Sum.inl (Sum.inl high_208)
theorem row_208_members_highActive : (⟨1011, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_208_rowCode : rowCode (Sum.inl high_208 : High ⊕ Unit) = 1011 := by decide
theorem row_208_selectedColumns : selectedColumns obs_208 = (⟨252, by decide⟩, ⟨2, by decide⟩) := by decide
#print axioms row_208_members_highActive
#print axioms row_208_rowCode
#print axioms row_208_selectedColumns
def high_209 : High := ⟨⟨1013, by decide⟩, by decide⟩
def obs_209 : Obs := Sum.inl (Sum.inl high_209)
theorem row_209_members_highActive : (⟨1013, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_209_rowCode : rowCode (Sum.inl high_209 : High ⊕ Unit) = 1013 := by decide
theorem row_209_selectedColumns : selectedColumns obs_209 = (⟨253, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_209_members_highActive
#print axioms row_209_rowCode
#print axioms row_209_selectedColumns
def high_210 : High := ⟨⟨1015, by decide⟩, by decide⟩
def obs_210 : Obs := Sum.inl (Sum.inl high_210)
theorem row_210_members_highActive : (⟨1015, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_210_rowCode : rowCode (Sum.inl high_210 : High ⊕ Unit) = 1015 := by decide
theorem row_210_selectedColumns : selectedColumns obs_210 = (⟨253, by decide⟩, ⟨2, by decide⟩) := by decide
#print axioms row_210_members_highActive
#print axioms row_210_rowCode
#print axioms row_210_selectedColumns
def high_211 : High := ⟨⟨1017, by decide⟩, by decide⟩
def obs_211 : Obs := Sum.inl (Sum.inl high_211)
theorem row_211_members_highActive : (⟨1017, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_211_rowCode : rowCode (Sum.inl high_211 : High ⊕ Unit) = 1017 := by decide
theorem row_211_selectedColumns : selectedColumns obs_211 = (⟨254, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_211_members_highActive
#print axioms row_211_rowCode
#print axioms row_211_selectedColumns
def high_212 : High := ⟨⟨1019, by decide⟩, by decide⟩
def obs_212 : Obs := Sum.inl (Sum.inl high_212)
theorem row_212_members_highActive : (⟨1019, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_212_rowCode : rowCode (Sum.inl high_212 : High ⊕ Unit) = 1019 := by decide
theorem row_212_selectedColumns : selectedColumns obs_212 = (⟨254, by decide⟩, ⟨2, by decide⟩) := by decide
#print axioms row_212_members_highActive
#print axioms row_212_rowCode
#print axioms row_212_selectedColumns
def obs_top : Obs := Sum.inl (Sum.inr ())
theorem top_rowCode : rowCode (Sum.inr () : High ⊕ Unit) = 1022 := by decide
theorem top_selectedColumns : selectedColumns obs_top = (⟨254, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms top_rowCode
#print axioms top_selectedColumns
def obs_point_0 : Obs := Sum.inr (Sum.inl (⟨0, by decide⟩ : Fin 3))
theorem point_0_selectedColumns : selectedColumns obs_point_0 = (⟨23, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms point_0_selectedColumns
def obs_point_1 : Obs := Sum.inr (Sum.inl (⟨1, by decide⟩ : Fin 3))
theorem point_1_selectedColumns : selectedColumns obs_point_1 = (⟨23, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms point_1_selectedColumns
end AspisV8R19.R790LiteralObservationChunk12
