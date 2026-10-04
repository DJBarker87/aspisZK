import AspisV8R19.R790LiteralObservationChunk01
import AspisV8R19.R746SelectedJointMinor
import AspisV8R19.R707FullActiveDeterminant
import AspisV8R19.R698ActiveCoreLayout
import AspisV8R19.R702ActiveScalarEmbedding

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R790LiteralObservationChunk02
open AspisV8R17
open AspisV8R19.R698ActiveCoreLayout
open AspisV8R19.R702ActiveScalarEmbedding
open AspisV8R19.R707FullActiveDeterminant
open AspisV8R19.R710SelectedActivePolynomial
open AspisV8R19.R746SelectedJointMinor
abbrev Obs := R746SelectedJointMinor.ObservationRow

def high_040 : High := ⟨⟨202, by decide⟩, by decide⟩
def obs_040 : Obs := Sum.inl (Sum.inl high_040)
theorem row_040_members_highActive : (⟨202, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_040_rowCode : rowCode (Sum.inl high_040 : High ⊕ Unit) = 202 := by decide
theorem row_040_selectedColumns : selectedColumns obs_040 = (⟨50, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_040_members_highActive
#print axioms row_040_rowCode
#print axioms row_040_selectedColumns
def high_041 : High := ⟨⟨204, by decide⟩, by decide⟩
def obs_041 : Obs := Sum.inl (Sum.inl high_041)
theorem row_041_members_highActive : (⟨204, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_041_rowCode : rowCode (Sum.inl high_041 : High ⊕ Unit) = 204 := by decide
theorem row_041_selectedColumns : selectedColumns obs_041 = (⟨51, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_041_members_highActive
#print axioms row_041_rowCode
#print axioms row_041_selectedColumns
def high_042 : High := ⟨⟨206, by decide⟩, by decide⟩
def obs_042 : Obs := Sum.inl (Sum.inl high_042)
theorem row_042_members_highActive : (⟨206, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_042_rowCode : rowCode (Sum.inl high_042 : High ⊕ Unit) = 206 := by decide
theorem row_042_selectedColumns : selectedColumns obs_042 = (⟨51, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_042_members_highActive
#print axioms row_042_rowCode
#print axioms row_042_selectedColumns
def high_043 : High := ⟨⟨208, by decide⟩, by decide⟩
def obs_043 : Obs := Sum.inl (Sum.inl high_043)
theorem row_043_members_highActive : (⟨208, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_043_rowCode : rowCode (Sum.inl high_043 : High ⊕ Unit) = 208 := by decide
theorem row_043_selectedColumns : selectedColumns obs_043 = (⟨52, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_043_members_highActive
#print axioms row_043_rowCode
#print axioms row_043_selectedColumns
def high_044 : High := ⟨⟨210, by decide⟩, by decide⟩
def obs_044 : Obs := Sum.inl (Sum.inl high_044)
theorem row_044_members_highActive : (⟨210, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_044_rowCode : rowCode (Sum.inl high_044 : High ⊕ Unit) = 210 := by decide
theorem row_044_selectedColumns : selectedColumns obs_044 = (⟨52, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_044_members_highActive
#print axioms row_044_rowCode
#print axioms row_044_selectedColumns
def high_045 : High := ⟨⟨212, by decide⟩, by decide⟩
def obs_045 : Obs := Sum.inl (Sum.inl high_045)
theorem row_045_members_highActive : (⟨212, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_045_rowCode : rowCode (Sum.inl high_045 : High ⊕ Unit) = 212 := by decide
theorem row_045_selectedColumns : selectedColumns obs_045 = (⟨53, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_045_members_highActive
#print axioms row_045_rowCode
#print axioms row_045_selectedColumns
def high_046 : High := ⟨⟨214, by decide⟩, by decide⟩
def obs_046 : Obs := Sum.inl (Sum.inl high_046)
theorem row_046_members_highActive : (⟨214, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_046_rowCode : rowCode (Sum.inl high_046 : High ⊕ Unit) = 214 := by decide
theorem row_046_selectedColumns : selectedColumns obs_046 = (⟨53, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_046_members_highActive
#print axioms row_046_rowCode
#print axioms row_046_selectedColumns
def high_047 : High := ⟨⟨216, by decide⟩, by decide⟩
def obs_047 : Obs := Sum.inl (Sum.inl high_047)
theorem row_047_members_highActive : (⟨216, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_047_rowCode : rowCode (Sum.inl high_047 : High ⊕ Unit) = 216 := by decide
theorem row_047_selectedColumns : selectedColumns obs_047 = (⟨54, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_047_members_highActive
#print axioms row_047_rowCode
#print axioms row_047_selectedColumns
def high_048 : High := ⟨⟨218, by decide⟩, by decide⟩
def obs_048 : Obs := Sum.inl (Sum.inl high_048)
theorem row_048_members_highActive : (⟨218, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_048_rowCode : rowCode (Sum.inl high_048 : High ⊕ Unit) = 218 := by decide
theorem row_048_selectedColumns : selectedColumns obs_048 = (⟨54, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_048_members_highActive
#print axioms row_048_rowCode
#print axioms row_048_selectedColumns
def high_049 : High := ⟨⟨220, by decide⟩, by decide⟩
def obs_049 : Obs := Sum.inl (Sum.inl high_049)
theorem row_049_members_highActive : (⟨220, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_049_rowCode : rowCode (Sum.inl high_049 : High ⊕ Unit) = 220 := by decide
theorem row_049_selectedColumns : selectedColumns obs_049 = (⟨55, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_049_members_highActive
#print axioms row_049_rowCode
#print axioms row_049_selectedColumns
def high_050 : High := ⟨⟨222, by decide⟩, by decide⟩
def obs_050 : Obs := Sum.inl (Sum.inl high_050)
theorem row_050_members_highActive : (⟨222, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_050_rowCode : rowCode (Sum.inl high_050 : High ⊕ Unit) = 222 := by decide
theorem row_050_selectedColumns : selectedColumns obs_050 = (⟨55, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_050_members_highActive
#print axioms row_050_rowCode
#print axioms row_050_selectedColumns
def high_051 : High := ⟨⟨224, by decide⟩, by decide⟩
def obs_051 : Obs := Sum.inl (Sum.inl high_051)
theorem row_051_members_highActive : (⟨224, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_051_rowCode : rowCode (Sum.inl high_051 : High ⊕ Unit) = 224 := by decide
theorem row_051_selectedColumns : selectedColumns obs_051 = (⟨56, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_051_members_highActive
#print axioms row_051_rowCode
#print axioms row_051_selectedColumns
def high_052 : High := ⟨⟨226, by decide⟩, by decide⟩
def obs_052 : Obs := Sum.inl (Sum.inl high_052)
theorem row_052_members_highActive : (⟨226, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_052_rowCode : rowCode (Sum.inl high_052 : High ⊕ Unit) = 226 := by decide
theorem row_052_selectedColumns : selectedColumns obs_052 = (⟨56, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_052_members_highActive
#print axioms row_052_rowCode
#print axioms row_052_selectedColumns
def high_053 : High := ⟨⟨228, by decide⟩, by decide⟩
def obs_053 : Obs := Sum.inl (Sum.inl high_053)
theorem row_053_members_highActive : (⟨228, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_053_rowCode : rowCode (Sum.inl high_053 : High ⊕ Unit) = 228 := by decide
theorem row_053_selectedColumns : selectedColumns obs_053 = (⟨57, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_053_members_highActive
#print axioms row_053_rowCode
#print axioms row_053_selectedColumns
def high_054 : High := ⟨⟨230, by decide⟩, by decide⟩
def obs_054 : Obs := Sum.inl (Sum.inl high_054)
theorem row_054_members_highActive : (⟨230, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_054_rowCode : rowCode (Sum.inl high_054 : High ⊕ Unit) = 230 := by decide
theorem row_054_selectedColumns : selectedColumns obs_054 = (⟨57, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_054_members_highActive
#print axioms row_054_rowCode
#print axioms row_054_selectedColumns
def high_055 : High := ⟨⟨232, by decide⟩, by decide⟩
def obs_055 : Obs := Sum.inl (Sum.inl high_055)
theorem row_055_members_highActive : (⟨232, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_055_rowCode : rowCode (Sum.inl high_055 : High ⊕ Unit) = 232 := by decide
theorem row_055_selectedColumns : selectedColumns obs_055 = (⟨58, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_055_members_highActive
#print axioms row_055_rowCode
#print axioms row_055_selectedColumns
end AspisV8R19.R790LiteralObservationChunk02
