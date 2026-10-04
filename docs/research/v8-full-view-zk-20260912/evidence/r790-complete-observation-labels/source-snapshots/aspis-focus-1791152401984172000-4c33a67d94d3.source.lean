import AspisV8R19.R790LiteralObservationChunk06
import AspisV8R19.R746SelectedJointMinor
import AspisV8R19.R707FullActiveDeterminant
import AspisV8R19.R698ActiveCoreLayout
import AspisV8R19.R702ActiveScalarEmbedding

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R790LiteralObservationChunk07
open AspisV8R17
open AspisV8R19.R698ActiveCoreLayout
open AspisV8R19.R702ActiveScalarEmbedding
open AspisV8R19.R707FullActiveDeterminant
open AspisV8R19.R710SelectedActivePolynomial
open AspisV8R19.R746SelectedJointMinor
abbrev Obs := R746SelectedJointMinor.ObservationRow

def high_120 : High := ⟨⟨370, by decide⟩, by decide⟩
def obs_120 : Obs := Sum.inl (Sum.inl high_120)
theorem row_120_members_highActive : (⟨370, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_120_rowCode : rowCode (Sum.inl high_120 : High ⊕ Unit) = 370 := by decide
theorem row_120_selectedColumns : selectedColumns obs_120 = (⟨92, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_120_members_highActive
#print axioms row_120_rowCode
#print axioms row_120_selectedColumns
def high_121 : High := ⟨⟨372, by decide⟩, by decide⟩
def obs_121 : Obs := Sum.inl (Sum.inl high_121)
theorem row_121_members_highActive : (⟨372, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_121_rowCode : rowCode (Sum.inl high_121 : High ⊕ Unit) = 372 := by decide
theorem row_121_selectedColumns : selectedColumns obs_121 = (⟨93, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_121_members_highActive
#print axioms row_121_rowCode
#print axioms row_121_selectedColumns
def high_122 : High := ⟨⟨374, by decide⟩, by decide⟩
def obs_122 : Obs := Sum.inl (Sum.inl high_122)
theorem row_122_members_highActive : (⟨374, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_122_rowCode : rowCode (Sum.inl high_122 : High ⊕ Unit) = 374 := by decide
theorem row_122_selectedColumns : selectedColumns obs_122 = (⟨93, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_122_members_highActive
#print axioms row_122_rowCode
#print axioms row_122_selectedColumns
def high_123 : High := ⟨⟨376, by decide⟩, by decide⟩
def obs_123 : Obs := Sum.inl (Sum.inl high_123)
theorem row_123_members_highActive : (⟨376, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_123_rowCode : rowCode (Sum.inl high_123 : High ⊕ Unit) = 376 := by decide
theorem row_123_selectedColumns : selectedColumns obs_123 = (⟨94, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_123_members_highActive
#print axioms row_123_rowCode
#print axioms row_123_selectedColumns
def high_124 : High := ⟨⟨378, by decide⟩, by decide⟩
def obs_124 : Obs := Sum.inl (Sum.inl high_124)
theorem row_124_members_highActive : (⟨378, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_124_rowCode : rowCode (Sum.inl high_124 : High ⊕ Unit) = 378 := by decide
theorem row_124_selectedColumns : selectedColumns obs_124 = (⟨94, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_124_members_highActive
#print axioms row_124_rowCode
#print axioms row_124_selectedColumns
def high_125 : High := ⟨⟨380, by decide⟩, by decide⟩
def obs_125 : Obs := Sum.inl (Sum.inl high_125)
theorem row_125_members_highActive : (⟨380, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_125_rowCode : rowCode (Sum.inl high_125 : High ⊕ Unit) = 380 := by decide
theorem row_125_selectedColumns : selectedColumns obs_125 = (⟨95, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_125_members_highActive
#print axioms row_125_rowCode
#print axioms row_125_selectedColumns
def high_126 : High := ⟨⟨382, by decide⟩, by decide⟩
def obs_126 : Obs := Sum.inl (Sum.inl high_126)
theorem row_126_members_highActive : (⟨382, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_126_rowCode : rowCode (Sum.inl high_126 : High ⊕ Unit) = 382 := by decide
theorem row_126_selectedColumns : selectedColumns obs_126 = (⟨95, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_126_members_highActive
#print axioms row_126_rowCode
#print axioms row_126_selectedColumns
def high_127 : High := ⟨⟨499, by decide⟩, by decide⟩
def obs_127 : Obs := Sum.inl (Sum.inl high_127)
theorem row_127_members_highActive : (⟨499, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_127_rowCode : rowCode (Sum.inl high_127 : High ⊕ Unit) = 499 := by decide
theorem row_127_selectedColumns : selectedColumns obs_127 = (⟨124, by decide⟩, ⟨2, by decide⟩) := by decide
#print axioms row_127_members_highActive
#print axioms row_127_rowCode
#print axioms row_127_selectedColumns
def high_128 : High := ⟨⟨501, by decide⟩, by decide⟩
def obs_128 : Obs := Sum.inl (Sum.inl high_128)
theorem row_128_members_highActive : (⟨501, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_128_rowCode : rowCode (Sum.inl high_128 : High ⊕ Unit) = 501 := by decide
theorem row_128_selectedColumns : selectedColumns obs_128 = (⟨125, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_128_members_highActive
#print axioms row_128_rowCode
#print axioms row_128_selectedColumns
def high_129 : High := ⟨⟨503, by decide⟩, by decide⟩
def obs_129 : Obs := Sum.inl (Sum.inl high_129)
theorem row_129_members_highActive : (⟨503, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_129_rowCode : rowCode (Sum.inl high_129 : High ⊕ Unit) = 503 := by decide
theorem row_129_selectedColumns : selectedColumns obs_129 = (⟨125, by decide⟩, ⟨2, by decide⟩) := by decide
#print axioms row_129_members_highActive
#print axioms row_129_rowCode
#print axioms row_129_selectedColumns
def high_130 : High := ⟨⟨505, by decide⟩, by decide⟩
def obs_130 : Obs := Sum.inl (Sum.inl high_130)
theorem row_130_members_highActive : (⟨505, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_130_rowCode : rowCode (Sum.inl high_130 : High ⊕ Unit) = 505 := by decide
theorem row_130_selectedColumns : selectedColumns obs_130 = (⟨126, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_130_members_highActive
#print axioms row_130_rowCode
#print axioms row_130_selectedColumns
def high_131 : High := ⟨⟨507, by decide⟩, by decide⟩
def obs_131 : Obs := Sum.inl (Sum.inl high_131)
theorem row_131_members_highActive : (⟨507, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_131_rowCode : rowCode (Sum.inl high_131 : High ⊕ Unit) = 507 := by decide
theorem row_131_selectedColumns : selectedColumns obs_131 = (⟨126, by decide⟩, ⟨2, by decide⟩) := by decide
#print axioms row_131_members_highActive
#print axioms row_131_rowCode
#print axioms row_131_selectedColumns
def high_132 : High := ⟨⟨509, by decide⟩, by decide⟩
def obs_132 : Obs := Sum.inl (Sum.inl high_132)
theorem row_132_members_highActive : (⟨509, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_132_rowCode : rowCode (Sum.inl high_132 : High ⊕ Unit) = 509 := by decide
theorem row_132_selectedColumns : selectedColumns obs_132 = (⟨127, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_132_members_highActive
#print axioms row_132_rowCode
#print axioms row_132_selectedColumns
def high_133 : High := ⟨⟨511, by decide⟩, by decide⟩
def obs_133 : Obs := Sum.inl (Sum.inl high_133)
theorem row_133_members_highActive : (⟨511, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_133_rowCode : rowCode (Sum.inl high_133 : High ⊕ Unit) = 511 := by decide
theorem row_133_selectedColumns : selectedColumns obs_133 = (⟨127, by decide⟩, ⟨2, by decide⟩) := by decide
#print axioms row_133_members_highActive
#print axioms row_133_rowCode
#print axioms row_133_selectedColumns
def high_134 : High := ⟨⟨626, by decide⟩, by decide⟩
def obs_134 : Obs := Sum.inl (Sum.inl high_134)
theorem row_134_members_highActive : (⟨626, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_134_rowCode : rowCode (Sum.inl high_134 : High ⊕ Unit) = 626 := by decide
theorem row_134_selectedColumns : selectedColumns obs_134 = (⟨156, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_134_members_highActive
#print axioms row_134_rowCode
#print axioms row_134_selectedColumns
def high_135 : High := ⟨⟨628, by decide⟩, by decide⟩
def obs_135 : Obs := Sum.inl (Sum.inl high_135)
theorem row_135_members_highActive : (⟨628, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_135_rowCode : rowCode (Sum.inl high_135 : High ⊕ Unit) = 628 := by decide
theorem row_135_selectedColumns : selectedColumns obs_135 = (⟨157, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_135_members_highActive
#print axioms row_135_rowCode
#print axioms row_135_selectedColumns
end AspisV8R19.R790LiteralObservationChunk07
