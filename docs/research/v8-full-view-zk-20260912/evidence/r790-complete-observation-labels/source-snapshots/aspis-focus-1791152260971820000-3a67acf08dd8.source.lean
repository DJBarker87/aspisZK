import AspisV8R19.R790LiteralObservationOrderPrototype
import AspisV8R19.R746SelectedJointMinor
import AspisV8R19.R707FullActiveDeterminant
import AspisV8R19.R698ActiveCoreLayout
import AspisV8R19.R702ActiveScalarEmbedding

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R790LiteralObservationChunk00
open AspisV8R17
open AspisV8R19.R698ActiveCoreLayout
open AspisV8R19.R702ActiveScalarEmbedding
open AspisV8R19.R707FullActiveDeterminant
open AspisV8R19.R710SelectedActivePolynomial
open AspisV8R19.R746SelectedJointMinor
abbrev Obs := R746SelectedJointMinor.ObservationRow

def high_008 : High := ⟨⟨130, by decide⟩, by decide⟩
def obs_008 : Obs := Sum.inl (Sum.inl high_008)
theorem row_008_members_highActive : (⟨130, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_008_rowCode : rowCode (Sum.inl high_008 : High ⊕ Unit) = 130 := by decide
theorem row_008_selectedColumns : selectedColumns obs_008 = (⟨32, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_008_members_highActive
#print axioms row_008_rowCode
#print axioms row_008_selectedColumns
def high_009 : High := ⟨⟨132, by decide⟩, by decide⟩
def obs_009 : Obs := Sum.inl (Sum.inl high_009)
theorem row_009_members_highActive : (⟨132, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_009_rowCode : rowCode (Sum.inl high_009 : High ⊕ Unit) = 132 := by decide
theorem row_009_selectedColumns : selectedColumns obs_009 = (⟨33, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_009_members_highActive
#print axioms row_009_rowCode
#print axioms row_009_selectedColumns
def high_010 : High := ⟨⟨134, by decide⟩, by decide⟩
def obs_010 : Obs := Sum.inl (Sum.inl high_010)
theorem row_010_members_highActive : (⟨134, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_010_rowCode : rowCode (Sum.inl high_010 : High ⊕ Unit) = 134 := by decide
theorem row_010_selectedColumns : selectedColumns obs_010 = (⟨33, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_010_members_highActive
#print axioms row_010_rowCode
#print axioms row_010_selectedColumns
def high_011 : High := ⟨⟨136, by decide⟩, by decide⟩
def obs_011 : Obs := Sum.inl (Sum.inl high_011)
theorem row_011_members_highActive : (⟨136, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_011_rowCode : rowCode (Sum.inl high_011 : High ⊕ Unit) = 136 := by decide
theorem row_011_selectedColumns : selectedColumns obs_011 = (⟨34, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_011_members_highActive
#print axioms row_011_rowCode
#print axioms row_011_selectedColumns
def high_012 : High := ⟨⟨138, by decide⟩, by decide⟩
def obs_012 : Obs := Sum.inl (Sum.inl high_012)
theorem row_012_members_highActive : (⟨138, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_012_rowCode : rowCode (Sum.inl high_012 : High ⊕ Unit) = 138 := by decide
theorem row_012_selectedColumns : selectedColumns obs_012 = (⟨34, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_012_members_highActive
#print axioms row_012_rowCode
#print axioms row_012_selectedColumns
def high_013 : High := ⟨⟨140, by decide⟩, by decide⟩
def obs_013 : Obs := Sum.inl (Sum.inl high_013)
theorem row_013_members_highActive : (⟨140, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_013_rowCode : rowCode (Sum.inl high_013 : High ⊕ Unit) = 140 := by decide
theorem row_013_selectedColumns : selectedColumns obs_013 = (⟨35, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_013_members_highActive
#print axioms row_013_rowCode
#print axioms row_013_selectedColumns
def high_014 : High := ⟨⟨142, by decide⟩, by decide⟩
def obs_014 : Obs := Sum.inl (Sum.inl high_014)
theorem row_014_members_highActive : (⟨142, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_014_rowCode : rowCode (Sum.inl high_014 : High ⊕ Unit) = 142 := by decide
theorem row_014_selectedColumns : selectedColumns obs_014 = (⟨35, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_014_members_highActive
#print axioms row_014_rowCode
#print axioms row_014_selectedColumns
def high_015 : High := ⟨⟨144, by decide⟩, by decide⟩
def obs_015 : Obs := Sum.inl (Sum.inl high_015)
theorem row_015_members_highActive : (⟨144, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_015_rowCode : rowCode (Sum.inl high_015 : High ⊕ Unit) = 144 := by decide
theorem row_015_selectedColumns : selectedColumns obs_015 = (⟨36, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_015_members_highActive
#print axioms row_015_rowCode
#print axioms row_015_selectedColumns
def high_016 : High := ⟨⟨146, by decide⟩, by decide⟩
def obs_016 : Obs := Sum.inl (Sum.inl high_016)
theorem row_016_members_highActive : (⟨146, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_016_rowCode : rowCode (Sum.inl high_016 : High ⊕ Unit) = 146 := by decide
theorem row_016_selectedColumns : selectedColumns obs_016 = (⟨36, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_016_members_highActive
#print axioms row_016_rowCode
#print axioms row_016_selectedColumns
def high_017 : High := ⟨⟨148, by decide⟩, by decide⟩
def obs_017 : Obs := Sum.inl (Sum.inl high_017)
theorem row_017_members_highActive : (⟨148, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_017_rowCode : rowCode (Sum.inl high_017 : High ⊕ Unit) = 148 := by decide
theorem row_017_selectedColumns : selectedColumns obs_017 = (⟨37, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_017_members_highActive
#print axioms row_017_rowCode
#print axioms row_017_selectedColumns
def high_018 : High := ⟨⟨150, by decide⟩, by decide⟩
def obs_018 : Obs := Sum.inl (Sum.inl high_018)
theorem row_018_members_highActive : (⟨150, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_018_rowCode : rowCode (Sum.inl high_018 : High ⊕ Unit) = 150 := by decide
theorem row_018_selectedColumns : selectedColumns obs_018 = (⟨37, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_018_members_highActive
#print axioms row_018_rowCode
#print axioms row_018_selectedColumns
def high_019 : High := ⟨⟨152, by decide⟩, by decide⟩
def obs_019 : Obs := Sum.inl (Sum.inl high_019)
theorem row_019_members_highActive : (⟨152, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_019_rowCode : rowCode (Sum.inl high_019 : High ⊕ Unit) = 152 := by decide
theorem row_019_selectedColumns : selectedColumns obs_019 = (⟨38, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_019_members_highActive
#print axioms row_019_rowCode
#print axioms row_019_selectedColumns
def high_020 : High := ⟨⟨154, by decide⟩, by decide⟩
def obs_020 : Obs := Sum.inl (Sum.inl high_020)
theorem row_020_members_highActive : (⟨154, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_020_rowCode : rowCode (Sum.inl high_020 : High ⊕ Unit) = 154 := by decide
theorem row_020_selectedColumns : selectedColumns obs_020 = (⟨38, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_020_members_highActive
#print axioms row_020_rowCode
#print axioms row_020_selectedColumns
def high_021 : High := ⟨⟨156, by decide⟩, by decide⟩
def obs_021 : Obs := Sum.inl (Sum.inl high_021)
theorem row_021_members_highActive : (⟨156, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_021_rowCode : rowCode (Sum.inl high_021 : High ⊕ Unit) = 156 := by decide
theorem row_021_selectedColumns : selectedColumns obs_021 = (⟨39, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_021_members_highActive
#print axioms row_021_rowCode
#print axioms row_021_selectedColumns
def high_022 : High := ⟨⟨158, by decide⟩, by decide⟩
def obs_022 : Obs := Sum.inl (Sum.inl high_022)
theorem row_022_members_highActive : (⟨158, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_022_rowCode : rowCode (Sum.inl high_022 : High ⊕ Unit) = 158 := by decide
theorem row_022_selectedColumns : selectedColumns obs_022 = (⟨39, by decide⟩, ⟨1, by decide⟩) := by decide
#print axioms row_022_members_highActive
#print axioms row_022_rowCode
#print axioms row_022_selectedColumns
def high_023 : High := ⟨⟨160, by decide⟩, by decide⟩
def obs_023 : Obs := Sum.inl (Sum.inl high_023)
theorem row_023_members_highActive : (⟨160, by decide⟩ : R698ActiveCoreLayout.I) ∈ highActive := by decide
theorem row_023_rowCode : rowCode (Sum.inl high_023 : High ⊕ Unit) = 160 := by decide
theorem row_023_selectedColumns : selectedColumns obs_023 = (⟨40, by decide⟩, ⟨0, by decide⟩) := by decide
#print axioms row_023_members_highActive
#print axioms row_023_rowCode
#print axioms row_023_selectedColumns
end AspisV8R19.R790LiteralObservationChunk00
