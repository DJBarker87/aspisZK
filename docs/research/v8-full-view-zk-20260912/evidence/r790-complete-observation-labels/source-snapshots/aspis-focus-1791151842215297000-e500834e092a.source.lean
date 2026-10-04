import AspisV8R19.R746SelectedJointMinor
import AspisV8R19.R707FullActiveDeterminant
import AspisV8R19.R698ActiveCoreLayout
import AspisV8R19.R702ActiveScalarEmbedding
import AspisV8R19.TwoSwapSourceTable

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R790LiteralObservationOrderPrototype
open AspisV8R17
open AspisV8R19.R698ActiveCoreLayout
open AspisV8R19.R702ActiveScalarEmbedding
open AspisV8R19.R707FullActiveDeterminant
open AspisV8R19.R710SelectedActivePolynomial
open AspisV8R19.R746SelectedJointMinor

abbrev Obs := R746SelectedJointMinor.ObservationRow
abbrev ActiveJ := R710SelectedActivePolynomial.J

def h114 : High := ⟨⟨114, by decide⟩, by decide⟩
def h116 : High := ⟨⟨116, by decide⟩, by decide⟩
def h118 : High := ⟨⟨118, by decide⟩, by decide⟩
def h120 : High := ⟨⟨120, by decide⟩, by decide⟩
def h122 : High := ⟨⟨122, by decide⟩, by decide⟩
def h124 : High := ⟨⟨124, by decide⟩, by decide⟩
def h126 : High := ⟨⟨126, by decide⟩, by decide⟩
def h128 : High := ⟨⟨128, by decide⟩, by decide⟩

def obs0 : Obs := Sum.inl (Sum.inl h114)
def obs1 : Obs := Sum.inl (Sum.inl h116)
def obs2 : Obs := Sum.inl (Sum.inl h118)
def obs3 : Obs := Sum.inl (Sum.inl h120)
def obs4 : Obs := Sum.inl (Sum.inl h122)
def obs5 : Obs := Sum.inl (Sum.inl h124)
def obs6 : Obs := Sum.inl (Sum.inl h126)
def obs7 : Obs := Sum.inl (Sum.inl h128)

theorem row0_members_highActive : (⟨114, by decide⟩ : I) ∈ highActive := by decide
theorem row1_members_highActive : (⟨116, by decide⟩ : I) ∈ highActive := by decide
theorem row2_members_highActive : (⟨118, by decide⟩ : I) ∈ highActive := by decide
theorem row3_members_highActive : (⟨120, by decide⟩ : I) ∈ highActive := by decide
theorem row4_members_highActive : (⟨122, by decide⟩ : I) ∈ highActive := by decide
theorem row5_members_highActive : (⟨124, by decide⟩ : I) ∈ highActive := by decide
theorem row6_members_highActive : (⟨126, by decide⟩ : I) ∈ highActive := by decide
theorem row7_members_highActive : (⟨128, by decide⟩ : I) ∈ highActive := by decide

theorem row0_rowCode : rowCode (Sum.inl h114 : High ⊕ Unit) = 114 := by decide
theorem row1_rowCode : rowCode (Sum.inl h116 : High ⊕ Unit) = 116 := by decide
theorem row2_rowCode : rowCode (Sum.inl h118 : High ⊕ Unit) = 118 := by decide
theorem row3_rowCode : rowCode (Sum.inl h120 : High ⊕ Unit) = 120 := by decide
theorem row4_rowCode : rowCode (Sum.inl h122 : High ⊕ Unit) = 122 := by decide
theorem row5_rowCode : rowCode (Sum.inl h124 : High ⊕ Unit) = 124 := by decide
theorem row6_rowCode : rowCode (Sum.inl h126 : High ⊕ Unit) = 126 := by decide
theorem row7_rowCode : rowCode (Sum.inl h128 : High ⊕ Unit) = 128 := by decide

theorem row0_selectedColumn : selectedColumns obs0 = (⟨28, by decide⟩, ⟨1, by decide⟩) := by decide
theorem row1_selectedColumn : selectedColumns obs1 = (⟨29, by decide⟩, ⟨0, by decide⟩) := by decide
theorem row2_selectedColumn : selectedColumns obs2 = (⟨29, by decide⟩, ⟨1, by decide⟩) := by decide
theorem row3_selectedColumn : selectedColumns obs3 = (⟨30, by decide⟩, ⟨0, by decide⟩) := by decide
theorem row4_selectedColumn : selectedColumns obs4 = (⟨30, by decide⟩, ⟨1, by decide⟩) := by decide
theorem row5_selectedColumn : selectedColumns obs5 = (⟨31, by decide⟩, ⟨0, by decide⟩) := by decide
theorem row6_selectedColumn : selectedColumns obs6 = (⟨31, by decide⟩, ⟨1, by decide⟩) := by decide
theorem row7_selectedColumn : selectedColumns obs7 = (⟨32, by decide⟩, ⟨0, by decide⟩) := by decide

#print axioms row0_members_highActive
#print axioms row1_members_highActive
#print axioms row2_members_highActive
#print axioms row3_members_highActive
#print axioms row4_members_highActive
#print axioms row5_members_highActive
#print axioms row6_members_highActive
#print axioms row7_members_highActive
#print axioms row0_rowCode
#print axioms row1_rowCode
#print axioms row2_rowCode
#print axioms row3_rowCode
#print axioms row4_rowCode
#print axioms row5_rowCode
#print axioms row6_rowCode
#print axioms row7_rowCode
#print axioms row0_selectedColumn
#print axioms row1_selectedColumn
#print axioms row2_selectedColumn
#print axioms row3_selectedColumn
#print axioms row4_selectedColumn
#print axioms row5_selectedColumn
#print axioms row6_selectedColumn
#print axioms row7_selectedColumn
end AspisV8R19.R790LiteralObservationOrderPrototype
