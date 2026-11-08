import PV_THR2_Packet12801ExecutableTable
import PV_THR2_PacketInner320
set_option autoImplicit false
noncomputable section
namespace PV_THR2_PacketJoinedTable
open PV_STX2_Syntax
/-- One resolver for the constructor, metadata and dereference intervals. The
original-entry transport remains to be proved; no old run is relabelled. -/
def table (fallback : Data → Option PV_STX2_SliceSyntax.Program) :=
  PV_THR2_PacketConstructorLocalTable.table
    (PV_THR2_PacketInner320.resolve (PV_THR2_PacketOriginalTable.table fallback))
/-- All executed bodies and native-child dispositions of the three intervals. -/
theorem dispositions (fallback : Data → Option PV_STX2_SliceSyntax.Program) :
    table fallback PV_THR2_Source361PacketChildren.fn58 = some PV_THR2_F124.live ∧
    table fallback PV_THR2_PacketEnter216.fn = some PV_THR2_F216.live ∧
    table fallback PV_THR2_Packet124ReturnData.arcFn = some PV_THR2_F218.live ∧
    table fallback PV_THR2_Packet218ReturnData.fn = some PV_THR2_F315.live ∧
    table fallback PV_THR2_PacketDataTable.fn126 = some PV_THR2_F126.live ∧
    table fallback PV_THR2_PacketDataTable.fn222 = some PV_THR2_F222.live ∧
    table fallback PV_THR2_PacketInner320.fn = none ∧
    table fallback PV_THR2_Packet124BoxIssue17.fn = none ∧
    table fallback PV_THR2_Packet216Children.fn5 = none ∧
    table fallback PV_THR2_Packet216Children.fn15 = none ∧
    table fallback PV_THR2_Packet124ReturnData.intoFn = none ∧
    table fallback PV_THR2_Packet124Children.fn7 = none ∧
    table fallback PV_THR2_Packet124Children.fn9 = none ∧
    table fallback PV_THR2_Source361PacketChildren.fn63 = none ∧
    table fallback PV_THR2_Source361PacketChildren.fn70 = none := by
  refine ⟨PV_THR2_PacketOriginalTable.at124 fallback,rfl,rfl,rfl,
    PV_THR2_PacketOriginalTable.at126 fallback,
    PV_THR2_PacketOriginalTable.at222 fallback,rfl,
    PV_THR2_PacketConstructorLocalTable.atBox fallback,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  · change PV_THR2_PacketOriginalTable.table fallback PV_THR2_Source361PacketChildren.fn63 = none
    unfold PV_THR2_PacketOriginalTable.table
    obtain ⟨a,b,c⟩ := PV_THR2_PacketDispatchIds.by_id PV_THR2_Source361PacketChildren.fn63
      (by decide) (by decide) (by decide)
    rw [PV_THR2_PacketDataExactTable.away _ _ a b c]
    rw [PV_THR2_Source208Table.away]
    · rfl
    · apply PV_THR2_Source208SavedSyntax.different
      change (none : Option (Nat × Nat)) ≠ some (38973,0)
      intro h
      cases h
  · change PV_THR2_PacketOriginalTable.table fallback PV_THR2_Source361PacketChildren.fn70 = none
    unfold PV_THR2_PacketOriginalTable.table
    obtain ⟨a,b,c⟩ := PV_THR2_PacketDispatchIds.by_id PV_THR2_Source361PacketChildren.fn70
      (by decide) (by decide) (by decide)
    rw [PV_THR2_PacketDataExactTable.away _ _ a b c]
    rw [PV_THR2_Source208Table.away]
    · rfl
    · apply PV_THR2_Source208SavedSyntax.different
      change (none : Option (Nat × Nat)) ≠ some (38973,0)
      intro h
      cases h
#print axioms table
#print axioms dispositions
end PV_THR2_PacketJoinedTable
