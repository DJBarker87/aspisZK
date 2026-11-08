import PV_THR2_PacketJoinedTable
set_option autoImplicit false
noncomputable section
namespace PV_THR2_PacketJoinedTableAway
open PV_STX2_Syntax
/-- Internal pointwise resolver fact.121 is permitted when it is already the
retained scope child. All remaining conditions are generated syntax tests. -/
theorem constructor (P : Data → Option PV_STX2_SliceSyntax.Program) (fn : Data)
    (n216 : PV_THR2_OffPath.functionId fn ≠ some 216)
    (n218 : PV_THR2_OffPath.functionId fn ≠ some 218)
    (n315 : PV_THR2_OffPath.functionId fn ≠ some 315)
    (n217 : PV_THR2_OffPath.functionId fn ≠ some 217)
    (n312 : PV_THR2_OffPath.functionId fn ≠ some 312)
    (n313 : PV_THR2_OffPath.functionId fn ≠ some 313)
    (child121 : PV_THR2_OffPath.functionId fn = some 121 → P fn = none) :
    PV_THR2_PacketConstructorLocalTable.table P fn = P fn := by
  unfold PV_THR2_PacketConstructorLocalTable.table
  split <;> simp_all
/-- Internal pointwise opaque320 agreement; no execution premise. -/
theorem inner (P : Data → Option PV_STX2_SliceSyntax.Program) (fn : Data)
    (n320 : PV_THR2_OffPath.functionId fn ≠ some 320) :
    PV_THR2_PacketInner320.resolve P fn = P fn := by
  unfold PV_THR2_PacketInner320.resolve
  split <;> simp_all
/-- ONE joined resolver agrees with the retained resolver at every certified
prefix request. This is a symbolic descriptor law, not a prefix theorem. -/
theorem at_request (fallback : Data → Option PV_STX2_SliceSyntax.Program) (fn : Data)
    (n124 : fn ≠ PV_THR2_Source361PacketChildren.fn58)
    (n126 : fn ≠ PV_THR2_PacketDataTable.fn126)
    (n222 : fn ≠ PV_THR2_PacketDataTable.fn222)
    (n216 : PV_THR2_OffPath.functionId fn ≠ some 216)
    (n218 : PV_THR2_OffPath.functionId fn ≠ some 218)
    (n315 : PV_THR2_OffPath.functionId fn ≠ some 315)
    (n217 : PV_THR2_OffPath.functionId fn ≠ some 217)
    (n312 : PV_THR2_OffPath.functionId fn ≠ some 312)
    (n313 : PV_THR2_OffPath.functionId fn ≠ some 313)
    (n320 : PV_THR2_OffPath.functionId fn ≠ some 320)
    (child121 : PV_THR2_OffPath.functionId fn = some 121 →
      PV_THR2_PacketOriginalTable.table fallback fn = none) :
    PV_THR2_PacketJoinedTable.table fallback fn =
      PV_THR2_Source208Table.table (PV_THR2_PacketOriginalTable.retained fallback) fn := by
  unfold PV_THR2_PacketJoinedTable.table
  rw [constructor _ fn n216 n218 n315 n217 n312 n313]
  · rw [inner _ fn n320]
    exact PV_THR2_PacketDataExactTable.away _ fn n124 n126 n222
  · intro id
    rw [inner _ fn n320]
    exact child121 id
#print axioms constructor
#print axioms inner
#print axioms at_request
end PV_THR2_PacketJoinedTableAway
