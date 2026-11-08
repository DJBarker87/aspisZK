import PV_THR2_PacketConstructorLocalTable
import PV_THR2_PacketOriginalTable
set_option autoImplicit false
noncomputable section
namespace PV_THR2_Packet12801ExecutableTable
open PV_STX2_Syntax
/-- Used only at the reached12801 call, never installed at originalF0 entry. -/
def table (fallback : Data → Option PV_STX2_SliceSyntax.Program) (d : Data) :=
  match PV_THR2_OffPath.functionId d with
  | some 124 => some PV_THR2_F124.live
  | _ => PV_THR2_PacketConstructorLocalTable.table (PV_THR2_PacketOriginalTable.table fallback) d
theorem entry (fallback : Data → Option PV_STX2_SliceSyntax.Program) :
    table fallback PV_THR2_Source361PacketChildren.fn58 = some PV_THR2_F124.live := rfl
theorem bodies (fallback : Data → Option PV_STX2_SliceSyntax.Program) :
    table fallback PV_THR2_PacketEnter216.fn = some PV_THR2_F216.live ∧
    table fallback PV_THR2_Packet124ReturnData.arcFn = some PV_THR2_F218.live ∧
    table fallback PV_THR2_Packet218ReturnData.fn = some PV_THR2_F315.live := ⟨rfl,rfl,rfl⟩
theorem children (fallback : Data → Option PV_STX2_SliceSyntax.Program) :
    table fallback PV_THR2_Packet124BoxIssue17.fn = none ∧
    table fallback PV_THR2_Packet216Children.fn5 = none ∧
    table fallback PV_THR2_Packet216Children.fn15 = none ∧
    table fallback PV_THR2_Packet124ReturnData.intoFn = none ∧
    table fallback PV_THR2_Packet124Children.fn7 = none ∧
    table fallback PV_THR2_Packet124Children.fn9 = none := by
  exact ⟨PV_THR2_PacketConstructorLocalTable.atBox fallback,rfl,rfl,rfl,rfl,rfl⟩
#print axioms entry
#print axioms bodies
#print axioms children
end PV_THR2_Packet12801ExecutableTable
