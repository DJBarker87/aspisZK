import NDO_JGk_TX2_Positions0
import NDO_JGk_TX2_Positions1
import NDO_JGk_TX2_Positions2
import NDO_JGf_TX2_Sort
import NDO_JGh_TX2_FinalAudit
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGk_TX2_FrontierOrder
open Aeneas Aeneas.Std Result

def q := Port4B_KeyInstall.queries JFo_Prepared.value.queries

theorem tree0 : (OraclePortFrozenOrder.sortedPositions q 1 0).map
    (OraclePortSelectedDraft.index q 0)=JGf_TX2_Count0.indices00 := JGk_TX2_Positions0.source
#print axioms tree0
theorem tree1 : (OraclePortFrozenOrder.sortedPositions q 1 1).map
    (OraclePortSelectedDraft.index q 1)=JGf_TX2_Count0.indices00 := JGk_TX2_Positions1.source
#print axioms tree1
theorem tree2 : (OraclePortFrozenOrder.sortedPositions q 1 2).map
    (OraclePortSelectedDraft.index q 2)=JGf_TX2_Count2.indices00 := JGk_TX2_Positions2.source
#print axioms tree2

theorem source (kind : Nat) : ∃ out : Array U64 16#usize,
    Port4B_Install.leaves.op5 (JGf_TX2_Keys.raw kind) 12#usize=ok out ∧
    Port4B_LeafLoop.KeyStream q 1 kind out 0#usize
      (OraclePortFrozenOrder.sortedPositions q 1 kind) := JGh_TX2_FinalFacts.keys kind
#print axioms source
end AspisR1.JGk_TX2_FrontierOrder
end
