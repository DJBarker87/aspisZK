import NMX_ProgramFold
import NMX_FullChildren
import NMX_SourceProgram
set_option autoImplicit false
noncomputable section
namespace NMX_Parameterized233
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_FullChildren
/-- Complete typed source fold. All child laws are at the exact command and
current world. This is an INTERMEDIATE theorem; ClosedPackets and the two
OPEN RowSpecs may not be retained as assumptions of a claimed row root. -/
theorem fold {W E : Type} (native model : Handler W E)
 (closed : ClosedPackets native model)
 (lane : RowSpec_217 native model) (registry : RowSpec_234 native model)
 (ops : Ops) (program : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey)
 (outputLane : U8) (slot : U64) (before : W) :
 eval native (NMX_SourceProgram.auth ops program accounts pool outputLane slot) before =
 eval model (NMX_SourceProgram.auth ops program accounts pool outputLane slot) before := by
 apply NMX_ProgramFold.congruence
 intro B cmd w
 cases cmd <;> first
 | exact lane _ _
 | exact registry _ _ _ _ _ _ _ _
 | exact closed _ _ (by simp only [NMX_FullChildren.IsOpen,not_false_eq_true])
#print fold
#print axioms fold
end NMX_Parameterized233
end
