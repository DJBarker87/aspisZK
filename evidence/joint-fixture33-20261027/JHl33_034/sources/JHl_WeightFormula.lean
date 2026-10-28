import JHl_Basis00
import JHl_Basis01
import JHl_Basis02
import JHl_Basis03
import JHl_Basis04
import JHl_Basis05
import JHl_Basis06
import JHl_Basis07
import JHl_Basis08
import JHl_Basis09
import JHk_RhsFacts
import JHl_SumField
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_WeightFormula
open Aeneas Aeneas.Std Result AspisR1Stage2
open AspisCircleTensorBinding
open JHl_SumField (value scalar)
def node (i : Fin 10) : U32 := match i.val with
  | 0 => JHl_Basis00.node
  | 1 => JHl_Basis01.node
  | 2 => JHl_Basis02.node
  | 3 => JHl_Basis03.node
  | 4 => JHl_Basis04.node
  | 5 => JHl_Basis05.node
  | 6 => JHl_Basis06.node
  | 7 => JHl_Basis07.node
  | 8 => JHl_Basis08.node
  | _ => JHl_Basis09.node

def contribution (i : Fin 10) (j : Nat) : JHl_SumField.K :=
  JHk_RhsFacts.power i.val*scalar (naturalLineValue (S7JoinBasisMachine.decode (node i)) j)

def prefix : Nat → Nat → JHl_SumField.K
  | 0,_ => 0
  | n+1,j => prefix n j+ (if h : n<10 then contribution ⟨n,h⟩ j else 0)

theorem advance (i : Fin 10) (j : Nat) : prefix (i.val+1) j=prefix i.val j+contribution i j := by
  rw [prefix,dif_pos i.isLt]
#print axioms advance

theorem node_call (i : Fin 10) : JFv_TX2_NodeCall.sourceCall (JGp_Rows.value i).lineZ=ok (node i) := by
  fin_cases i
  · exact JHl_Basis00.node_call
  · exact JHl_Basis01.node_call
  · exact JHl_Basis02.node_call
  · exact JHl_Basis03.node_call
  · exact JHl_Basis04.node_call
  · exact JHl_Basis05.node_call
  · exact JHl_Basis06.node_call
  · exact JHl_Basis07.node_call
  · exact JHl_Basis08.node_call
  · exact JHl_Basis09.node_call
#print axioms node_call
end AspisR1.JHl_WeightFormula
end
