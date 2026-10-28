import NDO_JHl_Basis00
import NDO_JHl_Basis01
import NDO_JHl_Basis02
import NDO_JHl_Basis03
import NDO_JHl_Basis04
import NDO_JHl_Basis05
import NDO_JHl_Basis06
import NDO_JHl_Basis07
import NDO_JHl_Basis08
import NDO_JHl_Basis09
import NDO_JHk_RhsFacts
import NDO_JHl_SumField
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

def totalAt : Nat → Nat → JHl_SumField.K
  | 0,_ => 0
  | n+1,j => totalAt n j+ (if h : n<10 then contribution ⟨n,h⟩ j else 0)

theorem advance (i : Fin 10) (j : Nat) : totalAt (i.val+1) j=totalAt i.val j+contribution i j := by
  rw [totalAt,dif_pos i.isLt]
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
