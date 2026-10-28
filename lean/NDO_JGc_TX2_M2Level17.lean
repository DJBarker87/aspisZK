import NDO_JGc_TX2_M2Level16
import NDO_JGc_TX2_M2H160
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input163 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash163.message
def value163 : State := JFp_SHADigest.output JGc_TX2_M2.Hash163.result
theorem cast163_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash163.B00.input).map Fin.val=JGc_TX2_M2.Hash163.B00.input := by rfl
#print axioms cast163_0
theorem tail163 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash163.tail).map Fin.val=JGc_TX2_M2.Hash163.tail := by rfl
#print axioms tail163
theorem numeric163 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash163.message).map Fin.val=JGc_TX2_M2.Hash163.message := by
  simp only [JGc_TX2_M2.Hash163.message,JGc_TX2_M2.Hash163.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast163_0,tail163]
#print axioms numeric163
theorem hash163 : JFp_SHADigest.digest input163=value163 := by
  unfold input163 JFp_SHADigest.digest
  rw [numeric163,JGc_TX2_M2.Hash163.checked]
  rfl
#print axioms hash163
theorem address163 : BinMerkle32Path.nodeInput (children value162 (JGc_TX2_HashBytes.state [220,196,233,115,158,7,124,8,46,188,36,235,198,156,139,68,223,130,204,114,37,155,16,71,174,150,102,35,254,100,134,80]))=input163 := by rfl
#print axioms address163
def tree163 : Tree := .branch tree162 (.supplied (JGc_TX2_HashBytes.state [220,196,233,115,158,7,124,8,46,188,36,235,198,156,139,68,223,130,204,114,37,155,16,71,174,150,102,35,254,100,134,80]))
theorem root163 : root JFp_SHADigest.digest tree163=value163 := by
  rw [tree163,root,root162]
  exact (congrArg JFp_SHADigest.digest address163).trans hash163
#print axioms root163
theorem shape163 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 18 0=tree163 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 18 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape162 f g inputs siblings]
  rw [unoccupied f g 17 131072 (by decide),siblings 17 (by decide) 131072 (by decide)]
  rfl
#print axioms shape163
end AspisR1.JGc_TX2_M2Roots
end
