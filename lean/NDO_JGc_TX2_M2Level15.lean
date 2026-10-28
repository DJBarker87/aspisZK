import NDO_JGc_TX2_M2Level14
import NDO_JGc_TX2_M2H160
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input161 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash161.message
def value161 : State := JFp_SHADigest.output JGc_TX2_M2.Hash161.result
theorem cast161_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash161.B00.input).map Fin.val=JGc_TX2_M2.Hash161.B00.input := by rfl
#print axioms cast161_0
theorem tail161 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash161.tail).map Fin.val=JGc_TX2_M2.Hash161.tail := by rfl
#print axioms tail161
theorem numeric161 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash161.message).map Fin.val=JGc_TX2_M2.Hash161.message := by
  simp only [JGc_TX2_M2.Hash161.message,JGc_TX2_M2.Hash161.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast161_0,tail161]
#print axioms numeric161
theorem hash161 : JFp_SHADigest.digest input161=value161 := by
  unfold input161 JFp_SHADigest.digest
  rw [numeric161,JGc_TX2_M2.Hash161.checked]
  rfl
#print axioms hash161
theorem address161 : BinMerkle32Path.nodeInput (children value159 value160)=input161 := by rfl
#print axioms address161
def tree161 : Tree := .branch tree159 tree160
theorem root161 : root JFp_SHADigest.digest tree161=value161 := by
  rw [tree161,root,root159,root160]
  exact (congrArg JFp_SHADigest.digest address161).trans hash161
#print axioms root161
theorem shape161 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 16 0=tree161 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 16 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape159 f g inputs siblings]
  rw [shape160 f g inputs siblings]
  rfl
#print axioms shape161
end AspisR1.JGc_TX2_M2Roots
end
