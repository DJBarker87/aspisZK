import NDO_JGc_TX2_M2Level13
import NDO_JGc_TX2_M2H156
import NDO_JGc_TX2_M2H160
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input159 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash159.message
def value159 : State := JFp_SHADigest.output JGc_TX2_M2.Hash159.result
theorem cast159_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash159.B00.input).map Fin.val=JGc_TX2_M2.Hash159.B00.input := by rfl
#print axioms cast159_0
theorem tail159 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash159.tail).map Fin.val=JGc_TX2_M2.Hash159.tail := by rfl
#print axioms tail159
theorem numeric159 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash159.message).map Fin.val=JGc_TX2_M2.Hash159.message := by
  simp only [JGc_TX2_M2.Hash159.message,JGc_TX2_M2.Hash159.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast159_0,tail159]
#print axioms numeric159
theorem hash159 : JFp_SHADigest.digest input159=value159 := by
  unfold input159 JFp_SHADigest.digest
  rw [numeric159,JGc_TX2_M2.Hash159.checked]
  rfl
#print axioms hash159
theorem address159 : BinMerkle32Path.nodeInput (children value156 (JGc_TX2_HashBytes.state [228,96,201,65,47,217,114,210,72,6,233,71,93,13,177,139,113,68,25,125,252,162,191,55,162,47,84,136,175,38,253,181]))=input159 := by rfl
#print axioms address159
def tree159 : Tree := .branch tree156 (.supplied (JGc_TX2_HashBytes.state [228,96,201,65,47,217,114,210,72,6,233,71,93,13,177,139,113,68,25,125,252,162,191,55,162,47,84,136,175,38,253,181]))
theorem root159 : root JFp_SHADigest.digest tree159=value159 := by
  rw [tree159,root,root156]
  exact (congrArg JFp_SHADigest.digest address159).trans hash159
#print axioms root159
theorem shape159 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 15 0=tree159 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 15 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape156 f g inputs siblings]
  rw [unoccupied f g 14 16384 (by decide),siblings 14 (by decide) 16384 (by decide)]
  rfl
#print axioms shape159
def input160 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash160.message
def value160 : State := JFp_SHADigest.output JGc_TX2_M2.Hash160.result
theorem cast160_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash160.B00.input).map Fin.val=JGc_TX2_M2.Hash160.B00.input := by rfl
#print axioms cast160_0
theorem tail160 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash160.tail).map Fin.val=JGc_TX2_M2.Hash160.tail := by rfl
#print axioms tail160
theorem numeric160 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash160.message).map Fin.val=JGc_TX2_M2.Hash160.message := by
  simp only [JGc_TX2_M2.Hash160.message,JGc_TX2_M2.Hash160.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast160_0,tail160]
#print axioms numeric160
theorem hash160 : JFp_SHADigest.digest input160=value160 := by
  unfold input160 JFp_SHADigest.digest
  rw [numeric160,JGc_TX2_M2.Hash160.checked]
  rfl
#print axioms hash160
theorem address160 : BinMerkle32Path.nodeInput (children value157 value158)=input160 := by rfl
#print axioms address160
def tree160 : Tree := .branch tree157 tree158
theorem root160 : root JFp_SHADigest.digest tree160=value160 := by
  rw [tree160,root,root157,root158]
  exact (congrArg JFp_SHADigest.digest address160).trans hash160
#print axioms root160
theorem shape160 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 15 32768=tree160 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 15 32768)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape157 f g inputs siblings]
  rw [shape158 f g inputs siblings]
  rfl
#print axioms shape160
end AspisR1.JGc_TX2_M2Roots
end
