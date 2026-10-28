import NDO_JGc_TX2_M2Level15
import NDO_JGc_TX2_M2H160
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input162 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash162.message
def value162 : State := JFp_SHADigest.output JGc_TX2_M2.Hash162.result
theorem cast162_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash162.B00.input).map Fin.val=JGc_TX2_M2.Hash162.B00.input := by rfl
#print axioms cast162_0
theorem tail162 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash162.tail).map Fin.val=JGc_TX2_M2.Hash162.tail := by rfl
#print axioms tail162
theorem numeric162 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash162.message).map Fin.val=JGc_TX2_M2.Hash162.message := by
  simp only [JGc_TX2_M2.Hash162.message,JGc_TX2_M2.Hash162.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast162_0,tail162]
#print axioms numeric162
theorem hash162 : JFp_SHADigest.digest input162=value162 := by
  unfold input162 JFp_SHADigest.digest
  rw [numeric162,JGc_TX2_M2.Hash162.checked]
  rfl
#print axioms hash162
theorem address162 : BinMerkle32Path.nodeInput (children value161 (JGc_TX2_HashBytes.state [128,179,167,189,122,81,88,173,23,97,55,49,163,83,67,138,131,227,2,149,136,117,239,125,58,69,31,115,134,136,165,136]))=input162 := by rfl
#print axioms address162
def tree162 : Tree := .branch tree161 (.supplied (JGc_TX2_HashBytes.state [128,179,167,189,122,81,88,173,23,97,55,49,163,83,67,138,131,227,2,149,136,117,239,125,58,69,31,115,134,136,165,136]))
theorem root162 : root JFp_SHADigest.digest tree162=value162 := by
  rw [tree162,root,root161]
  exact (congrArg JFp_SHADigest.digest address162).trans hash162
#print axioms root162
theorem shape162 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 17 0=tree162 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 17 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape161 f g inputs siblings]
  rw [unoccupied f g 16 65536 (by decide),siblings 16 (by decide) 65536 (by decide)]
  rfl
#print axioms shape162
end AspisR1.JGc_TX2_M2Roots
end
