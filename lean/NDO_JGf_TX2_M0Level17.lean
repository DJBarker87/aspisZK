import NDO_JGf_TX2_M0Level16
import NDO_JGf_TX2_M0W056
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGf_TX2_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input185 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash185.message
def value185 : State := JFp_SHADigest.output JGf_TX2_M0.Hash185.result
theorem cast185_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash185.B00.input).map Fin.val=JGf_TX2_M0.Hash185.B00.input := by rfl
#print axioms cast185_0
theorem tail185 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash185.tail).map Fin.val=JGf_TX2_M0.Hash185.tail := by rfl
#print axioms tail185
theorem numeric185 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash185.message).map Fin.val=JGf_TX2_M0.Hash185.message := by
  simp only [JGf_TX2_M0.Hash185.message,JGf_TX2_M0.Hash185.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast185_0,tail185]
#print axioms numeric185
theorem hash185 : JFp_SHADigest.digest input185=value185 := by
  unfold input185 JFp_SHADigest.digest
  rw [numeric185,JGf_TX2_M0.Hash185.checked]
  rfl
#print axioms hash185
theorem address185 : BinMerkle32Path.nodeInput (children value183 value184)=input185 := by rfl
#print axioms address185
def tree185 : Tree := .branch tree183 tree184
theorem root185 : root JFp_SHADigest.digest tree185=value185 := by
  rw [tree185,root,root183,root184]
  exact (congrArg JFp_SHADigest.digest address185).trans hash185
#print axioms root185
theorem shape185 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 18 0=tree185 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 18 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape183 f g inputs siblings]
  rw [shape184 f g inputs siblings]
  rfl
#print axioms shape185
end AspisR1.JGf_TX2_M0Roots
end
