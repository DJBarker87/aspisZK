import NDO_JGf_TX2_M0Level15
import NDO_JGf_TX2_M0W056
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGf_TX2_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input183 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash183.message
def value183 : State := JFp_SHADigest.output JGf_TX2_M0.Hash183.result
theorem cast183_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash183.B00.input).map Fin.val=JGf_TX2_M0.Hash183.B00.input := by rfl
#print axioms cast183_0
theorem tail183 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash183.tail).map Fin.val=JGf_TX2_M0.Hash183.tail := by rfl
#print axioms tail183
theorem numeric183 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash183.message).map Fin.val=JGf_TX2_M0.Hash183.message := by
  simp only [JGf_TX2_M0.Hash183.message,JGf_TX2_M0.Hash183.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast183_0,tail183]
#print axioms numeric183
theorem hash183 : JFp_SHADigest.digest input183=value183 := by
  unfold input183 JFp_SHADigest.digest
  rw [numeric183,JGf_TX2_M0.Hash183.checked]
  rfl
#print axioms hash183
theorem address183 : BinMerkle32Path.nodeInput (children value180 (JGc_TX2_HashBytes.state [20,75,240,52,66,218,55,232,223,15,176,158,204,251,44,15,230,97,84,252,206,245,180,53,37,119,236,117,119,84,90,140]))=input183 := by rfl
#print axioms address183
def tree183 : Tree := .branch tree180 (.supplied (JGc_TX2_HashBytes.state [20,75,240,52,66,218,55,232,223,15,176,158,204,251,44,15,230,97,84,252,206,245,180,53,37,119,236,117,119,84,90,140]))
theorem root183 : root JFp_SHADigest.digest tree183=value183 := by
  rw [tree183,root,root180]
  exact (congrArg JFp_SHADigest.digest address183).trans hash183
#print axioms root183
theorem shape183 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 17 0=tree183 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 17 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape180 f g inputs siblings]
  rw [unoccupied f g 16 65536 (by decide),siblings 16 (by decide) 65536 (by decide)]
  rfl
#print axioms shape183
def input184 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash184.message
def value184 : State := JFp_SHADigest.output JGf_TX2_M0.Hash184.result
theorem cast184_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash184.B00.input).map Fin.val=JGf_TX2_M0.Hash184.B00.input := by rfl
#print axioms cast184_0
theorem tail184 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash184.tail).map Fin.val=JGf_TX2_M0.Hash184.tail := by rfl
#print axioms tail184
theorem numeric184 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash184.message).map Fin.val=JGf_TX2_M0.Hash184.message := by
  simp only [JGf_TX2_M0.Hash184.message,JGf_TX2_M0.Hash184.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast184_0,tail184]
#print axioms numeric184
theorem hash184 : JFp_SHADigest.digest input184=value184 := by
  unfold input184 JFp_SHADigest.digest
  rw [numeric184,JGf_TX2_M0.Hash184.checked]
  rfl
#print axioms hash184
theorem address184 : BinMerkle32Path.nodeInput (children value181 value182)=input184 := by rfl
#print axioms address184
def tree184 : Tree := .branch tree181 tree182
theorem root184 : root JFp_SHADigest.digest tree184=value184 := by
  rw [tree184,root,root181,root182]
  exact (congrArg JFp_SHADigest.digest address184).trans hash184
#print axioms root184
theorem shape184 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 17 131072=tree184 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 17 131072)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape181 f g inputs siblings]
  rw [shape182 f g inputs siblings]
  rfl
#print axioms shape184
end AspisR1.JGf_TX2_M0Roots
end
