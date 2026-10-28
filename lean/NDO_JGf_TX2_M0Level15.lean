import NDO_JGf_TX2_M0Level14
import NDO_JGf_TX2_M0W055
import NDO_JGf_TX2_M0W056
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGf_TX2_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input180 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash180.message
def value180 : State := JFp_SHADigest.output JGf_TX2_M0.Hash180.result
theorem cast180_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash180.B00.input).map Fin.val=JGf_TX2_M0.Hash180.B00.input := by rfl
#print axioms cast180_0
theorem tail180 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash180.tail).map Fin.val=JGf_TX2_M0.Hash180.tail := by rfl
#print axioms tail180
theorem numeric180 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash180.message).map Fin.val=JGf_TX2_M0.Hash180.message := by
  simp only [JGf_TX2_M0.Hash180.message,JGf_TX2_M0.Hash180.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast180_0,tail180]
#print axioms numeric180
theorem hash180 : JFp_SHADigest.digest input180=value180 := by
  unfold input180 JFp_SHADigest.digest
  rw [numeric180,JGf_TX2_M0.Hash180.checked]
  rfl
#print axioms hash180
theorem address180 : BinMerkle32Path.nodeInput (children value175 value176)=input180 := by rfl
#print axioms address180
def tree180 : Tree := .branch tree175 tree176
theorem root180 : root JFp_SHADigest.digest tree180=value180 := by
  rw [tree180,root,root175,root176]
  exact (congrArg JFp_SHADigest.digest address180).trans hash180
#print axioms root180
theorem shape180 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 16 0=tree180 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 16 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape175 f g inputs siblings]
  rw [shape176 f g inputs siblings]
  rfl
#print axioms shape180
def input181 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash181.message
def value181 : State := JFp_SHADigest.output JGf_TX2_M0.Hash181.result
theorem cast181_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash181.B00.input).map Fin.val=JGf_TX2_M0.Hash181.B00.input := by rfl
#print axioms cast181_0
theorem tail181 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash181.tail).map Fin.val=JGf_TX2_M0.Hash181.tail := by rfl
#print axioms tail181
theorem numeric181 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash181.message).map Fin.val=JGf_TX2_M0.Hash181.message := by
  simp only [JGf_TX2_M0.Hash181.message,JGf_TX2_M0.Hash181.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast181_0,tail181]
#print axioms numeric181
theorem hash181 : JFp_SHADigest.digest input181=value181 := by
  unfold input181 JFp_SHADigest.digest
  rw [numeric181,JGf_TX2_M0.Hash181.checked]
  rfl
#print axioms hash181
theorem address181 : BinMerkle32Path.nodeInput (children value177 value178)=input181 := by rfl
#print axioms address181
def tree181 : Tree := .branch tree177 tree178
theorem root181 : root JFp_SHADigest.digest tree181=value181 := by
  rw [tree181,root,root177,root178]
  exact (congrArg JFp_SHADigest.digest address181).trans hash181
#print axioms root181
theorem shape181 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 16 131072=tree181 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 16 131072)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape177 f g inputs siblings]
  rw [shape178 f g inputs siblings]
  rfl
#print axioms shape181
def input182 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash182.message
def value182 : State := JFp_SHADigest.output JGf_TX2_M0.Hash182.result
theorem cast182_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash182.B00.input).map Fin.val=JGf_TX2_M0.Hash182.B00.input := by rfl
#print axioms cast182_0
theorem tail182 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash182.tail).map Fin.val=JGf_TX2_M0.Hash182.tail := by rfl
#print axioms tail182
theorem numeric182 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash182.message).map Fin.val=JGf_TX2_M0.Hash182.message := by
  simp only [JGf_TX2_M0.Hash182.message,JGf_TX2_M0.Hash182.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast182_0,tail182]
#print axioms numeric182
theorem hash182 : JFp_SHADigest.digest input182=value182 := by
  unfold input182 JFp_SHADigest.digest
  rw [numeric182,JGf_TX2_M0.Hash182.checked]
  rfl
#print axioms hash182
theorem address182 : BinMerkle32Path.nodeInput (children value179 (JGc_TX2_HashBytes.state [78,76,78,145,83,145,125,165,149,199,20,232,15,8,165,94,236,114,212,6,118,28,230,173,255,46,190,216,0,213,150,249]))=input182 := by rfl
#print axioms address182
def tree182 : Tree := .branch tree179 (.supplied (JGc_TX2_HashBytes.state [78,76,78,145,83,145,125,165,149,199,20,232,15,8,165,94,236,114,212,6,118,28,230,173,255,46,190,216,0,213,150,249]))
theorem root182 : root JFp_SHADigest.digest tree182=value182 := by
  rw [tree182,root,root179]
  exact (congrArg JFp_SHADigest.digest address182).trans hash182
#print axioms root182
theorem shape182 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 16 196608=tree182 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 16 196608)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape179 f g inputs siblings]
  rw [unoccupied f g 15 229376 (by decide),siblings 15 (by decide) 229376 (by decide)]
  rfl
#print axioms shape182
end AspisR1.JGf_TX2_M0Roots
end
