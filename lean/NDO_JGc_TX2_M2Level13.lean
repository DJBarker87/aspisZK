import NDO_JGc_TX2_M2Level12
import NDO_JGc_TX2_M2H156
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input156 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash156.message
def value156 : State := JFp_SHADigest.output JGc_TX2_M2.Hash156.result
theorem cast156_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash156.B00.input).map Fin.val=JGc_TX2_M2.Hash156.B00.input := by rfl
#print axioms cast156_0
theorem tail156 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash156.tail).map Fin.val=JGc_TX2_M2.Hash156.tail := by rfl
#print axioms tail156
theorem numeric156 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash156.message).map Fin.val=JGc_TX2_M2.Hash156.message := by
  simp only [JGc_TX2_M2.Hash156.message,JGc_TX2_M2.Hash156.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast156_0,tail156]
#print axioms numeric156
theorem hash156 : JFp_SHADigest.digest input156=value156 := by
  unfold input156 JFp_SHADigest.digest
  rw [numeric156,JGc_TX2_M2.Hash156.checked]
  rfl
#print axioms hash156
theorem address156 : BinMerkle32Path.nodeInput (children value151 value152)=input156 := by rfl
#print axioms address156
def tree156 : Tree := .branch tree151 tree152
theorem root156 : root JFp_SHADigest.digest tree156=value156 := by
  rw [tree156,root,root151,root152]
  exact (congrArg JFp_SHADigest.digest address156).trans hash156
#print axioms root156
theorem shape156 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 0=tree156 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape151 f g inputs siblings]
  rw [shape152 f g inputs siblings]
  rfl
#print axioms shape156
def input157 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash157.message
def value157 : State := JFp_SHADigest.output JGc_TX2_M2.Hash157.result
theorem cast157_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash157.B00.input).map Fin.val=JGc_TX2_M2.Hash157.B00.input := by rfl
#print axioms cast157_0
theorem tail157 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash157.tail).map Fin.val=JGc_TX2_M2.Hash157.tail := by rfl
#print axioms tail157
theorem numeric157 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash157.message).map Fin.val=JGc_TX2_M2.Hash157.message := by
  simp only [JGc_TX2_M2.Hash157.message,JGc_TX2_M2.Hash157.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast157_0,tail157]
#print axioms numeric157
theorem hash157 : JFp_SHADigest.digest input157=value157 := by
  unfold input157 JFp_SHADigest.digest
  rw [numeric157,JGc_TX2_M2.Hash157.checked]
  rfl
#print axioms hash157
theorem address157 : BinMerkle32Path.nodeInput (children value153 value154)=input157 := by rfl
#print axioms address157
def tree157 : Tree := .branch tree153 tree154
theorem root157 : root JFp_SHADigest.digest tree157=value157 := by
  rw [tree157,root,root153,root154]
  exact (congrArg JFp_SHADigest.digest address157).trans hash157
#print axioms root157
theorem shape157 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 32768=tree157 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 32768)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape153 f g inputs siblings]
  rw [shape154 f g inputs siblings]
  rfl
#print axioms shape157
def input158 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash158.message
def value158 : State := JFp_SHADigest.output JGc_TX2_M2.Hash158.result
theorem cast158_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash158.B00.input).map Fin.val=JGc_TX2_M2.Hash158.B00.input := by rfl
#print axioms cast158_0
theorem tail158 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash158.tail).map Fin.val=JGc_TX2_M2.Hash158.tail := by rfl
#print axioms tail158
theorem numeric158 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash158.message).map Fin.val=JGc_TX2_M2.Hash158.message := by
  simp only [JGc_TX2_M2.Hash158.message,JGc_TX2_M2.Hash158.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast158_0,tail158]
#print axioms numeric158
theorem hash158 : JFp_SHADigest.digest input158=value158 := by
  unfold input158 JFp_SHADigest.digest
  rw [numeric158,JGc_TX2_M2.Hash158.checked]
  rfl
#print axioms hash158
theorem address158 : BinMerkle32Path.nodeInput (children value155 (JGc_TX2_HashBytes.state [106,68,94,34,200,155,227,56,14,109,54,154,223,75,246,156,164,96,202,178,139,180,29,27,104,175,115,251,85,57,235,119]))=input158 := by rfl
#print axioms address158
def tree158 : Tree := .branch tree155 (.supplied (JGc_TX2_HashBytes.state [106,68,94,34,200,155,227,56,14,109,54,154,223,75,246,156,164,96,202,178,139,180,29,27,104,175,115,251,85,57,235,119]))
theorem root158 : root JFp_SHADigest.digest tree158=value158 := by
  rw [tree158,root,root155]
  exact (congrArg JFp_SHADigest.digest address158).trans hash158
#print axioms root158
theorem shape158 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 49152=tree158 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 49152)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape155 f g inputs siblings]
  rw [unoccupied f g 13 57344 (by decide),siblings 13 (by decide) 57344 (by decide)]
  rfl
#print axioms shape158
end AspisR1.JGc_TX2_M2Roots
end
