import NDO_JGc_TX2_M2Level11
import NDO_JGc_TX2_M2H148
import NDO_JGc_TX2_M2H152
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input151 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash151.message
def value151 : State := JFp_SHADigest.output JGc_TX2_M2.Hash151.result
theorem cast151_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash151.B00.input).map Fin.val=JGc_TX2_M2.Hash151.B00.input := by rfl
#print axioms cast151_0
theorem tail151 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash151.tail).map Fin.val=JGc_TX2_M2.Hash151.tail := by rfl
#print axioms tail151
theorem numeric151 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash151.message).map Fin.val=JGc_TX2_M2.Hash151.message := by
  simp only [JGc_TX2_M2.Hash151.message,JGc_TX2_M2.Hash151.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast151_0,tail151]
#print axioms numeric151
theorem hash151 : JFp_SHADigest.digest input151=value151 := by
  unfold input151 JFp_SHADigest.digest
  rw [numeric151,JGc_TX2_M2.Hash151.checked]
  rfl
#print axioms hash151
theorem address151 : BinMerkle32Path.nodeInput (children value142 value143)=input151 := by rfl
#print axioms address151
def tree151 : Tree := .branch tree142 tree143
theorem root151 : root JFp_SHADigest.digest tree151=value151 := by
  rw [tree151,root,root142,root143]
  exact (congrArg JFp_SHADigest.digest address151).trans hash151
#print axioms root151
theorem shape151 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 0=tree151 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape142 f g inputs siblings]
  rw [shape143 f g inputs siblings]
  rfl
#print axioms shape151
def input152 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash152.message
def value152 : State := JFp_SHADigest.output JGc_TX2_M2.Hash152.result
theorem cast152_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash152.B00.input).map Fin.val=JGc_TX2_M2.Hash152.B00.input := by rfl
#print axioms cast152_0
theorem tail152 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash152.tail).map Fin.val=JGc_TX2_M2.Hash152.tail := by rfl
#print axioms tail152
theorem numeric152 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash152.message).map Fin.val=JGc_TX2_M2.Hash152.message := by
  simp only [JGc_TX2_M2.Hash152.message,JGc_TX2_M2.Hash152.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast152_0,tail152]
#print axioms numeric152
theorem hash152 : JFp_SHADigest.digest input152=value152 := by
  unfold input152 JFp_SHADigest.digest
  rw [numeric152,JGc_TX2_M2.Hash152.checked]
  rfl
#print axioms hash152
theorem address152 : BinMerkle32Path.nodeInput (children value144 value145)=input152 := by rfl
#print axioms address152
def tree152 : Tree := .branch tree144 tree145
theorem root152 : root JFp_SHADigest.digest tree152=value152 := by
  rw [tree152,root,root144,root145]
  exact (congrArg JFp_SHADigest.digest address152).trans hash152
#print axioms root152
theorem shape152 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 8192=tree152 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 8192)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape144 f g inputs siblings]
  rw [shape145 f g inputs siblings]
  rfl
#print axioms shape152
def input153 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash153.message
def value153 : State := JFp_SHADigest.output JGc_TX2_M2.Hash153.result
theorem cast153_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash153.B00.input).map Fin.val=JGc_TX2_M2.Hash153.B00.input := by rfl
#print axioms cast153_0
theorem tail153 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash153.tail).map Fin.val=JGc_TX2_M2.Hash153.tail := by rfl
#print axioms tail153
theorem numeric153 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash153.message).map Fin.val=JGc_TX2_M2.Hash153.message := by
  simp only [JGc_TX2_M2.Hash153.message,JGc_TX2_M2.Hash153.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast153_0,tail153]
#print axioms numeric153
theorem hash153 : JFp_SHADigest.digest input153=value153 := by
  unfold input153 JFp_SHADigest.digest
  rw [numeric153,JGc_TX2_M2.Hash153.checked]
  rfl
#print axioms hash153
theorem address153 : BinMerkle32Path.nodeInput (children value146 value147)=input153 := by rfl
#print axioms address153
def tree153 : Tree := .branch tree146 tree147
theorem root153 : root JFp_SHADigest.digest tree153=value153 := by
  rw [tree153,root,root146,root147]
  exact (congrArg JFp_SHADigest.digest address153).trans hash153
#print axioms root153
theorem shape153 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 32768=tree153 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 32768)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape146 f g inputs siblings]
  rw [shape147 f g inputs siblings]
  rfl
#print axioms shape153
def input154 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash154.message
def value154 : State := JFp_SHADigest.output JGc_TX2_M2.Hash154.result
theorem cast154_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash154.B00.input).map Fin.val=JGc_TX2_M2.Hash154.B00.input := by rfl
#print axioms cast154_0
theorem tail154 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash154.tail).map Fin.val=JGc_TX2_M2.Hash154.tail := by rfl
#print axioms tail154
theorem numeric154 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash154.message).map Fin.val=JGc_TX2_M2.Hash154.message := by
  simp only [JGc_TX2_M2.Hash154.message,JGc_TX2_M2.Hash154.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast154_0,tail154]
#print axioms numeric154
theorem hash154 : JFp_SHADigest.digest input154=value154 := by
  unfold input154 JFp_SHADigest.digest
  rw [numeric154,JGc_TX2_M2.Hash154.checked]
  rfl
#print axioms hash154
theorem address154 : BinMerkle32Path.nodeInput (children value148 value149)=input154 := by rfl
#print axioms address154
def tree154 : Tree := .branch tree148 tree149
theorem root154 : root JFp_SHADigest.digest tree154=value154 := by
  rw [tree154,root,root148,root149]
  exact (congrArg JFp_SHADigest.digest address154).trans hash154
#print axioms root154
theorem shape154 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 40960=tree154 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 40960)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape148 f g inputs siblings]
  rw [shape149 f g inputs siblings]
  rfl
#print axioms shape154
def input155 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash155.message
def value155 : State := JFp_SHADigest.output JGc_TX2_M2.Hash155.result
theorem cast155_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash155.B00.input).map Fin.val=JGc_TX2_M2.Hash155.B00.input := by rfl
#print axioms cast155_0
theorem tail155 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash155.tail).map Fin.val=JGc_TX2_M2.Hash155.tail := by rfl
#print axioms tail155
theorem numeric155 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash155.message).map Fin.val=JGc_TX2_M2.Hash155.message := by
  simp only [JGc_TX2_M2.Hash155.message,JGc_TX2_M2.Hash155.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast155_0,tail155]
#print axioms numeric155
theorem hash155 : JFp_SHADigest.digest input155=value155 := by
  unfold input155 JFp_SHADigest.digest
  rw [numeric155,JGc_TX2_M2.Hash155.checked]
  rfl
#print axioms hash155
theorem address155 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [42,167,120,228,166,1,0,116,125,12,190,232,159,84,170,36,120,158,7,37,241,178,42,150,75,119,11,252,15,55,236,76]) value150)=input155 := by rfl
#print axioms address155
def tree155 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [42,167,120,228,166,1,0,116,125,12,190,232,159,84,170,36,120,158,7,37,241,178,42,150,75,119,11,252,15,55,236,76])) tree150
theorem root155 : root JFp_SHADigest.digest tree155=value155 := by
  rw [tree155,root,root150]
  exact (congrArg JFp_SHADigest.digest address155).trans hash155
#print axioms root155
theorem shape155 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 49152=tree155 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 49152)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 12 49152 (by decide),siblings 12 (by decide) 49152 (by decide)]
  rw [shape150 f g inputs siblings]
  rfl
#print axioms shape155
end AspisR1.JGc_TX2_M2Roots
end
