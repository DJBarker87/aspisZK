import NDO_JGh_TX2_M1Level13
import NDO_JGh_TX2_M1W045
import NDO_JGh_TX2_M1W046
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input175 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash175.message
def value175 : State := JFp_SHADigest.output JGh_TX2_M1.Hash175.result
theorem cast175_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash175.B00.input).map Fin.val=JGh_TX2_M1.Hash175.B00.input := by rfl
#print axioms cast175_0
theorem tail175 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash175.tail).map Fin.val=JGh_TX2_M1.Hash175.tail := by rfl
#print axioms tail175
theorem numeric175 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash175.message).map Fin.val=JGh_TX2_M1.Hash175.message := by
  simp only [JGh_TX2_M1.Hash175.message,JGh_TX2_M1.Hash175.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast175_0,tail175]
#print axioms numeric175
theorem hash175 : JFp_SHADigest.digest input175=value175 := by
  unfold input175 JFp_SHADigest.digest
  rw [numeric175,JGh_TX2_M1.Hash175.checked]
  rfl
#print axioms hash175
theorem address175 : BinMerkle32Path.nodeInput (children value166 value167)=input175 := by rfl
#print axioms address175
def tree175 : Tree := .branch tree166 tree167
theorem root175 : root JFp_SHADigest.digest tree175=value175 := by
  rw [tree175,root,root166,root167]
  exact (congrArg JFp_SHADigest.digest address175).trans hash175
#print axioms root175
theorem shape175 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 15 0=tree175 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 15 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape166 f g inputs siblings]
  rw [shape167 f g inputs siblings]
  rfl
#print axioms shape175
def input176 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash176.message
def value176 : State := JFp_SHADigest.output JGh_TX2_M1.Hash176.result
theorem cast176_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash176.B00.input).map Fin.val=JGh_TX2_M1.Hash176.B00.input := by rfl
#print axioms cast176_0
theorem tail176 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash176.tail).map Fin.val=JGh_TX2_M1.Hash176.tail := by rfl
#print axioms tail176
theorem numeric176 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash176.message).map Fin.val=JGh_TX2_M1.Hash176.message := by
  simp only [JGh_TX2_M1.Hash176.message,JGh_TX2_M1.Hash176.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast176_0,tail176]
#print axioms numeric176
theorem hash176 : JFp_SHADigest.digest input176=value176 := by
  unfold input176 JFp_SHADigest.digest
  rw [numeric176,JGh_TX2_M1.Hash176.checked]
  rfl
#print axioms hash176
theorem address176 : BinMerkle32Path.nodeInput (children value168 value169)=input176 := by rfl
#print axioms address176
def tree176 : Tree := .branch tree168 tree169
theorem root176 : root JFp_SHADigest.digest tree176=value176 := by
  rw [tree176,root,root168,root169]
  exact (congrArg JFp_SHADigest.digest address176).trans hash176
#print axioms root176
theorem shape176 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 15 32768=tree176 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 15 32768)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape168 f g inputs siblings]
  rw [shape169 f g inputs siblings]
  rfl
#print axioms shape176
def input177 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash177.message
def value177 : State := JFp_SHADigest.output JGh_TX2_M1.Hash177.result
theorem cast177_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash177.B00.input).map Fin.val=JGh_TX2_M1.Hash177.B00.input := by rfl
#print axioms cast177_0
theorem tail177 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash177.tail).map Fin.val=JGh_TX2_M1.Hash177.tail := by rfl
#print axioms tail177
theorem numeric177 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash177.message).map Fin.val=JGh_TX2_M1.Hash177.message := by
  simp only [JGh_TX2_M1.Hash177.message,JGh_TX2_M1.Hash177.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast177_0,tail177]
#print axioms numeric177
theorem hash177 : JFp_SHADigest.digest input177=value177 := by
  unfold input177 JFp_SHADigest.digest
  rw [numeric177,JGh_TX2_M1.Hash177.checked]
  rfl
#print axioms hash177
theorem address177 : BinMerkle32Path.nodeInput (children value170 value171)=input177 := by rfl
#print axioms address177
def tree177 : Tree := .branch tree170 tree171
theorem root177 : root JFp_SHADigest.digest tree177=value177 := by
  rw [tree177,root,root170,root171]
  exact (congrArg JFp_SHADigest.digest address177).trans hash177
#print axioms root177
theorem shape177 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 15 131072=tree177 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 15 131072)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape170 f g inputs siblings]
  rw [shape171 f g inputs siblings]
  rfl
#print axioms shape177
def input178 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash178.message
def value178 : State := JFp_SHADigest.output JGh_TX2_M1.Hash178.result
theorem cast178_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash178.B00.input).map Fin.val=JGh_TX2_M1.Hash178.B00.input := by rfl
#print axioms cast178_0
theorem tail178 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash178.tail).map Fin.val=JGh_TX2_M1.Hash178.tail := by rfl
#print axioms tail178
theorem numeric178 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash178.message).map Fin.val=JGh_TX2_M1.Hash178.message := by
  simp only [JGh_TX2_M1.Hash178.message,JGh_TX2_M1.Hash178.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast178_0,tail178]
#print axioms numeric178
theorem hash178 : JFp_SHADigest.digest input178=value178 := by
  unfold input178 JFp_SHADigest.digest
  rw [numeric178,JGh_TX2_M1.Hash178.checked]
  rfl
#print axioms hash178
theorem address178 : BinMerkle32Path.nodeInput (children value172 value173)=input178 := by rfl
#print axioms address178
def tree178 : Tree := .branch tree172 tree173
theorem root178 : root JFp_SHADigest.digest tree178=value178 := by
  rw [tree178,root,root172,root173]
  exact (congrArg JFp_SHADigest.digest address178).trans hash178
#print axioms root178
theorem shape178 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 15 163840=tree178 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 15 163840)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape172 f g inputs siblings]
  rw [shape173 f g inputs siblings]
  rfl
#print axioms shape178
def input179 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash179.message
def value179 : State := JFp_SHADigest.output JGh_TX2_M1.Hash179.result
theorem cast179_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash179.B00.input).map Fin.val=JGh_TX2_M1.Hash179.B00.input := by rfl
#print axioms cast179_0
theorem tail179 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash179.tail).map Fin.val=JGh_TX2_M1.Hash179.tail := by rfl
#print axioms tail179
theorem numeric179 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash179.message).map Fin.val=JGh_TX2_M1.Hash179.message := by
  simp only [JGh_TX2_M1.Hash179.message,JGh_TX2_M1.Hash179.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast179_0,tail179]
#print axioms numeric179
theorem hash179 : JFp_SHADigest.digest input179=value179 := by
  unfold input179 JFp_SHADigest.digest
  rw [numeric179,JGh_TX2_M1.Hash179.checked]
  rfl
#print axioms hash179
theorem address179 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [94,141,123,142,16,86,40,121,91,237,183,116,254,58,142,124,219,39,123,41,165,187,42,68,243,146,139,31,5,160,3,117]) value174)=input179 := by rfl
#print axioms address179
def tree179 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [94,141,123,142,16,86,40,121,91,237,183,116,254,58,142,124,219,39,123,41,165,187,42,68,243,146,139,31,5,160,3,117])) tree174
theorem root179 : root JFp_SHADigest.digest tree179=value179 := by
  rw [tree179,root,root174]
  exact (congrArg JFp_SHADigest.digest address179).trans hash179
#print axioms root179
theorem shape179 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 15 196608=tree179 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 15 196608)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 14 196608 (by decide),siblings 14 (by decide) 196608 (by decide)]
  rw [shape174 f g inputs siblings]
  rfl
#print axioms shape179
end AspisR1.JGh_TX2_M1Roots
end
