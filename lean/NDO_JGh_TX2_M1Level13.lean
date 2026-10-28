import NDO_JGh_TX2_M1Level12
import NDO_JGh_TX2_M1W043
import NDO_JGh_TX2_M1W044
import NDO_JGh_TX2_M1W045
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input166 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash166.message
def value166 : State := JFp_SHADigest.output JGh_TX2_M1.Hash166.result
theorem cast166_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash166.B00.input).map Fin.val=JGh_TX2_M1.Hash166.B00.input := by rfl
#print axioms cast166_0
theorem tail166 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash166.tail).map Fin.val=JGh_TX2_M1.Hash166.tail := by rfl
#print axioms tail166
theorem numeric166 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash166.message).map Fin.val=JGh_TX2_M1.Hash166.message := by
  simp only [JGh_TX2_M1.Hash166.message,JGh_TX2_M1.Hash166.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast166_0,tail166]
#print axioms numeric166
theorem hash166 : JFp_SHADigest.digest input166=value166 := by
  unfold input166 JFp_SHADigest.digest
  rw [numeric166,JGh_TX2_M1.Hash166.checked]
  rfl
#print axioms hash166
theorem address166 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [83,203,141,47,29,49,83,0,229,119,249,157,202,75,8,137,134,86,89,187,41,192,74,79,178,93,121,27,76,166,10,122]) value155)=input166 := by rfl
#print axioms address166
def tree166 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [83,203,141,47,29,49,83,0,229,119,249,157,202,75,8,137,134,86,89,187,41,192,74,79,178,93,121,27,76,166,10,122])) tree155
theorem root166 : root JFp_SHADigest.digest tree166=value166 := by
  rw [tree166,root,root155]
  exact (congrArg JFp_SHADigest.digest address166).trans hash166
#print axioms root166
theorem shape166 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 0=tree166 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 13 0 (by decide),siblings 13 (by decide) 0 (by decide)]
  rw [shape155 f g inputs siblings]
  rfl
#print axioms shape166
def input167 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash167.message
def value167 : State := JFp_SHADigest.output JGh_TX2_M1.Hash167.result
theorem cast167_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash167.B00.input).map Fin.val=JGh_TX2_M1.Hash167.B00.input := by rfl
#print axioms cast167_0
theorem tail167 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash167.tail).map Fin.val=JGh_TX2_M1.Hash167.tail := by rfl
#print axioms tail167
theorem numeric167 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash167.message).map Fin.val=JGh_TX2_M1.Hash167.message := by
  simp only [JGh_TX2_M1.Hash167.message,JGh_TX2_M1.Hash167.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast167_0,tail167]
#print axioms numeric167
theorem hash167 : JFp_SHADigest.digest input167=value167 := by
  unfold input167 JFp_SHADigest.digest
  rw [numeric167,JGh_TX2_M1.Hash167.checked]
  rfl
#print axioms hash167
theorem address167 : BinMerkle32Path.nodeInput (children value156 (JGc_TX2_HashBytes.state [196,221,2,183,23,248,133,73,8,51,42,147,161,96,75,209,207,56,209,208,20,232,101,7,108,174,79,78,94,219,127,125]))=input167 := by rfl
#print axioms address167
def tree167 : Tree := .branch tree156 (.supplied (JGc_TX2_HashBytes.state [196,221,2,183,23,248,133,73,8,51,42,147,161,96,75,209,207,56,209,208,20,232,101,7,108,174,79,78,94,219,127,125]))
theorem root167 : root JFp_SHADigest.digest tree167=value167 := by
  rw [tree167,root,root156]
  exact (congrArg JFp_SHADigest.digest address167).trans hash167
#print axioms root167
theorem shape167 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 16384=tree167 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 16384)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape156 f g inputs siblings]
  rw [unoccupied f g 13 24576 (by decide),siblings 13 (by decide) 24576 (by decide)]
  rfl
#print axioms shape167
def input168 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash168.message
def value168 : State := JFp_SHADigest.output JGh_TX2_M1.Hash168.result
theorem cast168_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash168.B00.input).map Fin.val=JGh_TX2_M1.Hash168.B00.input := by rfl
#print axioms cast168_0
theorem tail168 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash168.tail).map Fin.val=JGh_TX2_M1.Hash168.tail := by rfl
#print axioms tail168
theorem numeric168 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash168.message).map Fin.val=JGh_TX2_M1.Hash168.message := by
  simp only [JGh_TX2_M1.Hash168.message,JGh_TX2_M1.Hash168.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast168_0,tail168]
#print axioms numeric168
theorem hash168 : JFp_SHADigest.digest input168=value168 := by
  unfold input168 JFp_SHADigest.digest
  rw [numeric168,JGh_TX2_M1.Hash168.checked]
  rfl
#print axioms hash168
theorem address168 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [210,139,140,59,153,186,251,0,172,145,80,161,74,249,119,170,61,196,198,137,184,185,136,105,74,136,176,56,243,80,148,155]) value157)=input168 := by rfl
#print axioms address168
def tree168 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [210,139,140,59,153,186,251,0,172,145,80,161,74,249,119,170,61,196,198,137,184,185,136,105,74,136,176,56,243,80,148,155])) tree157
theorem root168 : root JFp_SHADigest.digest tree168=value168 := by
  rw [tree168,root,root157]
  exact (congrArg JFp_SHADigest.digest address168).trans hash168
#print axioms root168
theorem shape168 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 32768=tree168 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 32768)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 13 32768 (by decide),siblings 13 (by decide) 32768 (by decide)]
  rw [shape157 f g inputs siblings]
  rfl
#print axioms shape168
def input169 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash169.message
def value169 : State := JFp_SHADigest.output JGh_TX2_M1.Hash169.result
theorem cast169_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash169.B00.input).map Fin.val=JGh_TX2_M1.Hash169.B00.input := by rfl
#print axioms cast169_0
theorem tail169 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash169.tail).map Fin.val=JGh_TX2_M1.Hash169.tail := by rfl
#print axioms tail169
theorem numeric169 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash169.message).map Fin.val=JGh_TX2_M1.Hash169.message := by
  simp only [JGh_TX2_M1.Hash169.message,JGh_TX2_M1.Hash169.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast169_0,tail169]
#print axioms numeric169
theorem hash169 : JFp_SHADigest.digest input169=value169 := by
  unfold input169 JFp_SHADigest.digest
  rw [numeric169,JGh_TX2_M1.Hash169.checked]
  rfl
#print axioms hash169
theorem address169 : BinMerkle32Path.nodeInput (children value158 value159)=input169 := by rfl
#print axioms address169
def tree169 : Tree := .branch tree158 tree159
theorem root169 : root JFp_SHADigest.digest tree169=value169 := by
  rw [tree169,root,root158,root159]
  exact (congrArg JFp_SHADigest.digest address169).trans hash169
#print axioms root169
theorem shape169 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 49152=tree169 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 49152)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape158 f g inputs siblings]
  rw [shape159 f g inputs siblings]
  rfl
#print axioms shape169
def input170 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash170.message
def value170 : State := JFp_SHADigest.output JGh_TX2_M1.Hash170.result
theorem cast170_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash170.B00.input).map Fin.val=JGh_TX2_M1.Hash170.B00.input := by rfl
#print axioms cast170_0
theorem tail170 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash170.tail).map Fin.val=JGh_TX2_M1.Hash170.tail := by rfl
#print axioms tail170
theorem numeric170 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash170.message).map Fin.val=JGh_TX2_M1.Hash170.message := by
  simp only [JGh_TX2_M1.Hash170.message,JGh_TX2_M1.Hash170.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast170_0,tail170]
#print axioms numeric170
theorem hash170 : JFp_SHADigest.digest input170=value170 := by
  unfold input170 JFp_SHADigest.digest
  rw [numeric170,JGh_TX2_M1.Hash170.checked]
  rfl
#print axioms hash170
theorem address170 : BinMerkle32Path.nodeInput (children value160 (JGc_TX2_HashBytes.state [6,127,182,246,61,243,32,244,27,158,168,158,29,234,144,165,109,106,190,43,248,29,25,250,131,155,171,164,222,234,139,173]))=input170 := by rfl
#print axioms address170
def tree170 : Tree := .branch tree160 (.supplied (JGc_TX2_HashBytes.state [6,127,182,246,61,243,32,244,27,158,168,158,29,234,144,165,109,106,190,43,248,29,25,250,131,155,171,164,222,234,139,173]))
theorem root170 : root JFp_SHADigest.digest tree170=value170 := by
  rw [tree170,root,root160]
  exact (congrArg JFp_SHADigest.digest address170).trans hash170
#print axioms root170
theorem shape170 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 131072=tree170 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 131072)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape160 f g inputs siblings]
  rw [unoccupied f g 13 139264 (by decide),siblings 13 (by decide) 139264 (by decide)]
  rfl
#print axioms shape170
def input171 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash171.message
def value171 : State := JFp_SHADigest.output JGh_TX2_M1.Hash171.result
theorem cast171_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash171.B00.input).map Fin.val=JGh_TX2_M1.Hash171.B00.input := by rfl
#print axioms cast171_0
theorem tail171 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash171.tail).map Fin.val=JGh_TX2_M1.Hash171.tail := by rfl
#print axioms tail171
theorem numeric171 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash171.message).map Fin.val=JGh_TX2_M1.Hash171.message := by
  simp only [JGh_TX2_M1.Hash171.message,JGh_TX2_M1.Hash171.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast171_0,tail171]
#print axioms numeric171
theorem hash171 : JFp_SHADigest.digest input171=value171 := by
  unfold input171 JFp_SHADigest.digest
  rw [numeric171,JGh_TX2_M1.Hash171.checked]
  rfl
#print axioms hash171
theorem address171 : BinMerkle32Path.nodeInput (children value161 (JGc_TX2_HashBytes.state [117,86,123,7,186,122,67,234,65,160,231,60,37,157,151,54,110,85,27,160,149,14,29,168,187,145,252,114,94,219,94,177]))=input171 := by rfl
#print axioms address171
def tree171 : Tree := .branch tree161 (.supplied (JGc_TX2_HashBytes.state [117,86,123,7,186,122,67,234,65,160,231,60,37,157,151,54,110,85,27,160,149,14,29,168,187,145,252,114,94,219,94,177]))
theorem root171 : root JFp_SHADigest.digest tree171=value171 := by
  rw [tree171,root,root161]
  exact (congrArg JFp_SHADigest.digest address171).trans hash171
#print axioms root171
theorem shape171 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 147456=tree171 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 147456)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape161 f g inputs siblings]
  rw [unoccupied f g 13 155648 (by decide),siblings 13 (by decide) 155648 (by decide)]
  rfl
#print axioms shape171
def input172 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash172.message
def value172 : State := JFp_SHADigest.output JGh_TX2_M1.Hash172.result
theorem cast172_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash172.B00.input).map Fin.val=JGh_TX2_M1.Hash172.B00.input := by rfl
#print axioms cast172_0
theorem tail172 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash172.tail).map Fin.val=JGh_TX2_M1.Hash172.tail := by rfl
#print axioms tail172
theorem numeric172 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash172.message).map Fin.val=JGh_TX2_M1.Hash172.message := by
  simp only [JGh_TX2_M1.Hash172.message,JGh_TX2_M1.Hash172.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast172_0,tail172]
#print axioms numeric172
theorem hash172 : JFp_SHADigest.digest input172=value172 := by
  unfold input172 JFp_SHADigest.digest
  rw [numeric172,JGh_TX2_M1.Hash172.checked]
  rfl
#print axioms hash172
theorem address172 : BinMerkle32Path.nodeInput (children value162 value163)=input172 := by rfl
#print axioms address172
def tree172 : Tree := .branch tree162 tree163
theorem root172 : root JFp_SHADigest.digest tree172=value172 := by
  rw [tree172,root,root162,root163]
  exact (congrArg JFp_SHADigest.digest address172).trans hash172
#print axioms root172
theorem shape172 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 163840=tree172 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 163840)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape162 f g inputs siblings]
  rw [shape163 f g inputs siblings]
  rfl
#print axioms shape172
def input173 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash173.message
def value173 : State := JFp_SHADigest.output JGh_TX2_M1.Hash173.result
theorem cast173_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash173.B00.input).map Fin.val=JGh_TX2_M1.Hash173.B00.input := by rfl
#print axioms cast173_0
theorem tail173 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash173.tail).map Fin.val=JGh_TX2_M1.Hash173.tail := by rfl
#print axioms tail173
theorem numeric173 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash173.message).map Fin.val=JGh_TX2_M1.Hash173.message := by
  simp only [JGh_TX2_M1.Hash173.message,JGh_TX2_M1.Hash173.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast173_0,tail173]
#print axioms numeric173
theorem hash173 : JFp_SHADigest.digest input173=value173 := by
  unfold input173 JFp_SHADigest.digest
  rw [numeric173,JGh_TX2_M1.Hash173.checked]
  rfl
#print axioms hash173
theorem address173 : BinMerkle32Path.nodeInput (children value164 (JGc_TX2_HashBytes.state [78,12,25,15,184,19,27,72,56,190,63,8,79,60,29,195,83,19,70,161,110,125,134,153,240,82,199,75,98,153,166,251]))=input173 := by rfl
#print axioms address173
def tree173 : Tree := .branch tree164 (.supplied (JGc_TX2_HashBytes.state [78,12,25,15,184,19,27,72,56,190,63,8,79,60,29,195,83,19,70,161,110,125,134,153,240,82,199,75,98,153,166,251]))
theorem root173 : root JFp_SHADigest.digest tree173=value173 := by
  rw [tree173,root,root164]
  exact (congrArg JFp_SHADigest.digest address173).trans hash173
#print axioms root173
theorem shape173 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 180224=tree173 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 180224)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape164 f g inputs siblings]
  rw [unoccupied f g 13 188416 (by decide),siblings 13 (by decide) 188416 (by decide)]
  rfl
#print axioms shape173
def input174 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash174.message
def value174 : State := JFp_SHADigest.output JGh_TX2_M1.Hash174.result
theorem cast174_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash174.B00.input).map Fin.val=JGh_TX2_M1.Hash174.B00.input := by rfl
#print axioms cast174_0
theorem tail174 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash174.tail).map Fin.val=JGh_TX2_M1.Hash174.tail := by rfl
#print axioms tail174
theorem numeric174 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash174.message).map Fin.val=JGh_TX2_M1.Hash174.message := by
  simp only [JGh_TX2_M1.Hash174.message,JGh_TX2_M1.Hash174.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast174_0,tail174]
#print axioms numeric174
theorem hash174 : JFp_SHADigest.digest input174=value174 := by
  unfold input174 JFp_SHADigest.digest
  rw [numeric174,JGh_TX2_M1.Hash174.checked]
  rfl
#print axioms hash174
theorem address174 : BinMerkle32Path.nodeInput (children value165 (JGc_TX2_HashBytes.state [231,175,9,73,193,151,78,114,131,10,124,215,162,10,201,179,141,208,35,230,20,155,240,194,241,32,103,192,199,110,107,27]))=input174 := by rfl
#print axioms address174
def tree174 : Tree := .branch tree165 (.supplied (JGc_TX2_HashBytes.state [231,175,9,73,193,151,78,114,131,10,124,215,162,10,201,179,141,208,35,230,20,155,240,194,241,32,103,192,199,110,107,27]))
theorem root174 : root JFp_SHADigest.digest tree174=value174 := by
  rw [tree174,root,root165]
  exact (congrArg JFp_SHADigest.digest address174).trans hash174
#print axioms root174
theorem shape174 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 212992=tree174 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 212992)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape165 f g inputs siblings]
  rw [unoccupied f g 13 221184 (by decide),siblings 13 (by decide) 221184 (by decide)]
  rfl
#print axioms shape174
end AspisR1.JGh_TX2_M1Roots
end
