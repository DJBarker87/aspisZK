import NDO_JGf_TX2_M0Level05
import NDO_JGf_TX2_M0W031
import NDO_JGf_TX2_M0W032
import NDO_JGf_TX2_M0W033
import NDO_JGf_TX2_M0W034
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGf_TX2_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input084 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash084.message
def value084 : State := JFp_SHADigest.output JGf_TX2_M0.Hash084.result
theorem cast084_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash084.B00.input).map Fin.val=JGf_TX2_M0.Hash084.B00.input := by rfl
#print axioms cast084_0
theorem tail084 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash084.tail).map Fin.val=JGf_TX2_M0.Hash084.tail := by rfl
#print axioms tail084
theorem numeric084 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash084.message).map Fin.val=JGf_TX2_M0.Hash084.message := by
  simp only [JGf_TX2_M0.Hash084.message,JGf_TX2_M0.Hash084.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast084_0,tail084]
#print axioms numeric084
theorem hash084 : JFp_SHADigest.digest input084=value084 := by
  unfold input084 JFp_SHADigest.digest
  rw [numeric084,JGf_TX2_M0.Hash084.checked]
  rfl
#print axioms hash084
theorem address084 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [123,49,231,25,124,46,138,88,170,132,171,108,66,107,228,170,126,49,86,142,143,68,113,157,108,61,37,32,116,24,176,247]) value072)=input084 := by rfl
#print axioms address084
def tree084 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [123,49,231,25,124,46,138,88,170,132,171,108,66,107,228,170,126,49,86,142,143,68,113,157,108,61,37,32,116,24,176,247])) tree072
theorem root084 : root JFp_SHADigest.digest tree084=value084 := by
  rw [tree084,root,root072]
  exact (congrArg JFp_SHADigest.digest address084).trans hash084
#print axioms root084
theorem shape084 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 14208=tree084 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 14208)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 14208 (by decide),siblings 6 (by decide) 14208 (by decide)]
  rw [shape072 f g inputs siblings]
  rfl
#print axioms shape084
def input085 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash085.message
def value085 : State := JFp_SHADigest.output JGf_TX2_M0.Hash085.result
theorem cast085_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash085.B00.input).map Fin.val=JGf_TX2_M0.Hash085.B00.input := by rfl
#print axioms cast085_0
theorem tail085 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash085.tail).map Fin.val=JGf_TX2_M0.Hash085.tail := by rfl
#print axioms tail085
theorem numeric085 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash085.message).map Fin.val=JGf_TX2_M0.Hash085.message := by
  simp only [JGf_TX2_M0.Hash085.message,JGf_TX2_M0.Hash085.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast085_0,tail085]
#print axioms numeric085
theorem hash085 : JFp_SHADigest.digest input085=value085 := by
  unfold input085 JFp_SHADigest.digest
  rw [numeric085,JGf_TX2_M0.Hash085.checked]
  rfl
#print axioms hash085
theorem address085 : BinMerkle32Path.nodeInput (children value073 (JGc_TX2_HashBytes.state [28,173,37,241,82,193,120,157,16,226,26,48,57,30,85,173,29,113,71,228,48,174,168,18,58,71,247,188,77,81,235,30]))=input085 := by rfl
#print axioms address085
def tree085 : Tree := .branch tree073 (.supplied (JGc_TX2_HashBytes.state [28,173,37,241,82,193,120,157,16,226,26,48,57,30,85,173,29,113,71,228,48,174,168,18,58,71,247,188,77,81,235,30]))
theorem root085 : root JFp_SHADigest.digest tree085=value085 := by
  rw [tree085,root,root073]
  exact (congrArg JFp_SHADigest.digest address085).trans hash085
#print axioms root085
theorem shape085 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 21248=tree085 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 21248)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape073 f g inputs siblings]
  rw [unoccupied f g 6 21312 (by decide),siblings 6 (by decide) 21312 (by decide)]
  rfl
#print axioms shape085
def input086 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash086.message
def value086 : State := JFp_SHADigest.output JGf_TX2_M0.Hash086.result
theorem cast086_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash086.B00.input).map Fin.val=JGf_TX2_M0.Hash086.B00.input := by rfl
#print axioms cast086_0
theorem tail086 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash086.tail).map Fin.val=JGf_TX2_M0.Hash086.tail := by rfl
#print axioms tail086
theorem numeric086 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash086.message).map Fin.val=JGf_TX2_M0.Hash086.message := by
  simp only [JGf_TX2_M0.Hash086.message,JGf_TX2_M0.Hash086.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast086_0,tail086]
#print axioms numeric086
theorem hash086 : JFp_SHADigest.digest input086=value086 := by
  unfold input086 JFp_SHADigest.digest
  rw [numeric086,JGf_TX2_M0.Hash086.checked]
  rfl
#print axioms hash086
theorem address086 : BinMerkle32Path.nodeInput (children value074 (JGc_TX2_HashBytes.state [14,77,9,24,47,85,156,213,8,56,205,195,118,142,95,123,184,95,176,47,133,240,66,83,48,142,152,246,97,226,253,27]))=input086 := by rfl
#print axioms address086
def tree086 : Tree := .branch tree074 (.supplied (JGc_TX2_HashBytes.state [14,77,9,24,47,85,156,213,8,56,205,195,118,142,95,123,184,95,176,47,133,240,66,83,48,142,152,246,97,226,253,27]))
theorem root086 : root JFp_SHADigest.digest tree086=value086 := by
  rw [tree086,root,root074]
  exact (congrArg JFp_SHADigest.digest address086).trans hash086
#print axioms root086
theorem shape086 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 42112=tree086 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 42112)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape074 f g inputs siblings]
  rw [unoccupied f g 6 42176 (by decide),siblings 6 (by decide) 42176 (by decide)]
  rfl
#print axioms shape086
def input087 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash087.message
def value087 : State := JFp_SHADigest.output JGf_TX2_M0.Hash087.result
theorem cast087_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash087.B00.input).map Fin.val=JGf_TX2_M0.Hash087.B00.input := by rfl
#print axioms cast087_0
theorem tail087 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash087.tail).map Fin.val=JGf_TX2_M0.Hash087.tail := by rfl
#print axioms tail087
theorem numeric087 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash087.message).map Fin.val=JGf_TX2_M0.Hash087.message := by
  simp only [JGf_TX2_M0.Hash087.message,JGf_TX2_M0.Hash087.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast087_0,tail087]
#print axioms numeric087
theorem hash087 : JFp_SHADigest.digest input087=value087 := by
  unfold input087 JFp_SHADigest.digest
  rw [numeric087,JGf_TX2_M0.Hash087.checked]
  rfl
#print axioms hash087
theorem address087 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [2,171,209,240,15,165,22,179,21,183,127,225,28,35,201,42,34,40,97,177,92,32,201,220,146,214,215,116,204,184,116,86]) value075)=input087 := by rfl
#print axioms address087
def tree087 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [2,171,209,240,15,165,22,179,21,183,127,225,28,35,201,42,34,40,97,177,92,32,201,220,146,214,215,116,204,184,116,86])) tree075
theorem root087 : root JFp_SHADigest.digest tree087=value087 := by
  rw [tree087,root,root075]
  exact (congrArg JFp_SHADigest.digest address087).trans hash087
#print axioms root087
theorem shape087 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 55296=tree087 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 55296)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 55296 (by decide),siblings 6 (by decide) 55296 (by decide)]
  rw [shape075 f g inputs siblings]
  rfl
#print axioms shape087
def input088 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash088.message
def value088 : State := JFp_SHADigest.output JGf_TX2_M0.Hash088.result
theorem cast088_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash088.B00.input).map Fin.val=JGf_TX2_M0.Hash088.B00.input := by rfl
#print axioms cast088_0
theorem tail088 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash088.tail).map Fin.val=JGf_TX2_M0.Hash088.tail := by rfl
#print axioms tail088
theorem numeric088 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash088.message).map Fin.val=JGf_TX2_M0.Hash088.message := by
  simp only [JGf_TX2_M0.Hash088.message,JGf_TX2_M0.Hash088.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast088_0,tail088]
#print axioms numeric088
theorem hash088 : JFp_SHADigest.digest input088=value088 := by
  unfold input088 JFp_SHADigest.digest
  rw [numeric088,JGf_TX2_M0.Hash088.checked]
  rfl
#print axioms hash088
theorem address088 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [169,153,97,232,104,73,88,127,42,189,30,67,83,150,237,221,8,1,100,235,54,130,199,216,220,102,198,221,164,69,40,183]) value076)=input088 := by rfl
#print axioms address088
def tree088 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [169,153,97,232,104,73,88,127,42,189,30,67,83,150,237,221,8,1,100,235,54,130,199,216,220,102,198,221,164,69,40,183])) tree076
theorem root088 : root JFp_SHADigest.digest tree088=value088 := by
  rw [tree088,root,root076]
  exact (congrArg JFp_SHADigest.digest address088).trans hash088
#print axioms root088
theorem shape088 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 63744=tree088 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 63744)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 63744 (by decide),siblings 6 (by decide) 63744 (by decide)]
  rw [shape076 f g inputs siblings]
  rfl
#print axioms shape088
def input089 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash089.message
def value089 : State := JFp_SHADigest.output JGf_TX2_M0.Hash089.result
theorem cast089_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash089.B00.input).map Fin.val=JGf_TX2_M0.Hash089.B00.input := by rfl
#print axioms cast089_0
theorem tail089 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash089.tail).map Fin.val=JGf_TX2_M0.Hash089.tail := by rfl
#print axioms tail089
theorem numeric089 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash089.message).map Fin.val=JGf_TX2_M0.Hash089.message := by
  simp only [JGf_TX2_M0.Hash089.message,JGf_TX2_M0.Hash089.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast089_0,tail089]
#print axioms numeric089
theorem hash089 : JFp_SHADigest.digest input089=value089 := by
  unfold input089 JFp_SHADigest.digest
  rw [numeric089,JGf_TX2_M0.Hash089.checked]
  rfl
#print axioms hash089
theorem address089 : BinMerkle32Path.nodeInput (children value077 (JGc_TX2_HashBytes.state [177,17,136,138,84,162,21,82,110,11,160,20,187,76,131,138,181,195,224,5,98,111,218,231,27,185,210,253,55,107,55,107]))=input089 := by rfl
#print axioms address089
def tree089 : Tree := .branch tree077 (.supplied (JGc_TX2_HashBytes.state [177,17,136,138,84,162,21,82,110,11,160,20,187,76,131,138,181,195,224,5,98,111,218,231,27,185,210,253,55,107,55,107]))
theorem root089 : root JFp_SHADigest.digest tree089=value089 := by
  rw [tree089,root,root077]
  exact (congrArg JFp_SHADigest.digest address089).trans hash089
#print axioms root089
theorem shape089 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 132352=tree089 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 132352)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape077 f g inputs siblings]
  rw [unoccupied f g 6 132416 (by decide),siblings 6 (by decide) 132416 (by decide)]
  rfl
#print axioms shape089
def input090 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash090.message
def value090 : State := JFp_SHADigest.output JGf_TX2_M0.Hash090.result
theorem cast090_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash090.B00.input).map Fin.val=JGf_TX2_M0.Hash090.B00.input := by rfl
#print axioms cast090_0
theorem tail090 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash090.tail).map Fin.val=JGf_TX2_M0.Hash090.tail := by rfl
#print axioms tail090
theorem numeric090 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash090.message).map Fin.val=JGf_TX2_M0.Hash090.message := by
  simp only [JGf_TX2_M0.Hash090.message,JGf_TX2_M0.Hash090.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast090_0,tail090]
#print axioms numeric090
theorem hash090 : JFp_SHADigest.digest input090=value090 := by
  unfold input090 JFp_SHADigest.digest
  rw [numeric090,JGf_TX2_M0.Hash090.checked]
  rfl
#print axioms hash090
theorem address090 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [70,24,169,9,54,222,54,24,12,184,245,232,177,52,145,35,24,195,97,116,255,150,201,184,244,96,199,198,150,234,198,227]) value078)=input090 := by rfl
#print axioms address090
def tree090 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [70,24,169,9,54,222,54,24,12,184,245,232,177,52,145,35,24,195,97,116,255,150,201,184,244,96,199,198,150,234,198,227])) tree078
theorem root090 : root JFp_SHADigest.digest tree090=value090 := by
  rw [tree090,root,root078]
  exact (congrArg JFp_SHADigest.digest address090).trans hash090
#print axioms root090
theorem shape090 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 149504=tree090 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 149504)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 149504 (by decide),siblings 6 (by decide) 149504 (by decide)]
  rw [shape078 f g inputs siblings]
  rfl
#print axioms shape090
def input091 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash091.message
def value091 : State := JFp_SHADigest.output JGf_TX2_M0.Hash091.result
theorem cast091_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash091.B00.input).map Fin.val=JGf_TX2_M0.Hash091.B00.input := by rfl
#print axioms cast091_0
theorem tail091 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash091.tail).map Fin.val=JGf_TX2_M0.Hash091.tail := by rfl
#print axioms tail091
theorem numeric091 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash091.message).map Fin.val=JGf_TX2_M0.Hash091.message := by
  simp only [JGf_TX2_M0.Hash091.message,JGf_TX2_M0.Hash091.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast091_0,tail091]
#print axioms numeric091
theorem hash091 : JFp_SHADigest.digest input091=value091 := by
  unfold input091 JFp_SHADigest.digest
  rw [numeric091,JGf_TX2_M0.Hash091.checked]
  rfl
#print axioms hash091
theorem address091 : BinMerkle32Path.nodeInput (children value079 (JGc_TX2_HashBytes.state [123,159,119,27,131,73,129,1,243,159,228,157,197,117,73,109,53,154,238,180,2,55,81,128,169,48,14,170,16,217,8,88]))=input091 := by rfl
#print axioms address091
def tree091 : Tree := .branch tree079 (.supplied (JGc_TX2_HashBytes.state [123,159,119,27,131,73,129,1,243,159,228,157,197,117,73,109,53,154,238,180,2,55,81,128,169,48,14,170,16,217,8,88]))
theorem root091 : root JFp_SHADigest.digest tree091=value091 := by
  rw [tree091,root,root079]
  exact (congrArg JFp_SHADigest.digest address091).trans hash091
#print axioms root091
theorem shape091 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 166144=tree091 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 166144)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape079 f g inputs siblings]
  rw [unoccupied f g 6 166208 (by decide),siblings 6 (by decide) 166208 (by decide)]
  rfl
#print axioms shape091
def input092 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash092.message
def value092 : State := JFp_SHADigest.output JGf_TX2_M0.Hash092.result
theorem cast092_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash092.B00.input).map Fin.val=JGf_TX2_M0.Hash092.B00.input := by rfl
#print axioms cast092_0
theorem tail092 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash092.tail).map Fin.val=JGf_TX2_M0.Hash092.tail := by rfl
#print axioms tail092
theorem numeric092 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash092.message).map Fin.val=JGf_TX2_M0.Hash092.message := by
  simp only [JGf_TX2_M0.Hash092.message,JGf_TX2_M0.Hash092.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast092_0,tail092]
#print axioms numeric092
theorem hash092 : JFp_SHADigest.digest input092=value092 := by
  unfold input092 JFp_SHADigest.digest
  rw [numeric092,JGf_TX2_M0.Hash092.checked]
  rfl
#print axioms hash092
theorem address092 : BinMerkle32Path.nodeInput (children value080 (JGc_TX2_HashBytes.state [25,246,166,187,178,241,115,122,197,69,93,82,27,227,1,109,82,4,4,216,167,131,16,216,253,33,13,31,228,184,241,56]))=input092 := by rfl
#print axioms address092
def tree092 : Tree := .branch tree080 (.supplied (JGc_TX2_HashBytes.state [25,246,166,187,178,241,115,122,197,69,93,82,27,227,1,109,82,4,4,216,167,131,16,216,253,33,13,31,228,184,241,56]))
theorem root092 : root JFp_SHADigest.digest tree092=value092 := by
  rw [tree092,root,root080]
  exact (congrArg JFp_SHADigest.digest address092).trans hash092
#print axioms root092
theorem shape092 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 178048=tree092 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 178048)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape080 f g inputs siblings]
  rw [unoccupied f g 6 178112 (by decide),siblings 6 (by decide) 178112 (by decide)]
  rfl
#print axioms shape092
def input093 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash093.message
def value093 : State := JFp_SHADigest.output JGf_TX2_M0.Hash093.result
theorem cast093_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash093.B00.input).map Fin.val=JGf_TX2_M0.Hash093.B00.input := by rfl
#print axioms cast093_0
theorem tail093 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash093.tail).map Fin.val=JGf_TX2_M0.Hash093.tail := by rfl
#print axioms tail093
theorem numeric093 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash093.message).map Fin.val=JGf_TX2_M0.Hash093.message := by
  simp only [JGf_TX2_M0.Hash093.message,JGf_TX2_M0.Hash093.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast093_0,tail093]
#print axioms numeric093
theorem hash093 : JFp_SHADigest.digest input093=value093 := by
  unfold input093 JFp_SHADigest.digest
  rw [numeric093,JGf_TX2_M0.Hash093.checked]
  rfl
#print axioms hash093
theorem address093 : BinMerkle32Path.nodeInput (children value081 (JGc_TX2_HashBytes.state [64,27,21,10,232,228,1,239,126,128,250,143,209,80,213,151,177,170,232,183,184,107,231,238,137,231,32,82,148,237,56,50]))=input093 := by rfl
#print axioms address093
def tree093 : Tree := .branch tree081 (.supplied (JGc_TX2_HashBytes.state [64,27,21,10,232,228,1,239,126,128,250,143,209,80,213,151,177,170,232,183,184,107,231,238,137,231,32,82,148,237,56,50]))
theorem root093 : root JFp_SHADigest.digest tree093=value093 := by
  rw [tree093,root,root081]
  exact (congrArg JFp_SHADigest.digest address093).trans hash093
#print axioms root093
theorem shape093 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 179584=tree093 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 179584)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape081 f g inputs siblings]
  rw [unoccupied f g 6 179648 (by decide),siblings 6 (by decide) 179648 (by decide)]
  rfl
#print axioms shape093
def input094 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash094.message
def value094 : State := JFp_SHADigest.output JGf_TX2_M0.Hash094.result
theorem cast094_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash094.B00.input).map Fin.val=JGf_TX2_M0.Hash094.B00.input := by rfl
#print axioms cast094_0
theorem tail094 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash094.tail).map Fin.val=JGf_TX2_M0.Hash094.tail := by rfl
#print axioms tail094
theorem numeric094 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash094.message).map Fin.val=JGf_TX2_M0.Hash094.message := by
  simp only [JGf_TX2_M0.Hash094.message,JGf_TX2_M0.Hash094.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast094_0,tail094]
#print axioms numeric094
theorem hash094 : JFp_SHADigest.digest input094=value094 := by
  unfold input094 JFp_SHADigest.digest
  rw [numeric094,JGf_TX2_M0.Hash094.checked]
  rfl
#print axioms hash094
theorem address094 : BinMerkle32Path.nodeInput (children value082 (JGc_TX2_HashBytes.state [156,81,83,246,128,62,144,103,23,139,168,54,132,189,254,143,203,83,128,139,28,2,150,61,243,203,91,239,63,80,99,61]))=input094 := by rfl
#print axioms address094
def tree094 : Tree := .branch tree082 (.supplied (JGc_TX2_HashBytes.state [156,81,83,246,128,62,144,103,23,139,168,54,132,189,254,143,203,83,128,139,28,2,150,61,243,203,91,239,63,80,99,61]))
theorem root094 : root JFp_SHADigest.digest tree094=value094 := by
  rw [tree094,root,root082]
  exact (congrArg JFp_SHADigest.digest address094).trans hash094
#print axioms root094
theorem shape094 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 185600=tree094 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 185600)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape082 f g inputs siblings]
  rw [unoccupied f g 6 185664 (by decide),siblings 6 (by decide) 185664 (by decide)]
  rfl
#print axioms shape094
def input095 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash095.message
def value095 : State := JFp_SHADigest.output JGf_TX2_M0.Hash095.result
theorem cast095_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash095.B00.input).map Fin.val=JGf_TX2_M0.Hash095.B00.input := by rfl
#print axioms cast095_0
theorem tail095 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash095.tail).map Fin.val=JGf_TX2_M0.Hash095.tail := by rfl
#print axioms tail095
theorem numeric095 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash095.message).map Fin.val=JGf_TX2_M0.Hash095.message := by
  simp only [JGf_TX2_M0.Hash095.message,JGf_TX2_M0.Hash095.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast095_0,tail095]
#print axioms numeric095
theorem hash095 : JFp_SHADigest.digest input095=value095 := by
  unfold input095 JFp_SHADigest.digest
  rw [numeric095,JGf_TX2_M0.Hash095.checked]
  rfl
#print axioms hash095
theorem address095 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [213,198,73,173,136,245,34,182,27,137,62,151,75,57,18,81,103,105,17,35,233,123,149,171,198,151,95,19,101,127,8,252]) value083)=input095 := by rfl
#print axioms address095
def tree095 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [213,198,73,173,136,245,34,182,27,137,62,151,75,57,18,81,103,105,17,35,233,123,149,171,198,151,95,19,101,127,8,252])) tree083
theorem root095 : root JFp_SHADigest.digest tree095=value095 := by
  rw [tree095,root,root083]
  exact (congrArg JFp_SHADigest.digest address095).trans hash095
#print axioms root095
theorem shape095 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 217984=tree095 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 217984)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 217984 (by decide),siblings 6 (by decide) 217984 (by decide)]
  rw [shape083 f g inputs siblings]
  rfl
#print axioms shape095
end AspisR1.JGf_TX2_M0Roots
end
