import NDO_JGh_TX2_M1Level05
import NDO_JGh_TX2_M1W022
import NDO_JGh_TX2_M1W023
import NDO_JGh_TX2_M1W024
import NDO_JGh_TX2_M1W025
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input084 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash084.message
def value084 : State := JFp_SHADigest.output JGh_TX2_M1.Hash084.result
theorem cast084_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash084.B00.input).map Fin.val=JGh_TX2_M1.Hash084.B00.input := by rfl
#print axioms cast084_0
theorem tail084 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash084.tail).map Fin.val=JGh_TX2_M1.Hash084.tail := by rfl
#print axioms tail084
theorem numeric084 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash084.message).map Fin.val=JGh_TX2_M1.Hash084.message := by
  simp only [JGh_TX2_M1.Hash084.message,JGh_TX2_M1.Hash084.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast084_0,tail084]
#print axioms numeric084
theorem hash084 : JFp_SHADigest.digest input084=value084 := by
  unfold input084 JFp_SHADigest.digest
  rw [numeric084,JGh_TX2_M1.Hash084.checked]
  rfl
#print axioms hash084
theorem address084 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [5,14,141,90,169,39,53,83,83,142,81,208,146,23,21,216,91,232,81,120,231,229,168,131,104,135,53,201,168,191,194,47]) value072)=input084 := by rfl
#print axioms address084
def tree084 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [5,14,141,90,169,39,53,83,83,142,81,208,146,23,21,216,91,232,81,120,231,229,168,131,104,135,53,201,168,191,194,47])) tree072
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
def input085 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash085.message
def value085 : State := JFp_SHADigest.output JGh_TX2_M1.Hash085.result
theorem cast085_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash085.B00.input).map Fin.val=JGh_TX2_M1.Hash085.B00.input := by rfl
#print axioms cast085_0
theorem tail085 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash085.tail).map Fin.val=JGh_TX2_M1.Hash085.tail := by rfl
#print axioms tail085
theorem numeric085 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash085.message).map Fin.val=JGh_TX2_M1.Hash085.message := by
  simp only [JGh_TX2_M1.Hash085.message,JGh_TX2_M1.Hash085.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast085_0,tail085]
#print axioms numeric085
theorem hash085 : JFp_SHADigest.digest input085=value085 := by
  unfold input085 JFp_SHADigest.digest
  rw [numeric085,JGh_TX2_M1.Hash085.checked]
  rfl
#print axioms hash085
theorem address085 : BinMerkle32Path.nodeInput (children value073 (JGc_TX2_HashBytes.state [184,111,36,183,104,91,22,115,84,207,81,116,150,195,194,158,38,199,21,130,103,36,190,232,127,29,217,213,102,104,132,241]))=input085 := by rfl
#print axioms address085
def tree085 : Tree := .branch tree073 (.supplied (JGc_TX2_HashBytes.state [184,111,36,183,104,91,22,115,84,207,81,116,150,195,194,158,38,199,21,130,103,36,190,232,127,29,217,213,102,104,132,241]))
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
def input086 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash086.message
def value086 : State := JFp_SHADigest.output JGh_TX2_M1.Hash086.result
theorem cast086_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash086.B00.input).map Fin.val=JGh_TX2_M1.Hash086.B00.input := by rfl
#print axioms cast086_0
theorem tail086 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash086.tail).map Fin.val=JGh_TX2_M1.Hash086.tail := by rfl
#print axioms tail086
theorem numeric086 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash086.message).map Fin.val=JGh_TX2_M1.Hash086.message := by
  simp only [JGh_TX2_M1.Hash086.message,JGh_TX2_M1.Hash086.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast086_0,tail086]
#print axioms numeric086
theorem hash086 : JFp_SHADigest.digest input086=value086 := by
  unfold input086 JFp_SHADigest.digest
  rw [numeric086,JGh_TX2_M1.Hash086.checked]
  rfl
#print axioms hash086
theorem address086 : BinMerkle32Path.nodeInput (children value074 (JGc_TX2_HashBytes.state [153,177,65,71,52,128,250,203,189,12,49,80,141,229,145,210,198,229,202,31,188,162,195,192,31,215,14,0,126,110,162,251]))=input086 := by rfl
#print axioms address086
def tree086 : Tree := .branch tree074 (.supplied (JGc_TX2_HashBytes.state [153,177,65,71,52,128,250,203,189,12,49,80,141,229,145,210,198,229,202,31,188,162,195,192,31,215,14,0,126,110,162,251]))
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
def input087 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash087.message
def value087 : State := JFp_SHADigest.output JGh_TX2_M1.Hash087.result
theorem cast087_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash087.B00.input).map Fin.val=JGh_TX2_M1.Hash087.B00.input := by rfl
#print axioms cast087_0
theorem tail087 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash087.tail).map Fin.val=JGh_TX2_M1.Hash087.tail := by rfl
#print axioms tail087
theorem numeric087 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash087.message).map Fin.val=JGh_TX2_M1.Hash087.message := by
  simp only [JGh_TX2_M1.Hash087.message,JGh_TX2_M1.Hash087.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast087_0,tail087]
#print axioms numeric087
theorem hash087 : JFp_SHADigest.digest input087=value087 := by
  unfold input087 JFp_SHADigest.digest
  rw [numeric087,JGh_TX2_M1.Hash087.checked]
  rfl
#print axioms hash087
theorem address087 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [55,53,215,205,196,229,228,81,145,6,28,131,82,169,210,238,87,109,105,13,169,125,241,37,3,56,148,106,32,161,232,37]) value075)=input087 := by rfl
#print axioms address087
def tree087 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [55,53,215,205,196,229,228,81,145,6,28,131,82,169,210,238,87,109,105,13,169,125,241,37,3,56,148,106,32,161,232,37])) tree075
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
def input088 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash088.message
def value088 : State := JFp_SHADigest.output JGh_TX2_M1.Hash088.result
theorem cast088_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash088.B00.input).map Fin.val=JGh_TX2_M1.Hash088.B00.input := by rfl
#print axioms cast088_0
theorem tail088 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash088.tail).map Fin.val=JGh_TX2_M1.Hash088.tail := by rfl
#print axioms tail088
theorem numeric088 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash088.message).map Fin.val=JGh_TX2_M1.Hash088.message := by
  simp only [JGh_TX2_M1.Hash088.message,JGh_TX2_M1.Hash088.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast088_0,tail088]
#print axioms numeric088
theorem hash088 : JFp_SHADigest.digest input088=value088 := by
  unfold input088 JFp_SHADigest.digest
  rw [numeric088,JGh_TX2_M1.Hash088.checked]
  rfl
#print axioms hash088
theorem address088 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [6,3,24,53,73,183,202,184,64,100,52,173,74,76,36,231,30,127,112,238,69,229,58,35,76,128,165,168,59,82,19,143]) value076)=input088 := by rfl
#print axioms address088
def tree088 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [6,3,24,53,73,183,202,184,64,100,52,173,74,76,36,231,30,127,112,238,69,229,58,35,76,128,165,168,59,82,19,143])) tree076
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
def input089 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash089.message
def value089 : State := JFp_SHADigest.output JGh_TX2_M1.Hash089.result
theorem cast089_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash089.B00.input).map Fin.val=JGh_TX2_M1.Hash089.B00.input := by rfl
#print axioms cast089_0
theorem tail089 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash089.tail).map Fin.val=JGh_TX2_M1.Hash089.tail := by rfl
#print axioms tail089
theorem numeric089 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash089.message).map Fin.val=JGh_TX2_M1.Hash089.message := by
  simp only [JGh_TX2_M1.Hash089.message,JGh_TX2_M1.Hash089.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast089_0,tail089]
#print axioms numeric089
theorem hash089 : JFp_SHADigest.digest input089=value089 := by
  unfold input089 JFp_SHADigest.digest
  rw [numeric089,JGh_TX2_M1.Hash089.checked]
  rfl
#print axioms hash089
theorem address089 : BinMerkle32Path.nodeInput (children value077 (JGc_TX2_HashBytes.state [182,208,30,198,94,243,210,10,44,105,105,195,118,197,107,41,213,138,210,114,164,7,16,25,109,205,12,9,192,79,131,42]))=input089 := by rfl
#print axioms address089
def tree089 : Tree := .branch tree077 (.supplied (JGc_TX2_HashBytes.state [182,208,30,198,94,243,210,10,44,105,105,195,118,197,107,41,213,138,210,114,164,7,16,25,109,205,12,9,192,79,131,42]))
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
def input090 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash090.message
def value090 : State := JFp_SHADigest.output JGh_TX2_M1.Hash090.result
theorem cast090_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash090.B00.input).map Fin.val=JGh_TX2_M1.Hash090.B00.input := by rfl
#print axioms cast090_0
theorem tail090 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash090.tail).map Fin.val=JGh_TX2_M1.Hash090.tail := by rfl
#print axioms tail090
theorem numeric090 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash090.message).map Fin.val=JGh_TX2_M1.Hash090.message := by
  simp only [JGh_TX2_M1.Hash090.message,JGh_TX2_M1.Hash090.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast090_0,tail090]
#print axioms numeric090
theorem hash090 : JFp_SHADigest.digest input090=value090 := by
  unfold input090 JFp_SHADigest.digest
  rw [numeric090,JGh_TX2_M1.Hash090.checked]
  rfl
#print axioms hash090
theorem address090 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [156,230,140,61,84,248,80,66,2,44,182,101,147,148,190,86,151,50,143,164,104,178,90,105,127,41,40,98,219,204,233,208]) value078)=input090 := by rfl
#print axioms address090
def tree090 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [156,230,140,61,84,248,80,66,2,44,182,101,147,148,190,86,151,50,143,164,104,178,90,105,127,41,40,98,219,204,233,208])) tree078
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
def input091 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash091.message
def value091 : State := JFp_SHADigest.output JGh_TX2_M1.Hash091.result
theorem cast091_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash091.B00.input).map Fin.val=JGh_TX2_M1.Hash091.B00.input := by rfl
#print axioms cast091_0
theorem tail091 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash091.tail).map Fin.val=JGh_TX2_M1.Hash091.tail := by rfl
#print axioms tail091
theorem numeric091 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash091.message).map Fin.val=JGh_TX2_M1.Hash091.message := by
  simp only [JGh_TX2_M1.Hash091.message,JGh_TX2_M1.Hash091.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast091_0,tail091]
#print axioms numeric091
theorem hash091 : JFp_SHADigest.digest input091=value091 := by
  unfold input091 JFp_SHADigest.digest
  rw [numeric091,JGh_TX2_M1.Hash091.checked]
  rfl
#print axioms hash091
theorem address091 : BinMerkle32Path.nodeInput (children value079 (JGc_TX2_HashBytes.state [54,100,128,13,24,149,127,139,9,65,12,226,120,23,178,22,196,33,176,221,226,100,237,14,131,43,117,52,127,107,94,226]))=input091 := by rfl
#print axioms address091
def tree091 : Tree := .branch tree079 (.supplied (JGc_TX2_HashBytes.state [54,100,128,13,24,149,127,139,9,65,12,226,120,23,178,22,196,33,176,221,226,100,237,14,131,43,117,52,127,107,94,226]))
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
def input092 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash092.message
def value092 : State := JFp_SHADigest.output JGh_TX2_M1.Hash092.result
theorem cast092_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash092.B00.input).map Fin.val=JGh_TX2_M1.Hash092.B00.input := by rfl
#print axioms cast092_0
theorem tail092 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash092.tail).map Fin.val=JGh_TX2_M1.Hash092.tail := by rfl
#print axioms tail092
theorem numeric092 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash092.message).map Fin.val=JGh_TX2_M1.Hash092.message := by
  simp only [JGh_TX2_M1.Hash092.message,JGh_TX2_M1.Hash092.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast092_0,tail092]
#print axioms numeric092
theorem hash092 : JFp_SHADigest.digest input092=value092 := by
  unfold input092 JFp_SHADigest.digest
  rw [numeric092,JGh_TX2_M1.Hash092.checked]
  rfl
#print axioms hash092
theorem address092 : BinMerkle32Path.nodeInput (children value080 (JGc_TX2_HashBytes.state [149,218,98,173,65,74,136,31,78,43,246,179,253,13,41,169,136,128,238,86,77,188,190,151,31,19,131,60,219,216,14,8]))=input092 := by rfl
#print axioms address092
def tree092 : Tree := .branch tree080 (.supplied (JGc_TX2_HashBytes.state [149,218,98,173,65,74,136,31,78,43,246,179,253,13,41,169,136,128,238,86,77,188,190,151,31,19,131,60,219,216,14,8]))
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
def input093 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash093.message
def value093 : State := JFp_SHADigest.output JGh_TX2_M1.Hash093.result
theorem cast093_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash093.B00.input).map Fin.val=JGh_TX2_M1.Hash093.B00.input := by rfl
#print axioms cast093_0
theorem tail093 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash093.tail).map Fin.val=JGh_TX2_M1.Hash093.tail := by rfl
#print axioms tail093
theorem numeric093 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash093.message).map Fin.val=JGh_TX2_M1.Hash093.message := by
  simp only [JGh_TX2_M1.Hash093.message,JGh_TX2_M1.Hash093.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast093_0,tail093]
#print axioms numeric093
theorem hash093 : JFp_SHADigest.digest input093=value093 := by
  unfold input093 JFp_SHADigest.digest
  rw [numeric093,JGh_TX2_M1.Hash093.checked]
  rfl
#print axioms hash093
theorem address093 : BinMerkle32Path.nodeInput (children value081 (JGc_TX2_HashBytes.state [185,22,26,113,55,154,122,202,166,55,107,15,192,104,169,93,232,7,36,110,64,109,92,228,35,195,207,119,200,145,218,42]))=input093 := by rfl
#print axioms address093
def tree093 : Tree := .branch tree081 (.supplied (JGc_TX2_HashBytes.state [185,22,26,113,55,154,122,202,166,55,107,15,192,104,169,93,232,7,36,110,64,109,92,228,35,195,207,119,200,145,218,42]))
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
def input094 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash094.message
def value094 : State := JFp_SHADigest.output JGh_TX2_M1.Hash094.result
theorem cast094_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash094.B00.input).map Fin.val=JGh_TX2_M1.Hash094.B00.input := by rfl
#print axioms cast094_0
theorem tail094 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash094.tail).map Fin.val=JGh_TX2_M1.Hash094.tail := by rfl
#print axioms tail094
theorem numeric094 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash094.message).map Fin.val=JGh_TX2_M1.Hash094.message := by
  simp only [JGh_TX2_M1.Hash094.message,JGh_TX2_M1.Hash094.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast094_0,tail094]
#print axioms numeric094
theorem hash094 : JFp_SHADigest.digest input094=value094 := by
  unfold input094 JFp_SHADigest.digest
  rw [numeric094,JGh_TX2_M1.Hash094.checked]
  rfl
#print axioms hash094
theorem address094 : BinMerkle32Path.nodeInput (children value082 (JGc_TX2_HashBytes.state [1,22,169,204,229,7,149,73,247,171,17,240,135,153,232,96,139,106,201,197,27,100,247,82,26,95,83,98,253,103,75,161]))=input094 := by rfl
#print axioms address094
def tree094 : Tree := .branch tree082 (.supplied (JGc_TX2_HashBytes.state [1,22,169,204,229,7,149,73,247,171,17,240,135,153,232,96,139,106,201,197,27,100,247,82,26,95,83,98,253,103,75,161]))
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
def input095 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash095.message
def value095 : State := JFp_SHADigest.output JGh_TX2_M1.Hash095.result
theorem cast095_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash095.B00.input).map Fin.val=JGh_TX2_M1.Hash095.B00.input := by rfl
#print axioms cast095_0
theorem tail095 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash095.tail).map Fin.val=JGh_TX2_M1.Hash095.tail := by rfl
#print axioms tail095
theorem numeric095 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash095.message).map Fin.val=JGh_TX2_M1.Hash095.message := by
  simp only [JGh_TX2_M1.Hash095.message,JGh_TX2_M1.Hash095.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast095_0,tail095]
#print axioms numeric095
theorem hash095 : JFp_SHADigest.digest input095=value095 := by
  unfold input095 JFp_SHADigest.digest
  rw [numeric095,JGh_TX2_M1.Hash095.checked]
  rfl
#print axioms hash095
theorem address095 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [50,104,161,78,130,249,84,55,40,90,205,163,184,100,156,233,175,243,38,61,50,107,155,242,21,74,218,247,171,43,165,196]) value083)=input095 := by rfl
#print axioms address095
def tree095 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [50,104,161,78,130,249,84,55,40,90,205,163,184,100,156,233,175,243,38,61,50,107,155,242,21,74,218,247,171,43,165,196])) tree083
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
end AspisR1.JGh_TX2_M1Roots
end
