import NDO_JGc_TX2_M2Level05
import NDO_JGc_TX2_M2H084
import NDO_JGc_TX2_M2H088
import NDO_JGc_TX2_M2H092
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input084 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash084.message
def value084 : State := JFp_SHADigest.output JGc_TX2_M2.Hash084.result
theorem cast084_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash084.B00.input).map Fin.val=JGc_TX2_M2.Hash084.B00.input := by rfl
#print axioms cast084_0
theorem tail084 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash084.tail).map Fin.val=JGc_TX2_M2.Hash084.tail := by rfl
#print axioms tail084
theorem numeric084 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash084.message).map Fin.val=JGc_TX2_M2.Hash084.message := by
  simp only [JGc_TX2_M2.Hash084.message,JGc_TX2_M2.Hash084.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast084_0,tail084]
#print axioms numeric084
theorem hash084 : JFp_SHADigest.digest input084=value084 := by
  unfold input084 JFp_SHADigest.digest
  rw [numeric084,JGc_TX2_M2.Hash084.checked]
  rfl
#print axioms hash084
theorem address084 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [172,67,137,129,63,172,213,184,246,140,203,189,136,215,89,220,185,230,208,158,18,177,217,98,222,72,135,93,172,40,32,160]) value072)=input084 := by rfl
#print axioms address084
def tree084 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [172,67,137,129,63,172,213,184,246,140,203,189,136,215,89,220,185,230,208,158,18,177,217,98,222,72,135,93,172,40,32,160])) tree072
theorem root084 : root JFp_SHADigest.digest tree084=value084 := by
  rw [tree084,root,root072]
  exact (congrArg JFp_SHADigest.digest address084).trans hash084
#print axioms root084
theorem shape084 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 3456=tree084 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 3456)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 3456 (by decide),siblings 6 (by decide) 3456 (by decide)]
  rw [shape072 f g inputs siblings]
  rfl
#print axioms shape084
def input085 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash085.message
def value085 : State := JFp_SHADigest.output JGc_TX2_M2.Hash085.result
theorem cast085_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash085.B00.input).map Fin.val=JGc_TX2_M2.Hash085.B00.input := by rfl
#print axioms cast085_0
theorem tail085 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash085.tail).map Fin.val=JGc_TX2_M2.Hash085.tail := by rfl
#print axioms tail085
theorem numeric085 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash085.message).map Fin.val=JGc_TX2_M2.Hash085.message := by
  simp only [JGc_TX2_M2.Hash085.message,JGc_TX2_M2.Hash085.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast085_0,tail085]
#print axioms numeric085
theorem hash085 : JFp_SHADigest.digest input085=value085 := by
  unfold input085 JFp_SHADigest.digest
  rw [numeric085,JGc_TX2_M2.Hash085.checked]
  rfl
#print axioms hash085
theorem address085 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [192,100,6,122,185,90,6,201,115,33,239,251,7,29,119,219,203,29,219,48,33,203,239,165,153,210,29,187,213,92,243,99]) value073)=input085 := by rfl
#print axioms address085
def tree085 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [192,100,6,122,185,90,6,201,115,33,239,251,7,29,119,219,203,29,219,48,33,203,239,165,153,210,29,187,213,92,243,99])) tree073
theorem root085 : root JFp_SHADigest.digest tree085=value085 := by
  rw [tree085,root,root073]
  exact (congrArg JFp_SHADigest.digest address085).trans hash085
#print axioms root085
theorem shape085 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 5248=tree085 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 5248)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 5248 (by decide),siblings 6 (by decide) 5248 (by decide)]
  rw [shape073 f g inputs siblings]
  rfl
#print axioms shape085
def input086 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash086.message
def value086 : State := JFp_SHADigest.output JGc_TX2_M2.Hash086.result
theorem cast086_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash086.B00.input).map Fin.val=JGc_TX2_M2.Hash086.B00.input := by rfl
#print axioms cast086_0
theorem tail086 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash086.tail).map Fin.val=JGc_TX2_M2.Hash086.tail := by rfl
#print axioms tail086
theorem numeric086 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash086.message).map Fin.val=JGc_TX2_M2.Hash086.message := by
  simp only [JGc_TX2_M2.Hash086.message,JGc_TX2_M2.Hash086.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast086_0,tail086]
#print axioms numeric086
theorem hash086 : JFp_SHADigest.digest input086=value086 := by
  unfold input086 JFp_SHADigest.digest
  rw [numeric086,JGc_TX2_M2.Hash086.checked]
  rfl
#print axioms hash086
theorem address086 : BinMerkle32Path.nodeInput (children value074 (JGc_TX2_HashBytes.state [160,29,86,39,155,246,138,139,59,225,193,197,98,181,170,87,251,47,4,91,110,122,32,141,127,177,72,246,75,220,36,248]))=input086 := by rfl
#print axioms address086
def tree086 : Tree := .branch tree074 (.supplied (JGc_TX2_HashBytes.state [160,29,86,39,155,246,138,139,59,225,193,197,98,181,170,87,251,47,4,91,110,122,32,141,127,177,72,246,75,220,36,248]))
theorem root086 : root JFp_SHADigest.digest tree086=value086 := by
  rw [tree086,root,root074]
  exact (congrArg JFp_SHADigest.digest address086).trans hash086
#print axioms root086
theorem shape086 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 10496=tree086 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 10496)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape074 f g inputs siblings]
  rw [unoccupied f g 6 10560 (by decide),siblings 6 (by decide) 10560 (by decide)]
  rfl
#print axioms shape086
def input087 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash087.message
def value087 : State := JFp_SHADigest.output JGc_TX2_M2.Hash087.result
theorem cast087_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash087.B00.input).map Fin.val=JGc_TX2_M2.Hash087.B00.input := by rfl
#print axioms cast087_0
theorem tail087 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash087.tail).map Fin.val=JGc_TX2_M2.Hash087.tail := by rfl
#print axioms tail087
theorem numeric087 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash087.message).map Fin.val=JGc_TX2_M2.Hash087.message := by
  simp only [JGc_TX2_M2.Hash087.message,JGc_TX2_M2.Hash087.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast087_0,tail087]
#print axioms numeric087
theorem hash087 : JFp_SHADigest.digest input087=value087 := by
  unfold input087 JFp_SHADigest.digest
  rw [numeric087,JGc_TX2_M2.Hash087.checked]
  rfl
#print axioms hash087
theorem address087 : BinMerkle32Path.nodeInput (children value075 (JGc_TX2_HashBytes.state [166,214,63,214,11,10,238,8,114,208,36,118,8,70,86,233,111,73,40,88,18,215,83,213,47,162,199,7,118,175,34,210]))=input087 := by rfl
#print axioms address087
def tree087 : Tree := .branch tree075 (.supplied (JGc_TX2_HashBytes.state [166,214,63,214,11,10,238,8,114,208,36,118,8,70,86,233,111,73,40,88,18,215,83,213,47,162,199,7,118,175,34,210]))
theorem root087 : root JFp_SHADigest.digest tree087=value087 := by
  rw [tree087,root,root075]
  exact (congrArg JFp_SHADigest.digest address087).trans hash087
#print axioms root087
theorem shape087 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 13824=tree087 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 13824)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape075 f g inputs siblings]
  rw [unoccupied f g 6 13888 (by decide),siblings 6 (by decide) 13888 (by decide)]
  rfl
#print axioms shape087
def input088 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash088.message
def value088 : State := JFp_SHADigest.output JGc_TX2_M2.Hash088.result
theorem cast088_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash088.B00.input).map Fin.val=JGc_TX2_M2.Hash088.B00.input := by rfl
#print axioms cast088_0
theorem tail088 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash088.tail).map Fin.val=JGc_TX2_M2.Hash088.tail := by rfl
#print axioms tail088
theorem numeric088 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash088.message).map Fin.val=JGc_TX2_M2.Hash088.message := by
  simp only [JGc_TX2_M2.Hash088.message,JGc_TX2_M2.Hash088.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast088_0,tail088]
#print axioms numeric088
theorem hash088 : JFp_SHADigest.digest input088=value088 := by
  unfold input088 JFp_SHADigest.digest
  rw [numeric088,JGc_TX2_M2.Hash088.checked]
  rfl
#print axioms hash088
theorem address088 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [30,61,92,235,182,187,57,4,63,191,154,138,172,134,38,222,106,62,228,28,131,136,27,9,126,38,80,228,211,133,248,231]) value076)=input088 := by rfl
#print axioms address088
def tree088 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [30,61,92,235,182,187,57,4,63,191,154,138,172,134,38,222,106,62,228,28,131,136,27,9,126,38,80,228,211,133,248,231])) tree076
theorem root088 : root JFp_SHADigest.digest tree088=value088 := by
  rw [tree088,root,root076]
  exact (congrArg JFp_SHADigest.digest address088).trans hash088
#print axioms root088
theorem shape088 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 15872=tree088 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 15872)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 15872 (by decide),siblings 6 (by decide) 15872 (by decide)]
  rw [shape076 f g inputs siblings]
  rfl
#print axioms shape088
def input089 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash089.message
def value089 : State := JFp_SHADigest.output JGc_TX2_M2.Hash089.result
theorem cast089_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash089.B00.input).map Fin.val=JGc_TX2_M2.Hash089.B00.input := by rfl
#print axioms cast089_0
theorem tail089 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash089.tail).map Fin.val=JGc_TX2_M2.Hash089.tail := by rfl
#print axioms tail089
theorem numeric089 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash089.message).map Fin.val=JGc_TX2_M2.Hash089.message := by
  simp only [JGc_TX2_M2.Hash089.message,JGc_TX2_M2.Hash089.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast089_0,tail089]
#print axioms numeric089
theorem hash089 : JFp_SHADigest.digest input089=value089 := by
  unfold input089 JFp_SHADigest.digest
  rw [numeric089,JGc_TX2_M2.Hash089.checked]
  rfl
#print axioms hash089
theorem address089 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [223,165,248,99,102,245,66,219,179,246,44,60,203,239,166,162,96,176,21,241,209,235,211,87,48,252,109,199,219,229,103,200]) value077)=input089 := by rfl
#print axioms address089
def tree089 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [223,165,248,99,102,245,66,219,179,246,44,60,203,239,166,162,96,176,21,241,209,235,211,87,48,252,109,199,219,229,103,200])) tree077
theorem root089 : root JFp_SHADigest.digest tree089=value089 := by
  rw [tree089,root,root077]
  exact (congrArg JFp_SHADigest.digest address089).trans hash089
#print axioms root089
theorem shape089 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 33024=tree089 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 33024)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 33024 (by decide),siblings 6 (by decide) 33024 (by decide)]
  rw [shape077 f g inputs siblings]
  rfl
#print axioms shape089
def input090 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash090.message
def value090 : State := JFp_SHADigest.output JGc_TX2_M2.Hash090.result
theorem cast090_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash090.B00.input).map Fin.val=JGc_TX2_M2.Hash090.B00.input := by rfl
#print axioms cast090_0
theorem tail090 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash090.tail).map Fin.val=JGc_TX2_M2.Hash090.tail := by rfl
#print axioms tail090
theorem numeric090 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash090.message).map Fin.val=JGc_TX2_M2.Hash090.message := by
  simp only [JGc_TX2_M2.Hash090.message,JGc_TX2_M2.Hash090.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast090_0,tail090]
#print axioms numeric090
theorem hash090 : JFp_SHADigest.digest input090=value090 := by
  unfold input090 JFp_SHADigest.digest
  rw [numeric090,JGc_TX2_M2.Hash090.checked]
  rfl
#print axioms hash090
theorem address090 : BinMerkle32Path.nodeInput (children value078 (JGc_TX2_HashBytes.state [198,62,134,252,113,214,123,111,76,28,128,123,190,175,101,40,132,7,35,191,80,154,161,188,17,46,52,203,135,65,166,112]))=input090 := by rfl
#print axioms address090
def tree090 : Tree := .branch tree078 (.supplied (JGc_TX2_HashBytes.state [198,62,134,252,113,214,123,111,76,28,128,123,190,175,101,40,132,7,35,191,80,154,161,188,17,46,52,203,135,65,166,112]))
theorem root090 : root JFp_SHADigest.digest tree090=value090 := by
  rw [tree090,root,root078]
  exact (congrArg JFp_SHADigest.digest address090).trans hash090
#print axioms root090
theorem shape090 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 37376=tree090 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 37376)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape078 f g inputs siblings]
  rw [unoccupied f g 6 37440 (by decide),siblings 6 (by decide) 37440 (by decide)]
  rfl
#print axioms shape090
def input091 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash091.message
def value091 : State := JFp_SHADigest.output JGc_TX2_M2.Hash091.result
theorem cast091_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash091.B00.input).map Fin.val=JGc_TX2_M2.Hash091.B00.input := by rfl
#print axioms cast091_0
theorem tail091 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash091.tail).map Fin.val=JGc_TX2_M2.Hash091.tail := by rfl
#print axioms tail091
theorem numeric091 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash091.message).map Fin.val=JGc_TX2_M2.Hash091.message := by
  simp only [JGc_TX2_M2.Hash091.message,JGc_TX2_M2.Hash091.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast091_0,tail091]
#print axioms numeric091
theorem hash091 : JFp_SHADigest.digest input091=value091 := by
  unfold input091 JFp_SHADigest.digest
  rw [numeric091,JGc_TX2_M2.Hash091.checked]
  rfl
#print axioms hash091
theorem address091 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [36,197,178,9,230,13,104,143,163,9,16,179,99,249,195,81,219,27,81,56,198,108,12,53,89,178,43,172,163,62,170,112]) value079)=input091 := by rfl
#print axioms address091
def tree091 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [36,197,178,9,230,13,104,143,163,9,16,179,99,249,195,81,219,27,81,56,198,108,12,53,89,178,43,172,163,62,170,112])) tree079
theorem root091 : root JFp_SHADigest.digest tree091=value091 := by
  rw [tree091,root,root079]
  exact (congrArg JFp_SHADigest.digest address091).trans hash091
#print axioms root091
theorem shape091 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 41472=tree091 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 41472)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 41472 (by decide),siblings 6 (by decide) 41472 (by decide)]
  rw [shape079 f g inputs siblings]
  rfl
#print axioms shape091
def input092 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash092.message
def value092 : State := JFp_SHADigest.output JGc_TX2_M2.Hash092.result
theorem cast092_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash092.B00.input).map Fin.val=JGc_TX2_M2.Hash092.B00.input := by rfl
#print axioms cast092_0
theorem tail092 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash092.tail).map Fin.val=JGc_TX2_M2.Hash092.tail := by rfl
#print axioms tail092
theorem numeric092 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash092.message).map Fin.val=JGc_TX2_M2.Hash092.message := by
  simp only [JGc_TX2_M2.Hash092.message,JGc_TX2_M2.Hash092.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast092_0,tail092]
#print axioms numeric092
theorem hash092 : JFp_SHADigest.digest input092=value092 := by
  unfold input092 JFp_SHADigest.digest
  rw [numeric092,JGc_TX2_M2.Hash092.checked]
  rfl
#print axioms hash092
theorem address092 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [22,236,166,67,21,215,141,209,71,132,132,197,43,37,138,88,199,164,115,143,69,63,202,239,219,4,159,98,48,77,237,83]) value080)=input092 := by rfl
#print axioms address092
def tree092 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [22,236,166,67,21,215,141,209,71,132,132,197,43,37,138,88,199,164,115,143,69,63,202,239,219,4,159,98,48,77,237,83])) tree080
theorem root092 : root JFp_SHADigest.digest tree092=value092 := by
  rw [tree092,root,root080]
  exact (congrArg JFp_SHADigest.digest address092).trans hash092
#print axioms root092
theorem shape092 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 44416=tree092 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 44416)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 44416 (by decide),siblings 6 (by decide) 44416 (by decide)]
  rw [shape080 f g inputs siblings]
  rfl
#print axioms shape092
def input093 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash093.message
def value093 : State := JFp_SHADigest.output JGc_TX2_M2.Hash093.result
theorem cast093_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash093.B00.input).map Fin.val=JGc_TX2_M2.Hash093.B00.input := by rfl
#print axioms cast093_0
theorem tail093 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash093.tail).map Fin.val=JGc_TX2_M2.Hash093.tail := by rfl
#print axioms tail093
theorem numeric093 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash093.message).map Fin.val=JGc_TX2_M2.Hash093.message := by
  simp only [JGc_TX2_M2.Hash093.message,JGc_TX2_M2.Hash093.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast093_0,tail093]
#print axioms numeric093
theorem hash093 : JFp_SHADigest.digest input093=value093 := by
  unfold input093 JFp_SHADigest.digest
  rw [numeric093,JGc_TX2_M2.Hash093.checked]
  rfl
#print axioms hash093
theorem address093 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [182,212,215,63,255,39,69,5,133,254,2,40,136,4,209,190,155,88,38,45,233,136,227,145,61,147,86,118,142,35,104,75]) value081)=input093 := by rfl
#print axioms address093
def tree093 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [182,212,215,63,255,39,69,5,133,254,2,40,136,4,209,190,155,88,38,45,233,136,227,145,61,147,86,118,142,35,104,75])) tree081
theorem root093 : root JFp_SHADigest.digest tree093=value093 := by
  rw [tree093,root,root081]
  exact (congrArg JFp_SHADigest.digest address093).trans hash093
#print axioms root093
theorem shape093 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 44800=tree093 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 44800)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 44800 (by decide),siblings 6 (by decide) 44800 (by decide)]
  rw [shape081 f g inputs siblings]
  rfl
#print axioms shape093
def input094 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash094.message
def value094 : State := JFp_SHADigest.output JGc_TX2_M2.Hash094.result
theorem cast094_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash094.B00.input).map Fin.val=JGc_TX2_M2.Hash094.B00.input := by rfl
#print axioms cast094_0
theorem tail094 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash094.tail).map Fin.val=JGc_TX2_M2.Hash094.tail := by rfl
#print axioms tail094
theorem numeric094 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash094.message).map Fin.val=JGc_TX2_M2.Hash094.message := by
  simp only [JGc_TX2_M2.Hash094.message,JGc_TX2_M2.Hash094.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast094_0,tail094]
#print axioms numeric094
theorem hash094 : JFp_SHADigest.digest input094=value094 := by
  unfold input094 JFp_SHADigest.digest
  rw [numeric094,JGc_TX2_M2.Hash094.checked]
  rfl
#print axioms hash094
theorem address094 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [221,190,144,37,250,148,161,205,45,236,191,55,74,22,137,113,22,102,151,155,29,24,36,48,178,187,189,138,113,62,215,119]) value082)=input094 := by rfl
#print axioms address094
def tree094 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [221,190,144,37,250,148,161,205,45,236,191,55,74,22,137,113,22,102,151,155,29,24,36,48,178,187,189,138,113,62,215,119])) tree082
theorem root094 : root JFp_SHADigest.digest tree094=value094 := by
  rw [tree094,root,root082]
  exact (congrArg JFp_SHADigest.digest address094).trans hash094
#print axioms root094
theorem shape094 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 46336=tree094 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 46336)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 46336 (by decide),siblings 6 (by decide) 46336 (by decide)]
  rw [shape082 f g inputs siblings]
  rfl
#print axioms shape094
def input095 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash095.message
def value095 : State := JFp_SHADigest.output JGc_TX2_M2.Hash095.result
theorem cast095_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash095.B00.input).map Fin.val=JGc_TX2_M2.Hash095.B00.input := by rfl
#print axioms cast095_0
theorem tail095 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash095.tail).map Fin.val=JGc_TX2_M2.Hash095.tail := by rfl
#print axioms tail095
theorem numeric095 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash095.message).map Fin.val=JGc_TX2_M2.Hash095.message := by
  simp only [JGc_TX2_M2.Hash095.message,JGc_TX2_M2.Hash095.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast095_0,tail095]
#print axioms numeric095
theorem hash095 : JFp_SHADigest.digest input095=value095 := by
  unfold input095 JFp_SHADigest.digest
  rw [numeric095,JGc_TX2_M2.Hash095.checked]
  rfl
#print axioms hash095
theorem address095 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [159,122,129,237,10,27,151,100,235,23,81,3,119,58,53,120,161,156,210,101,211,167,134,168,116,89,18,3,55,73,7,207]) value083)=input095 := by rfl
#print axioms address095
def tree095 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [159,122,129,237,10,27,151,100,235,23,81,3,119,58,53,120,161,156,210,101,211,167,134,168,116,89,18,3,55,73,7,207])) tree083
theorem root095 : root JFp_SHADigest.digest tree095=value095 := by
  rw [tree095,root,root083]
  exact (congrArg JFp_SHADigest.digest address095).trans hash095
#print axioms root095
theorem shape095 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 54400=tree095 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 54400)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 54400 (by decide),siblings 6 (by decide) 54400 (by decide)]
  rw [shape083 f g inputs siblings]
  rfl
#print axioms shape095
end AspisR1.JGc_TX2_M2Roots
end
