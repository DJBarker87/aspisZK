import JGy_Tree2Part1
import JGc_TX2_M2Root
import JGy_Certs2_08
import JGy_Certs2_09
import JGy_Certs2_10
import JGe_View
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input100 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash100.message
def value100 : State := JFp_SHADigest.output JGy_Gr_M2.Hash100.result
theorem cast100_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash100.B00.input).map Fin.val=JGy_Gr_M2.Hash100.B00.input := by rfl
#print axioms cast100_0
theorem tail100 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash100.tail).map Fin.val=JGy_Gr_M2.Hash100.tail := by rfl
#print axioms tail100
theorem numeric100 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash100.message).map Fin.val=JGy_Gr_M2.Hash100.message := by
  simp only [JGy_Gr_M2.Hash100.message,JGy_Gr_M2.Hash100.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast100_0,tail100]
#print axioms numeric100
theorem hash100 : JFp_SHADigest.digest input100=value100 := by
  unfold input100 JFp_SHADigest.digest
  rw [numeric100,JGy_Gr_M2.Hash100.checked]
  rfl
#print axioms hash100
theorem address100 : BinMerkle32Path.nodeInput (children value090 (JGc_TX2_HashBytes.state [88,84,1,232,136,97,59,25,95,79,171,202,50,73,181,91,156,235,147,175,149,228,206,198,32,112,132,5,97,147,214,87]))=input100 := by rfl
#print axioms address100
def tree100 : Tree := .branch tree090 (.supplied (JGc_TX2_HashBytes.state [88,84,1,232,136,97,59,25,95,79,171,202,50,73,181,91,156,235,147,175,149,228,206,198,32,112,132,5,97,147,214,87]))
theorem root100 : root JFp_SHADigest.digest tree100=value100 := by
  rw [tree100,root,root090]
  exact (congrArg JFp_SHADigest.digest address100).trans hash100
#print axioms root100
theorem shape100 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 16384=tree100 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 16384)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape090 f g inputs siblings]
  rw [unoccupied f g 9 16896 (by decide),siblings 9 (by decide) 16896 (by decide)]
  rfl
#print axioms shape100
def input101 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash101.message
def value101 : State := JFp_SHADigest.output JGy_Gr_M2.Hash101.result
theorem cast101_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash101.B00.input).map Fin.val=JGy_Gr_M2.Hash101.B00.input := by rfl
#print axioms cast101_0
theorem tail101 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash101.tail).map Fin.val=JGy_Gr_M2.Hash101.tail := by rfl
#print axioms tail101
theorem numeric101 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash101.message).map Fin.val=JGy_Gr_M2.Hash101.message := by
  simp only [JGy_Gr_M2.Hash101.message,JGy_Gr_M2.Hash101.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast101_0,tail101]
#print axioms numeric101
theorem hash101 : JFp_SHADigest.digest input101=value101 := by
  unfold input101 JFp_SHADigest.digest
  rw [numeric101,JGy_Gr_M2.Hash101.checked]
  rfl
#print axioms hash101
theorem address101 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [49,215,205,0,167,207,189,105,41,234,95,241,207,36,58,176,15,198,248,69,205,13,124,207,197,169,58,105,168,219,95,167]) value091)=input101 := by rfl
#print axioms address101
def tree101 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [49,215,205,0,167,207,189,105,41,234,95,241,207,36,58,176,15,198,248,69,205,13,124,207,197,169,58,105,168,219,95,167])) tree091
theorem root101 : root JFp_SHADigest.digest tree101=value101 := by
  rw [tree101,root,root091]
  exact (congrArg JFp_SHADigest.digest address101).trans hash101
#print axioms root101
theorem shape101 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 22528=tree101 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 22528)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 9 22528 (by decide),siblings 9 (by decide) 22528 (by decide)]
  rw [shape091 f g inputs siblings]
  rfl
#print axioms shape101
def input102 : Bytes := JGc_TX2_M2Roots.input126
def value102 : State := JGc_TX2_M2Roots.value126
theorem hash102 : JFp_SHADigest.digest input102=value102 := JGc_TX2_M2Roots.hash126
#print axioms hash102
theorem address102 : BinMerkle32Path.nodeInput (children value092 (JGc_TX2_HashBytes.state [70,134,10,212,128,202,30,53,59,190,3,183,111,214,12,121,235,23,249,250,247,194,155,71,110,138,126,72,15,189,138,73]))=input102 := by rfl
#print axioms address102
def tree102 : Tree := .branch tree092 (.supplied (JGc_TX2_HashBytes.state [70,134,10,212,128,202,30,53,59,190,3,183,111,214,12,121,235,23,249,250,247,194,155,71,110,138,126,72,15,189,138,73]))
theorem root102 : root JFp_SHADigest.digest tree102=value102 := by
  rw [tree102,root,root092]
  exact (congrArg JFp_SHADigest.digest address102).trans hash102
#print axioms root102
theorem shape102 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 36864=tree102 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 36864)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape092 f g inputs siblings]
  rw [unoccupied f g 9 37376 (by decide),siblings 9 (by decide) 37376 (by decide)]
  rfl
#print axioms shape102
def input103 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash103.message
def value103 : State := JFp_SHADigest.output JGy_Gr_M2.Hash103.result
theorem cast103_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash103.B00.input).map Fin.val=JGy_Gr_M2.Hash103.B00.input := by rfl
#print axioms cast103_0
theorem tail103 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash103.tail).map Fin.val=JGy_Gr_M2.Hash103.tail := by rfl
#print axioms tail103
theorem numeric103 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash103.message).map Fin.val=JGy_Gr_M2.Hash103.message := by
  simp only [JGy_Gr_M2.Hash103.message,JGy_Gr_M2.Hash103.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast103_0,tail103]
#print axioms numeric103
theorem hash103 : JFp_SHADigest.digest input103=value103 := by
  unfold input103 JFp_SHADigest.digest
  rw [numeric103,JGy_Gr_M2.Hash103.checked]
  rfl
#print axioms hash103
theorem address103 : BinMerkle32Path.nodeInput (children value093 (JGc_TX2_HashBytes.state [10,39,97,221,95,35,17,150,57,128,55,20,176,218,99,160,138,81,221,206,84,83,87,98,113,139,232,155,109,200,172,130]))=input103 := by rfl
#print axioms address103
def tree103 : Tree := .branch tree093 (.supplied (JGc_TX2_HashBytes.state [10,39,97,221,95,35,17,150,57,128,55,20,176,218,99,160,138,81,221,206,84,83,87,98,113,139,232,155,109,200,172,130]))
theorem root103 : root JFp_SHADigest.digest tree103=value103 := by
  rw [tree103,root,root093]
  exact (congrArg JFp_SHADigest.digest address103).trans hash103
#print axioms root103
theorem shape103 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 39936=tree103 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 39936)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape093 f g inputs siblings]
  rw [unoccupied f g 9 40448 (by decide),siblings 9 (by decide) 40448 (by decide)]
  rfl
#print axioms shape103
def input104 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash104.message
def value104 : State := JFp_SHADigest.output JGy_Gr_M2.Hash104.result
theorem cast104_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash104.B00.input).map Fin.val=JGy_Gr_M2.Hash104.B00.input := by rfl
#print axioms cast104_0
theorem tail104 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash104.tail).map Fin.val=JGy_Gr_M2.Hash104.tail := by rfl
#print axioms tail104
theorem numeric104 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash104.message).map Fin.val=JGy_Gr_M2.Hash104.message := by
  simp only [JGy_Gr_M2.Hash104.message,JGy_Gr_M2.Hash104.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast104_0,tail104]
#print axioms numeric104
theorem hash104 : JFp_SHADigest.digest input104=value104 := by
  unfold input104 JFp_SHADigest.digest
  rw [numeric104,JGy_Gr_M2.Hash104.checked]
  rfl
#print axioms hash104
theorem address104 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [229,179,51,182,45,79,191,222,28,125,224,229,212,199,58,124,45,169,119,100,137,91,235,224,126,108,71,10,55,150,202,46]) value094)=input104 := by rfl
#print axioms address104
def tree104 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [229,179,51,182,45,79,191,222,28,125,224,229,212,199,58,124,45,169,119,100,137,91,235,224,126,108,71,10,55,150,202,46])) tree094
theorem root104 : root JFp_SHADigest.digest tree104=value104 := by
  rw [tree104,root,root094]
  exact (congrArg JFp_SHADigest.digest address104).trans hash104
#print axioms root104
theorem shape104 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 45056=tree104 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 45056)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 9 45056 (by decide),siblings 9 (by decide) 45056 (by decide)]
  rw [shape094 f g inputs siblings]
  rfl
#print axioms shape104
def input105 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash105.message
def value105 : State := JFp_SHADigest.output JGy_Gr_M2.Hash105.result
theorem cast105_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash105.B00.input).map Fin.val=JGy_Gr_M2.Hash105.B00.input := by rfl
#print axioms cast105_0
theorem tail105 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash105.tail).map Fin.val=JGy_Gr_M2.Hash105.tail := by rfl
#print axioms tail105
theorem numeric105 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash105.message).map Fin.val=JGy_Gr_M2.Hash105.message := by
  simp only [JGy_Gr_M2.Hash105.message,JGy_Gr_M2.Hash105.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast105_0,tail105]
#print axioms numeric105
theorem hash105 : JFp_SHADigest.digest input105=value105 := by
  unfold input105 JFp_SHADigest.digest
  rw [numeric105,JGy_Gr_M2.Hash105.checked]
  rfl
#print axioms hash105
theorem address105 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [225,153,52,213,21,109,19,130,233,62,120,171,84,78,8,150,137,100,130,111,192,224,128,194,151,56,130,138,66,53,217,85]) value095)=input105 := by rfl
#print axioms address105
def tree105 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [225,153,52,213,21,109,19,130,233,62,120,171,84,78,8,150,137,100,130,111,192,224,128,194,151,56,130,138,66,53,217,85])) tree095
theorem root105 : root JFp_SHADigest.digest tree105=value105 := by
  rw [tree105,root,root095]
  exact (congrArg JFp_SHADigest.digest address105).trans hash105
#print axioms root105
theorem shape105 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 47104=tree105 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 47104)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 9 47104 (by decide),siblings 9 (by decide) 47104 (by decide)]
  rw [shape095 f g inputs siblings]
  rfl
#print axioms shape105
def input106 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash106.message
def value106 : State := JFp_SHADigest.output JGy_Gr_M2.Hash106.result
theorem cast106_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash106.B00.input).map Fin.val=JGy_Gr_M2.Hash106.B00.input := by rfl
#print axioms cast106_0
theorem tail106 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash106.tail).map Fin.val=JGy_Gr_M2.Hash106.tail := by rfl
#print axioms tail106
theorem numeric106 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash106.message).map Fin.val=JGy_Gr_M2.Hash106.message := by
  simp only [JGy_Gr_M2.Hash106.message,JGy_Gr_M2.Hash106.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast106_0,tail106]
#print axioms numeric106
theorem hash106 : JFp_SHADigest.digest input106=value106 := by
  unfold input106 JFp_SHADigest.digest
  rw [numeric106,JGy_Gr_M2.Hash106.checked]
  rfl
#print axioms hash106
theorem address106 : BinMerkle32Path.nodeInput (children value096 (JGc_TX2_HashBytes.state [63,157,246,68,247,156,167,236,33,147,196,148,11,221,187,24,80,152,186,62,219,33,199,166,205,164,91,93,159,195,123,173]))=input106 := by rfl
#print axioms address106
def tree106 : Tree := .branch tree096 (.supplied (JGc_TX2_HashBytes.state [63,157,246,68,247,156,167,236,33,147,196,148,11,221,187,24,80,152,186,62,219,33,199,166,205,164,91,93,159,195,123,173]))
theorem root106 : root JFp_SHADigest.digest tree106=value106 := by
  rw [tree106,root,root096]
  exact (congrArg JFp_SHADigest.digest address106).trans hash106
#print axioms root106
theorem shape106 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 48128=tree106 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 48128)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape096 f g inputs siblings]
  rw [unoccupied f g 9 48640 (by decide),siblings 9 (by decide) 48640 (by decide)]
  rfl
#print axioms shape106
def input107 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash107.message
def value107 : State := JFp_SHADigest.output JGy_Gr_M2.Hash107.result
theorem cast107_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash107.B00.input).map Fin.val=JGy_Gr_M2.Hash107.B00.input := by rfl
#print axioms cast107_0
theorem tail107 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash107.tail).map Fin.val=JGy_Gr_M2.Hash107.tail := by rfl
#print axioms tail107
theorem numeric107 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash107.message).map Fin.val=JGy_Gr_M2.Hash107.message := by
  simp only [JGy_Gr_M2.Hash107.message,JGy_Gr_M2.Hash107.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast107_0,tail107]
#print axioms numeric107
theorem hash107 : JFp_SHADigest.digest input107=value107 := by
  unfold input107 JFp_SHADigest.digest
  rw [numeric107,JGy_Gr_M2.Hash107.checked]
  rfl
#print axioms hash107
theorem address107 : BinMerkle32Path.nodeInput (children value097 (JGc_TX2_HashBytes.state [248,231,68,50,25,138,85,185,211,224,168,58,116,149,74,89,192,55,189,210,248,227,32,87,12,111,89,138,56,159,211,246]))=input107 := by rfl
#print axioms address107
def tree107 : Tree := .branch tree097 (.supplied (JGc_TX2_HashBytes.state [248,231,68,50,25,138,85,185,211,224,168,58,116,149,74,89,192,55,189,210,248,227,32,87,12,111,89,138,56,159,211,246]))
theorem root107 : root JFp_SHADigest.digest tree107=value107 := by
  rw [tree107,root,root097]
  exact (congrArg JFp_SHADigest.digest address107).trans hash107
#print axioms root107
theorem shape107 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 52224=tree107 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 52224)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape097 f g inputs siblings]
  rw [unoccupied f g 9 52736 (by decide),siblings 9 (by decide) 52736 (by decide)]
  rfl
#print axioms shape107
def input108 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash108.message
def value108 : State := JFp_SHADigest.output JGy_Gr_M2.Hash108.result
theorem cast108_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash108.B00.input).map Fin.val=JGy_Gr_M2.Hash108.B00.input := by rfl
#print axioms cast108_0
theorem tail108 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash108.tail).map Fin.val=JGy_Gr_M2.Hash108.tail := by rfl
#print axioms tail108
theorem numeric108 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash108.message).map Fin.val=JGy_Gr_M2.Hash108.message := by
  simp only [JGy_Gr_M2.Hash108.message,JGy_Gr_M2.Hash108.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast108_0,tail108]
#print axioms numeric108
theorem hash108 : JFp_SHADigest.digest input108=value108 := by
  unfold input108 JFp_SHADigest.digest
  rw [numeric108,JGy_Gr_M2.Hash108.checked]
  rfl
#print axioms hash108
theorem address108 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [121,77,72,55,197,240,239,13,38,245,104,128,31,8,169,49,228,30,30,39,15,43,17,9,136,253,250,13,253,55,182,203]) value098)=input108 := by rfl
#print axioms address108
def tree108 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [121,77,72,55,197,240,239,13,38,245,104,128,31,8,169,49,228,30,30,39,15,43,17,9,136,253,250,13,253,55,182,203])) tree098
theorem root108 : root JFp_SHADigest.digest tree108=value108 := by
  rw [tree108,root,root098]
  exact (congrArg JFp_SHADigest.digest address108).trans hash108
#print axioms root108
theorem shape108 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 53248=tree108 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 53248)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 9 53248 (by decide),siblings 9 (by decide) 53248 (by decide)]
  rw [shape098 f g inputs siblings]
  rfl
#print axioms shape108
def input109 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash109.message
def value109 : State := JFp_SHADigest.output JGy_Gr_M2.Hash109.result
theorem cast109_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash109.B00.input).map Fin.val=JGy_Gr_M2.Hash109.B00.input := by rfl
#print axioms cast109_0
theorem tail109 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash109.tail).map Fin.val=JGy_Gr_M2.Hash109.tail := by rfl
#print axioms tail109
theorem numeric109 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash109.message).map Fin.val=JGy_Gr_M2.Hash109.message := by
  simp only [JGy_Gr_M2.Hash109.message,JGy_Gr_M2.Hash109.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast109_0,tail109]
#print axioms numeric109
theorem hash109 : JFp_SHADigest.digest input109=value109 := by
  unfold input109 JFp_SHADigest.digest
  rw [numeric109,JGy_Gr_M2.Hash109.checked]
  rfl
#print axioms hash109
theorem address109 : BinMerkle32Path.nodeInput (children value099 (JGc_TX2_HashBytes.state [3,74,103,5,105,99,91,75,105,84,175,69,235,21,94,73,167,83,99,16,155,139,147,0,108,111,209,105,20,221,143,245]))=input109 := by rfl
#print axioms address109
def tree109 : Tree := .branch tree099 (.supplied (JGc_TX2_HashBytes.state [3,74,103,5,105,99,91,75,105,84,175,69,235,21,94,73,167,83,99,16,155,139,147,0,108,111,209,105,20,221,143,245]))
theorem root109 : root JFp_SHADigest.digest tree109=value109 := by
  rw [tree109,root,root099]
  exact (congrArg JFp_SHADigest.digest address109).trans hash109
#print axioms root109
theorem shape109 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 61440=tree109 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 61440)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape099 f g inputs siblings]
  rw [unoccupied f g 9 61952 (by decide),siblings 9 (by decide) 61952 (by decide)]
  rfl
#print axioms shape109
end AspisR1.JGy_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input110 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash110.message
def value110 : State := JFp_SHADigest.output JGy_Gr_M2.Hash110.result
theorem cast110_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash110.B00.input).map Fin.val=JGy_Gr_M2.Hash110.B00.input := by rfl
#print axioms cast110_0
theorem tail110 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash110.tail).map Fin.val=JGy_Gr_M2.Hash110.tail := by rfl
#print axioms tail110
theorem numeric110 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash110.message).map Fin.val=JGy_Gr_M2.Hash110.message := by
  simp only [JGy_Gr_M2.Hash110.message,JGy_Gr_M2.Hash110.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast110_0,tail110]
#print axioms numeric110
theorem hash110 : JFp_SHADigest.digest input110=value110 := by
  unfold input110 JFp_SHADigest.digest
  rw [numeric110,JGy_Gr_M2.Hash110.checked]
  rfl
#print axioms hash110
theorem address110 : BinMerkle32Path.nodeInput (children value100 (JGc_TX2_HashBytes.state [59,119,73,169,22,234,180,231,182,173,95,170,28,240,254,211,36,169,197,26,155,126,34,120,70,14,2,233,116,165,77,238]))=input110 := by rfl
#print axioms address110
def tree110 : Tree := .branch tree100 (.supplied (JGc_TX2_HashBytes.state [59,119,73,169,22,234,180,231,182,173,95,170,28,240,254,211,36,169,197,26,155,126,34,120,70,14,2,233,116,165,77,238]))
theorem root110 : root JFp_SHADigest.digest tree110=value110 := by
  rw [tree110,root,root100]
  exact (congrArg JFp_SHADigest.digest address110).trans hash110
#print axioms root110
theorem shape110 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 16384=tree110 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 16384)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape100 f g inputs siblings]
  rw [unoccupied f g 10 17408 (by decide),siblings 10 (by decide) 17408 (by decide)]
  rfl
#print axioms shape110
def input111 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash111.message
def value111 : State := JFp_SHADigest.output JGy_Gr_M2.Hash111.result
theorem cast111_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash111.B00.input).map Fin.val=JGy_Gr_M2.Hash111.B00.input := by rfl
#print axioms cast111_0
theorem tail111 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash111.tail).map Fin.val=JGy_Gr_M2.Hash111.tail := by rfl
#print axioms tail111
theorem numeric111 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash111.message).map Fin.val=JGy_Gr_M2.Hash111.message := by
  simp only [JGy_Gr_M2.Hash111.message,JGy_Gr_M2.Hash111.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast111_0,tail111]
#print axioms numeric111
theorem hash111 : JFp_SHADigest.digest input111=value111 := by
  unfold input111 JFp_SHADigest.digest
  rw [numeric111,JGy_Gr_M2.Hash111.checked]
  rfl
#print axioms hash111
theorem address111 : BinMerkle32Path.nodeInput (children value101 (JGc_TX2_HashBytes.state [155,115,130,156,18,114,181,14,247,172,123,90,64,80,209,183,141,7,129,131,179,236,78,203,48,11,88,165,65,162,198,183]))=input111 := by rfl
#print axioms address111
def tree111 : Tree := .branch tree101 (.supplied (JGc_TX2_HashBytes.state [155,115,130,156,18,114,181,14,247,172,123,90,64,80,209,183,141,7,129,131,179,236,78,203,48,11,88,165,65,162,198,183]))
theorem root111 : root JFp_SHADigest.digest tree111=value111 := by
  rw [tree111,root,root101]
  exact (congrArg JFp_SHADigest.digest address111).trans hash111
#print axioms root111
theorem shape111 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 22528=tree111 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 22528)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape101 f g inputs siblings]
  rw [unoccupied f g 10 23552 (by decide),siblings 10 (by decide) 23552 (by decide)]
  rfl
#print axioms shape111
def input112 : Bytes := JGc_TX2_M2Roots.input137
def value112 : State := JGc_TX2_M2Roots.value137
theorem hash112 : JFp_SHADigest.digest input112=value112 := JGc_TX2_M2Roots.hash137
#print axioms hash112
theorem address112 : BinMerkle32Path.nodeInput (children value102 (JGc_TX2_HashBytes.state [233,55,27,237,249,242,100,244,152,233,196,144,235,235,188,45,24,60,248,32,79,165,176,201,186,138,207,29,188,87,191,26]))=input112 := by rfl
#print axioms address112
def tree112 : Tree := .branch tree102 (.supplied (JGc_TX2_HashBytes.state [233,55,27,237,249,242,100,244,152,233,196,144,235,235,188,45,24,60,248,32,79,165,176,201,186,138,207,29,188,87,191,26]))
theorem root112 : root JFp_SHADigest.digest tree112=value112 := by
  rw [tree112,root,root102]
  exact (congrArg JFp_SHADigest.digest address112).trans hash112
#print axioms root112
theorem shape112 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 36864=tree112 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 36864)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape102 f g inputs siblings]
  rw [unoccupied f g 10 37888 (by decide),siblings 10 (by decide) 37888 (by decide)]
  rfl
#print axioms shape112
def input113 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash113.message
def value113 : State := JFp_SHADigest.output JGy_Gr_M2.Hash113.result
theorem cast113_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash113.B00.input).map Fin.val=JGy_Gr_M2.Hash113.B00.input := by rfl
#print axioms cast113_0
theorem tail113 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash113.tail).map Fin.val=JGy_Gr_M2.Hash113.tail := by rfl
#print axioms tail113
theorem numeric113 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash113.message).map Fin.val=JGy_Gr_M2.Hash113.message := by
  simp only [JGy_Gr_M2.Hash113.message,JGy_Gr_M2.Hash113.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast113_0,tail113]
#print axioms numeric113
theorem hash113 : JFp_SHADigest.digest input113=value113 := by
  unfold input113 JFp_SHADigest.digest
  rw [numeric113,JGy_Gr_M2.Hash113.checked]
  rfl
#print axioms hash113
theorem address113 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [21,19,134,173,7,2,210,241,42,75,194,167,15,45,14,161,26,153,154,65,84,193,25,180,34,59,39,191,21,32,25,135]) value103)=input113 := by rfl
#print axioms address113
def tree113 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [21,19,134,173,7,2,210,241,42,75,194,167,15,45,14,161,26,153,154,65,84,193,25,180,34,59,39,191,21,32,25,135])) tree103
theorem root113 : root JFp_SHADigest.digest tree113=value113 := by
  rw [tree113,root,root103]
  exact (congrArg JFp_SHADigest.digest address113).trans hash113
#print axioms root113
theorem shape113 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 38912=tree113 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 38912)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 38912 (by decide),siblings 10 (by decide) 38912 (by decide)]
  rw [shape103 f g inputs siblings]
  rfl
#print axioms shape113
def input114 : Bytes := JGc_TX2_M2Roots.input140
def value114 : State := JGc_TX2_M2Roots.value140
theorem hash114 : JFp_SHADigest.digest input114=value114 := JGc_TX2_M2Roots.hash140
#print axioms hash114
theorem address114 : BinMerkle32Path.nodeInput (children value104 (JGc_TX2_HashBytes.state [186,104,47,209,122,14,221,153,173,57,67,129,86,66,66,233,32,56,115,230,42,38,98,22,111,235,154,246,230,200,89,9]))=input114 := by rfl
#print axioms address114
def tree114 : Tree := .branch tree104 (.supplied (JGc_TX2_HashBytes.state [186,104,47,209,122,14,221,153,173,57,67,129,86,66,66,233,32,56,115,230,42,38,98,22,111,235,154,246,230,200,89,9]))
theorem root114 : root JFp_SHADigest.digest tree114=value114 := by
  rw [tree114,root,root104]
  exact (congrArg JFp_SHADigest.digest address114).trans hash114
#print axioms root114
theorem shape114 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 45056=tree114 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 45056)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape104 f g inputs siblings]
  rw [unoccupied f g 10 46080 (by decide),siblings 10 (by decide) 46080 (by decide)]
  rfl
#print axioms shape114
def input115 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash115.message
def value115 : State := JFp_SHADigest.output JGy_Gr_M2.Hash115.result
theorem cast115_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash115.B00.input).map Fin.val=JGy_Gr_M2.Hash115.B00.input := by rfl
#print axioms cast115_0
theorem tail115 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash115.tail).map Fin.val=JGy_Gr_M2.Hash115.tail := by rfl
#print axioms tail115
theorem numeric115 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash115.message).map Fin.val=JGy_Gr_M2.Hash115.message := by
  simp only [JGy_Gr_M2.Hash115.message,JGy_Gr_M2.Hash115.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast115_0,tail115]
#print axioms numeric115
theorem hash115 : JFp_SHADigest.digest input115=value115 := by
  unfold input115 JFp_SHADigest.digest
  rw [numeric115,JGy_Gr_M2.Hash115.checked]
  rfl
#print axioms hash115
theorem address115 : BinMerkle32Path.nodeInput (children value105 value106)=input115 := by rfl
#print axioms address115
def tree115 : Tree := .branch tree105 tree106
theorem root115 : root JFp_SHADigest.digest tree115=value115 := by
  rw [tree115,root,root105,root106]
  exact (congrArg JFp_SHADigest.digest address115).trans hash115
#print axioms root115
theorem shape115 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 47104=tree115 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 47104)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape105 f g inputs siblings]
  rw [shape106 f g inputs siblings]
  rfl
#print axioms shape115
def input116 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash116.message
def value116 : State := JFp_SHADigest.output JGy_Gr_M2.Hash116.result
theorem cast116_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash116.B00.input).map Fin.val=JGy_Gr_M2.Hash116.B00.input := by rfl
#print axioms cast116_0
theorem tail116 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash116.tail).map Fin.val=JGy_Gr_M2.Hash116.tail := by rfl
#print axioms tail116
theorem numeric116 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash116.message).map Fin.val=JGy_Gr_M2.Hash116.message := by
  simp only [JGy_Gr_M2.Hash116.message,JGy_Gr_M2.Hash116.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast116_0,tail116]
#print axioms numeric116
theorem hash116 : JFp_SHADigest.digest input116=value116 := by
  unfold input116 JFp_SHADigest.digest
  rw [numeric116,JGy_Gr_M2.Hash116.checked]
  rfl
#print axioms hash116
theorem address116 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [160,11,21,231,220,161,4,194,145,32,85,167,167,102,254,212,177,251,97,177,99,36,215,15,114,51,84,17,30,107,226,151]) value107)=input116 := by rfl
#print axioms address116
def tree116 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [160,11,21,231,220,161,4,194,145,32,85,167,167,102,254,212,177,251,97,177,99,36,215,15,114,51,84,17,30,107,226,151])) tree107
theorem root116 : root JFp_SHADigest.digest tree116=value116 := by
  rw [tree116,root,root107]
  exact (congrArg JFp_SHADigest.digest address116).trans hash116
#print axioms root116
theorem shape116 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 51200=tree116 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 51200)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 51200 (by decide),siblings 10 (by decide) 51200 (by decide)]
  rw [shape107 f g inputs siblings]
  rfl
#print axioms shape116
def input117 : Bytes := JGc_TX2_M2Roots.input141
def value117 : State := JGc_TX2_M2Roots.value141
theorem hash117 : JFp_SHADigest.digest input117=value117 := JGc_TX2_M2Roots.hash141
#print axioms hash117
theorem address117 : BinMerkle32Path.nodeInput (children value108 (JGc_TX2_HashBytes.state [79,82,178,84,61,147,76,0,223,43,6,169,212,57,122,92,55,118,68,198,170,121,50,188,215,151,199,101,127,208,161,110]))=input117 := by rfl
#print axioms address117
def tree117 : Tree := .branch tree108 (.supplied (JGc_TX2_HashBytes.state [79,82,178,84,61,147,76,0,223,43,6,169,212,57,122,92,55,118,68,198,170,121,50,188,215,151,199,101,127,208,161,110]))
theorem root117 : root JFp_SHADigest.digest tree117=value117 := by
  rw [tree117,root,root108]
  exact (congrArg JFp_SHADigest.digest address117).trans hash117
#print axioms root117
theorem shape117 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 53248=tree117 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 53248)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape108 f g inputs siblings]
  rw [unoccupied f g 10 54272 (by decide),siblings 10 (by decide) 54272 (by decide)]
  rfl
#print axioms shape117
def input118 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash118.message
def value118 : State := JFp_SHADigest.output JGy_Gr_M2.Hash118.result
theorem cast118_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash118.B00.input).map Fin.val=JGy_Gr_M2.Hash118.B00.input := by rfl
#print axioms cast118_0
theorem tail118 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash118.tail).map Fin.val=JGy_Gr_M2.Hash118.tail := by rfl
#print axioms tail118
theorem numeric118 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash118.message).map Fin.val=JGy_Gr_M2.Hash118.message := by
  simp only [JGy_Gr_M2.Hash118.message,JGy_Gr_M2.Hash118.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast118_0,tail118]
#print axioms numeric118
theorem hash118 : JFp_SHADigest.digest input118=value118 := by
  unfold input118 JFp_SHADigest.digest
  rw [numeric118,JGy_Gr_M2.Hash118.checked]
  rfl
#print axioms hash118
theorem address118 : BinMerkle32Path.nodeInput (children value109 (JGc_TX2_HashBytes.state [113,199,16,24,52,72,40,241,79,147,76,57,246,194,155,42,154,10,38,24,158,221,37,151,184,52,224,109,73,38,75,31]))=input118 := by rfl
#print axioms address118
def tree118 : Tree := .branch tree109 (.supplied (JGc_TX2_HashBytes.state [113,199,16,24,52,72,40,241,79,147,76,57,246,194,155,42,154,10,38,24,158,221,37,151,184,52,224,109,73,38,75,31]))
theorem root118 : root JFp_SHADigest.digest tree118=value118 := by
  rw [tree118,root,root109]
  exact (congrArg JFp_SHADigest.digest address118).trans hash118
#print axioms root118
theorem shape118 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 61440=tree118 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 61440)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape109 f g inputs siblings]
  rw [unoccupied f g 10 62464 (by decide),siblings 10 (by decide) 62464 (by decide)]
  rfl
#print axioms shape118
end AspisR1.JGy_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input119 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash119.message
def value119 : State := JFp_SHADigest.output JGy_Gr_M2.Hash119.result
theorem cast119_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash119.B00.input).map Fin.val=JGy_Gr_M2.Hash119.B00.input := by rfl
#print axioms cast119_0
theorem tail119 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash119.tail).map Fin.val=JGy_Gr_M2.Hash119.tail := by rfl
#print axioms tail119
theorem numeric119 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash119.message).map Fin.val=JGy_Gr_M2.Hash119.message := by
  simp only [JGy_Gr_M2.Hash119.message,JGy_Gr_M2.Hash119.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast119_0,tail119]
#print axioms numeric119
theorem hash119 : JFp_SHADigest.digest input119=value119 := by
  unfold input119 JFp_SHADigest.digest
  rw [numeric119,JGy_Gr_M2.Hash119.checked]
  rfl
#print axioms hash119
theorem address119 : BinMerkle32Path.nodeInput (children value110 (JGc_TX2_HashBytes.state [170,153,117,5,67,73,116,195,9,13,223,78,171,169,18,95,110,140,91,37,34,17,55,253,160,219,151,107,246,215,123,234]))=input119 := by rfl
#print axioms address119
def tree119 : Tree := .branch tree110 (.supplied (JGc_TX2_HashBytes.state [170,153,117,5,67,73,116,195,9,13,223,78,171,169,18,95,110,140,91,37,34,17,55,253,160,219,151,107,246,215,123,234]))
theorem root119 : root JFp_SHADigest.digest tree119=value119 := by
  rw [tree119,root,root110]
  exact (congrArg JFp_SHADigest.digest address119).trans hash119
#print axioms root119
theorem shape119 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 16384=tree119 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 16384)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape110 f g inputs siblings]
  rw [unoccupied f g 11 18432 (by decide),siblings 11 (by decide) 18432 (by decide)]
  rfl
#print axioms shape119
def input120 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash120.message
def value120 : State := JFp_SHADigest.output JGy_Gr_M2.Hash120.result
theorem cast120_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash120.B00.input).map Fin.val=JGy_Gr_M2.Hash120.B00.input := by rfl
#print axioms cast120_0
theorem tail120 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash120.tail).map Fin.val=JGy_Gr_M2.Hash120.tail := by rfl
#print axioms tail120
theorem numeric120 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash120.message).map Fin.val=JGy_Gr_M2.Hash120.message := by
  simp only [JGy_Gr_M2.Hash120.message,JGy_Gr_M2.Hash120.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast120_0,tail120]
#print axioms numeric120
theorem hash120 : JFp_SHADigest.digest input120=value120 := by
  unfold input120 JFp_SHADigest.digest
  rw [numeric120,JGy_Gr_M2.Hash120.checked]
  rfl
#print axioms hash120
theorem address120 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [216,219,166,205,15,70,186,97,80,104,229,181,34,249,182,130,33,182,45,106,240,203,133,32,164,178,203,167,172,135,153,82]) value111)=input120 := by rfl
#print axioms address120
def tree120 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [216,219,166,205,15,70,186,97,80,104,229,181,34,249,182,130,33,182,45,106,240,203,133,32,164,178,203,167,172,135,153,82])) tree111
theorem root120 : root JFp_SHADigest.digest tree120=value120 := by
  rw [tree120,root,root111]
  exact (congrArg JFp_SHADigest.digest address120).trans hash120
#print axioms root120
theorem shape120 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 20480=tree120 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 20480)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 11 20480 (by decide),siblings 11 (by decide) 20480 (by decide)]
  rw [shape111 f g inputs siblings]
  rfl
#print axioms shape120
def input121 : Bytes := JGc_TX2_M2Roots.input147
def value121 : State := JGc_TX2_M2Roots.value147
theorem hash121 : JFp_SHADigest.digest input121=value121 := JGc_TX2_M2Roots.hash147
#print axioms hash121
theorem address121 : BinMerkle32Path.nodeInput (children value112 value113)=input121 := by rfl
#print axioms address121
def tree121 : Tree := .branch tree112 tree113
theorem root121 : root JFp_SHADigest.digest tree121=value121 := by
  rw [tree121,root,root112,root113]
  exact (congrArg JFp_SHADigest.digest address121).trans hash121
#print axioms root121
theorem shape121 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 36864=tree121 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 36864)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape112 f g inputs siblings]
  rw [shape113 f g inputs siblings]
  rfl
#print axioms shape121
def input122 : Bytes := JGc_TX2_M2Roots.input149
def value122 : State := JGc_TX2_M2Roots.value149
theorem hash122 : JFp_SHADigest.digest input122=value122 := JGc_TX2_M2Roots.hash149
#print axioms hash122
theorem address122 : BinMerkle32Path.nodeInput (children value114 value115)=input122 := by rfl
#print axioms address122
def tree122 : Tree := .branch tree114 tree115
theorem root122 : root JFp_SHADigest.digest tree122=value122 := by
  rw [tree122,root,root114,root115]
  exact (congrArg JFp_SHADigest.digest address122).trans hash122
#print axioms root122
theorem shape122 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 45056=tree122 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 45056)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape114 f g inputs siblings]
  rw [shape115 f g inputs siblings]
  rfl
#print axioms shape122
def input123 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash123.message
def value123 : State := JFp_SHADigest.output JGy_Gr_M2.Hash123.result
theorem cast123_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash123.B00.input).map Fin.val=JGy_Gr_M2.Hash123.B00.input := by rfl
#print axioms cast123_0
theorem tail123 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash123.tail).map Fin.val=JGy_Gr_M2.Hash123.tail := by rfl
#print axioms tail123
theorem numeric123 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash123.message).map Fin.val=JGy_Gr_M2.Hash123.message := by
  simp only [JGy_Gr_M2.Hash123.message,JGy_Gr_M2.Hash123.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast123_0,tail123]
#print axioms numeric123
theorem hash123 : JFp_SHADigest.digest input123=value123 := by
  unfold input123 JFp_SHADigest.digest
  rw [numeric123,JGy_Gr_M2.Hash123.checked]
  rfl
#print axioms hash123
theorem address123 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [60,65,38,140,93,216,131,203,27,50,149,248,16,182,251,250,174,83,223,189,145,180,153,159,227,187,210,101,127,209,224,34]) value116)=input123 := by rfl
#print axioms address123
def tree123 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [60,65,38,140,93,216,131,203,27,50,149,248,16,182,251,250,174,83,223,189,145,180,153,159,227,187,210,101,127,209,224,34])) tree116
theorem root123 : root JFp_SHADigest.digest tree123=value123 := by
  rw [tree123,root,root116]
  exact (congrArg JFp_SHADigest.digest address123).trans hash123
#print axioms root123
theorem shape123 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 49152=tree123 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 49152)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 11 49152 (by decide),siblings 11 (by decide) 49152 (by decide)]
  rw [shape116 f g inputs siblings]
  rfl
#print axioms shape123
def input124 : Bytes := JGc_TX2_M2Roots.input150
def value124 : State := JGc_TX2_M2Roots.value150
theorem hash124 : JFp_SHADigest.digest input124=value124 := JGc_TX2_M2Roots.hash150
#print axioms hash124
theorem address124 : BinMerkle32Path.nodeInput (children value117 (JGc_TX2_HashBytes.state [6,129,243,133,201,8,108,81,39,87,79,34,75,133,83,63,178,115,227,174,129,80,5,186,58,198,235,77,231,201,140,216]))=input124 := by rfl
#print axioms address124
def tree124 : Tree := .branch tree117 (.supplied (JGc_TX2_HashBytes.state [6,129,243,133,201,8,108,81,39,87,79,34,75,133,83,63,178,115,227,174,129,80,5,186,58,198,235,77,231,201,140,216]))
theorem root124 : root JFp_SHADigest.digest tree124=value124 := by
  rw [tree124,root,root117]
  exact (congrArg JFp_SHADigest.digest address124).trans hash124
#print axioms root124
theorem shape124 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 53248=tree124 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 53248)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape117 f g inputs siblings]
  rw [unoccupied f g 11 55296 (by decide),siblings 11 (by decide) 55296 (by decide)]
  rfl
#print axioms shape124
def input125 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash125.message
def value125 : State := JFp_SHADigest.output JGy_Gr_M2.Hash125.result
theorem cast125_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash125.B00.input).map Fin.val=JGy_Gr_M2.Hash125.B00.input := by rfl
#print axioms cast125_0
theorem tail125 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash125.tail).map Fin.val=JGy_Gr_M2.Hash125.tail := by rfl
#print axioms tail125
theorem numeric125 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash125.message).map Fin.val=JGy_Gr_M2.Hash125.message := by
  simp only [JGy_Gr_M2.Hash125.message,JGy_Gr_M2.Hash125.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast125_0,tail125]
#print axioms numeric125
theorem hash125 : JFp_SHADigest.digest input125=value125 := by
  unfold input125 JFp_SHADigest.digest
  rw [numeric125,JGy_Gr_M2.Hash125.checked]
  rfl
#print axioms hash125
theorem address125 : BinMerkle32Path.nodeInput (children value118 (JGc_TX2_HashBytes.state [197,225,37,96,40,16,98,217,159,88,149,106,254,188,227,153,131,207,22,77,128,46,74,234,41,2,48,235,27,112,230,153]))=input125 := by rfl
#print axioms address125
def tree125 : Tree := .branch tree118 (.supplied (JGc_TX2_HashBytes.state [197,225,37,96,40,16,98,217,159,88,149,106,254,188,227,153,131,207,22,77,128,46,74,234,41,2,48,235,27,112,230,153]))
theorem root125 : root JFp_SHADigest.digest tree125=value125 := by
  rw [tree125,root,root118]
  exact (congrArg JFp_SHADigest.digest address125).trans hash125
#print axioms root125
theorem shape125 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 61440=tree125 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 61440)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape118 f g inputs siblings]
  rw [unoccupied f g 11 63488 (by decide),siblings 11 (by decide) 63488 (by decide)]
  rfl
#print axioms shape125
end AspisR1.JGy_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input126 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash126.message
def value126 : State := JFp_SHADigest.output JGy_Gr_M2.Hash126.result
theorem cast126_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash126.B00.input).map Fin.val=JGy_Gr_M2.Hash126.B00.input := by rfl
#print axioms cast126_0
theorem tail126 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash126.tail).map Fin.val=JGy_Gr_M2.Hash126.tail := by rfl
#print axioms tail126
theorem numeric126 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash126.message).map Fin.val=JGy_Gr_M2.Hash126.message := by
  simp only [JGy_Gr_M2.Hash126.message,JGy_Gr_M2.Hash126.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast126_0,tail126]
#print axioms numeric126
theorem hash126 : JFp_SHADigest.digest input126=value126 := by
  unfold input126 JFp_SHADigest.digest
  rw [numeric126,JGy_Gr_M2.Hash126.checked]
  rfl
#print axioms hash126
theorem address126 : BinMerkle32Path.nodeInput (children value119 value120)=input126 := by rfl
#print axioms address126
def tree126 : Tree := .branch tree119 tree120
theorem root126 : root JFp_SHADigest.digest tree126=value126 := by
  rw [tree126,root,root119,root120]
  exact (congrArg JFp_SHADigest.digest address126).trans hash126
#print axioms root126
theorem shape126 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 16384=tree126 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 16384)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape119 f g inputs siblings]
  rw [shape120 f g inputs siblings]
  rfl
#print axioms shape126
def input127 : Bytes := JGc_TX2_M2Roots.input153
def value127 : State := JGc_TX2_M2Roots.value153
theorem hash127 : JFp_SHADigest.digest input127=value127 := JGc_TX2_M2Roots.hash153
#print axioms hash127
theorem address127 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [224,16,194,66,110,101,52,10,179,79,182,34,88,250,183,144,150,209,247,104,194,136,212,200,251,140,161,235,156,251,89,119]) value121)=input127 := by rfl
#print axioms address127
def tree127 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [224,16,194,66,110,101,52,10,179,79,182,34,88,250,183,144,150,209,247,104,194,136,212,200,251,140,161,235,156,251,89,119])) tree121
theorem root127 : root JFp_SHADigest.digest tree127=value127 := by
  rw [tree127,root,root121]
  exact (congrArg JFp_SHADigest.digest address127).trans hash127
#print axioms root127
theorem shape127 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 32768=tree127 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 32768)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 12 32768 (by decide),siblings 12 (by decide) 32768 (by decide)]
  rw [shape121 f g inputs siblings]
  rfl
#print axioms shape127
def input128 : Bytes := JGc_TX2_M2Roots.input154
def value128 : State := JGc_TX2_M2Roots.value154
theorem hash128 : JFp_SHADigest.digest input128=value128 := JGc_TX2_M2Roots.hash154
#print axioms hash128
theorem address128 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [110,140,14,207,117,61,1,50,35,2,166,51,143,145,85,104,230,62,135,43,183,242,18,192,131,122,184,244,45,205,135,7]) value122)=input128 := by rfl
#print axioms address128
def tree128 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [110,140,14,207,117,61,1,50,35,2,166,51,143,145,85,104,230,62,135,43,183,242,18,192,131,122,184,244,45,205,135,7])) tree122
theorem root128 : root JFp_SHADigest.digest tree128=value128 := by
  rw [tree128,root,root122]
  exact (congrArg JFp_SHADigest.digest address128).trans hash128
#print axioms root128
theorem shape128 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 40960=tree128 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 40960)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 12 40960 (by decide),siblings 12 (by decide) 40960 (by decide)]
  rw [shape122 f g inputs siblings]
  rfl
#print axioms shape128
def input129 : Bytes := JGc_TX2_M2Roots.input155
def value129 : State := JGc_TX2_M2Roots.value155
theorem hash129 : JFp_SHADigest.digest input129=value129 := JGc_TX2_M2Roots.hash155
#print axioms hash129
theorem address129 : BinMerkle32Path.nodeInput (children value123 value124)=input129 := by rfl
#print axioms address129
def tree129 : Tree := .branch tree123 tree124
theorem root129 : root JFp_SHADigest.digest tree129=value129 := by
  rw [tree129,root,root123,root124]
  exact (congrArg JFp_SHADigest.digest address129).trans hash129
#print axioms root129
theorem shape129 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 49152=tree129 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 49152)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape123 f g inputs siblings]
  rw [shape124 f g inputs siblings]
  rfl
#print axioms shape129
def input130 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash130.message
def value130 : State := JFp_SHADigest.output JGy_Gr_M2.Hash130.result
theorem cast130_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash130.B00.input).map Fin.val=JGy_Gr_M2.Hash130.B00.input := by rfl
#print axioms cast130_0
theorem tail130 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash130.tail).map Fin.val=JGy_Gr_M2.Hash130.tail := by rfl
#print axioms tail130
theorem numeric130 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash130.message).map Fin.val=JGy_Gr_M2.Hash130.message := by
  simp only [JGy_Gr_M2.Hash130.message,JGy_Gr_M2.Hash130.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast130_0,tail130]
#print axioms numeric130
theorem hash130 : JFp_SHADigest.digest input130=value130 := by
  unfold input130 JFp_SHADigest.digest
  rw [numeric130,JGy_Gr_M2.Hash130.checked]
  rfl
#print axioms hash130
theorem address130 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [141,64,232,71,157,231,216,45,93,159,181,117,153,193,198,18,181,64,29,202,192,123,128,152,11,184,100,22,94,163,139,202]) value125)=input130 := by rfl
#print axioms address130
def tree130 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [141,64,232,71,157,231,216,45,93,159,181,117,153,193,198,18,181,64,29,202,192,123,128,152,11,184,100,22,94,163,139,202])) tree125
theorem root130 : root JFp_SHADigest.digest tree130=value130 := by
  rw [tree130,root,root125]
  exact (congrArg JFp_SHADigest.digest address130).trans hash130
#print axioms root130
theorem shape130 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 57344=tree130 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 57344)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 12 57344 (by decide),siblings 12 (by decide) 57344 (by decide)]
  rw [shape125 f g inputs siblings]
  rfl
#print axioms shape130
end AspisR1.JGy_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input131 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash131.message
def value131 : State := JFp_SHADigest.output JGy_Gr_M2.Hash131.result
theorem cast131_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash131.B00.input).map Fin.val=JGy_Gr_M2.Hash131.B00.input := by rfl
#print axioms cast131_0
theorem tail131 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash131.tail).map Fin.val=JGy_Gr_M2.Hash131.tail := by rfl
#print axioms tail131
theorem numeric131 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash131.message).map Fin.val=JGy_Gr_M2.Hash131.message := by
  simp only [JGy_Gr_M2.Hash131.message,JGy_Gr_M2.Hash131.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast131_0,tail131]
#print axioms numeric131
theorem hash131 : JFp_SHADigest.digest input131=value131 := by
  unfold input131 JFp_SHADigest.digest
  rw [numeric131,JGy_Gr_M2.Hash131.checked]
  rfl
#print axioms hash131
theorem address131 : BinMerkle32Path.nodeInput (children value126 (JGc_TX2_HashBytes.state [34,112,182,144,67,6,64,238,194,132,59,239,67,247,9,55,180,77,17,67,178,157,110,43,220,71,83,104,67,4,240,73]))=input131 := by rfl
#print axioms address131
def tree131 : Tree := .branch tree126 (.supplied (JGc_TX2_HashBytes.state [34,112,182,144,67,6,64,238,194,132,59,239,67,247,9,55,180,77,17,67,178,157,110,43,220,71,83,104,67,4,240,73]))
theorem root131 : root JFp_SHADigest.digest tree131=value131 := by
  rw [tree131,root,root126]
  exact (congrArg JFp_SHADigest.digest address131).trans hash131
#print axioms root131
theorem shape131 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 16384=tree131 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 16384)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape126 f g inputs siblings]
  rw [unoccupied f g 13 24576 (by decide),siblings 13 (by decide) 24576 (by decide)]
  rfl
#print axioms shape131
def input132 : Bytes := JGc_TX2_M2Roots.input157
def value132 : State := JGc_TX2_M2Roots.value157
theorem hash132 : JFp_SHADigest.digest input132=value132 := JGc_TX2_M2Roots.hash157
#print axioms hash132
theorem address132 : BinMerkle32Path.nodeInput (children value127 value128)=input132 := by rfl
#print axioms address132
def tree132 : Tree := .branch tree127 tree128
theorem root132 : root JFp_SHADigest.digest tree132=value132 := by
  rw [tree132,root,root127,root128]
  exact (congrArg JFp_SHADigest.digest address132).trans hash132
#print axioms root132
theorem shape132 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 32768=tree132 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 32768)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape127 f g inputs siblings]
  rw [shape128 f g inputs siblings]
  rfl
#print axioms shape132
def input133 : Bytes := JGc_TX2_M2Roots.input158
def value133 : State := JGc_TX2_M2Roots.value158
theorem hash133 : JFp_SHADigest.digest input133=value133 := JGc_TX2_M2Roots.hash158
#print axioms hash133
theorem address133 : BinMerkle32Path.nodeInput (children value129 value130)=input133 := by rfl
#print axioms address133
def tree133 : Tree := .branch tree129 tree130
theorem root133 : root JFp_SHADigest.digest tree133=value133 := by
  rw [tree133,root,root129,root130]
  exact (congrArg JFp_SHADigest.digest address133).trans hash133
#print axioms root133
theorem shape133 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 49152=tree133 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 49152)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape129 f g inputs siblings]
  rw [shape130 f g inputs siblings]
  rfl
#print axioms shape133
end AspisR1.JGy_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input134 : Bytes := JGc_TX2_M2Roots.input159
def value134 : State := JGc_TX2_M2Roots.value159
theorem hash134 : JFp_SHADigest.digest input134=value134 := JGc_TX2_M2Roots.hash159
#print axioms hash134
theorem address134 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [28,133,8,205,254,15,139,95,248,58,225,38,64,117,236,147,74,140,165,149,219,239,213,12,183,184,40,0,97,10,83,26]) value131)=input134 := by rfl
#print axioms address134
def tree134 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [28,133,8,205,254,15,139,95,248,58,225,38,64,117,236,147,74,140,165,149,219,239,213,12,183,184,40,0,97,10,83,26])) tree131
theorem root134 : root JFp_SHADigest.digest tree134=value134 := by
  rw [tree134,root,root131]
  exact (congrArg JFp_SHADigest.digest address134).trans hash134
#print axioms root134
theorem shape134 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 15 0=tree134 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 15 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 14 0 (by decide),siblings 14 (by decide) 0 (by decide)]
  rw [shape131 f g inputs siblings]
  rfl
#print axioms shape134
def input135 : Bytes := JGc_TX2_M2Roots.input160
def value135 : State := JGc_TX2_M2Roots.value160
theorem hash135 : JFp_SHADigest.digest input135=value135 := JGc_TX2_M2Roots.hash160
#print axioms hash135
theorem address135 : BinMerkle32Path.nodeInput (children value132 value133)=input135 := by rfl
#print axioms address135
def tree135 : Tree := .branch tree132 tree133
theorem root135 : root JFp_SHADigest.digest tree135=value135 := by
  rw [tree135,root,root132,root133]
  exact (congrArg JFp_SHADigest.digest address135).trans hash135
#print axioms root135
theorem shape135 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 15 32768=tree135 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 15 32768)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape132 f g inputs siblings]
  rw [shape133 f g inputs siblings]
  rfl
#print axioms shape135
end AspisR1.JGy_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input136 : Bytes := JGc_TX2_M2Roots.input161
def value136 : State := JGc_TX2_M2Roots.value161
theorem hash136 : JFp_SHADigest.digest input136=value136 := JGc_TX2_M2Roots.hash161
#print axioms hash136
theorem address136 : BinMerkle32Path.nodeInput (children value134 value135)=input136 := by rfl
#print axioms address136
def tree136 : Tree := .branch tree134 tree135
theorem root136 : root JFp_SHADigest.digest tree136=value136 := by
  rw [tree136,root,root134,root135]
  exact (congrArg JFp_SHADigest.digest address136).trans hash136
#print axioms root136
theorem shape136 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 16 0=tree136 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 16 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape134 f g inputs siblings]
  rw [shape135 f g inputs siblings]
  rfl
#print axioms shape136
end AspisR1.JGy_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input137 : Bytes := JGc_TX2_M2Roots.input162
def value137 : State := JGc_TX2_M2Roots.value162
theorem hash137 : JFp_SHADigest.digest input137=value137 := JGc_TX2_M2Roots.hash162
#print axioms hash137
theorem address137 : BinMerkle32Path.nodeInput (children value136 (JGc_TX2_HashBytes.state [128,179,167,189,122,81,88,173,23,97,55,49,163,83,67,138,131,227,2,149,136,117,239,125,58,69,31,115,134,136,165,136]))=input137 := by rfl
#print axioms address137
def tree137 : Tree := .branch tree136 (.supplied (JGc_TX2_HashBytes.state [128,179,167,189,122,81,88,173,23,97,55,49,163,83,67,138,131,227,2,149,136,117,239,125,58,69,31,115,134,136,165,136]))
theorem root137 : root JFp_SHADigest.digest tree137=value137 := by
  rw [tree137,root,root136]
  exact (congrArg JFp_SHADigest.digest address137).trans hash137
#print axioms root137
theorem shape137 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 17 0=tree137 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 17 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape136 f g inputs siblings]
  rw [unoccupied f g 16 65536 (by decide),siblings 16 (by decide) 65536 (by decide)]
  rfl
#print axioms shape137
end AspisR1.JGy_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input138 : Bytes := JGc_TX2_M2Roots.input163
def value138 : State := JGc_TX2_M2Roots.value163
theorem hash138 : JFp_SHADigest.digest input138=value138 := JGc_TX2_M2Roots.hash163
#print axioms hash138
theorem address138 : BinMerkle32Path.nodeInput (children value137 (JGc_TX2_HashBytes.state [220,196,233,115,158,7,124,8,46,188,36,235,198,156,139,68,223,130,204,114,37,155,16,71,174,150,102,35,254,100,134,80]))=input138 := by rfl
#print axioms address138
def tree138 : Tree := .branch tree137 (.supplied (JGc_TX2_HashBytes.state [220,196,233,115,158,7,124,8,46,188,36,235,198,156,139,68,223,130,204,114,37,155,16,71,174,150,102,35,254,100,134,80]))
theorem root138 : root JFp_SHADigest.digest tree138=value138 := by
  rw [tree138,root,root137]
  exact (congrArg JFp_SHADigest.digest address138).trans hash138
#print axioms root138
theorem shape138 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 18 0=tree138 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 18 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape137 f g inputs siblings]
  rw [unoccupied f g 17 131072 (by decide),siblings 17 (by decide) 131072 (by decide)]
  rfl
#print axioms shape138
end AspisR1.JGy_Gr_M2Roots
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M2Root
open Aeneas Aeneas.Std
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiBuild OracleDecisionMultiTree JGy_Gr_M2Roots

def retainedRoot : State := JGc_TX2_M2Root.retainedRoot

theorem value_eq : value138=retainedRoot := by
  funext i
  fin_cases i <;> rfl
#print axioms value_eq

theorem source (f : Nat → Bytes) (g : Nat → Nat → State)
    (inputs : InputLaw f) (siblings : SiblingLaw g) :
    root JFp_SHADigest.digest (build indices f g 18 0)=retainedRoot := by
  rw [shape138 f g inputs siblings,root138,value_eq]
#print axioms source

theorem selected_queries : OraclePortSelectedDraft.selected
    (Port4B_KeyInstall.queries JFo_Prepared.value.queries) 0 2=indices := rfl
#print axioms selected_queries

theorem inhabited : ∃ (f : Nat → Bytes) (g : Nat → Nat → State),
    InputLaw f ∧ SiblingLaw g ∧
    root JFp_SHADigest.digest (build indices f g 18 0)=retainedRoot :=
  ⟨inputAt,siblingAt,(by intro b _;rfl),(by intro h _ b _;rfl),
    source inputAt siblingAt (by intro b _;rfl) (by intro h _ b _;rfl)⟩
#print axioms inhabited
end AspisR1.JGy_Gr_M2Root
end
