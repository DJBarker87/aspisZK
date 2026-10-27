import JHc_Tree1Part1
import JHc_Certs1_08
import JHc_Certs1_09
import JHc_Certs1_10
import JGh_TX2_M1Root
import JHc_Certs1_11
import JHc_Certs1_12
import JGe_View
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input100 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash100.message
def value100 : State := JFp_SHADigest.output JHc_Gr_M1.Hash100.result
theorem cast100_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash100.B00.input).map Fin.val=JHc_Gr_M1.Hash100.B00.input := by rfl
#print axioms cast100_0
theorem tail100 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash100.tail).map Fin.val=JHc_Gr_M1.Hash100.tail := by rfl
#print axioms tail100
theorem numeric100 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash100.message).map Fin.val=JHc_Gr_M1.Hash100.message := by
  simp only [JHc_Gr_M1.Hash100.message,JHc_Gr_M1.Hash100.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast100_0,tail100]
#print axioms numeric100
theorem hash100 : JFp_SHADigest.digest input100=value100 := by
  unfold input100 JFp_SHADigest.digest
  rw [numeric100,JHc_Gr_M1.Hash100.checked]
  rfl
#print axioms hash100
theorem address100 : BinMerkle32Path.nodeInput (children value090 (JGc_TX2_HashBytes.state [48,144,64,126,184,85,210,61,78,213,35,254,51,10,65,79,191,48,120,196,152,221,171,137,62,2,237,75,217,230,114,206]))=input100 := by rfl
#print axioms address100
def tree100 : Tree := .branch tree090 (.supplied (JGc_TX2_HashBytes.state [48,144,64,126,184,85,210,61,78,213,35,254,51,10,65,79,191,48,120,196,152,221,171,137,62,2,237,75,217,230,114,206]))
theorem root100 : root JFp_SHADigest.digest tree100=value100 := by
  rw [tree100,root,root090]
  exact (congrArg JFp_SHADigest.digest address100).trans hash100
#print axioms root100
theorem shape100 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 65536=tree100 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 65536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape090 f g inputs siblings]
  rw [unoccupied f g 9 66048 (by decide),siblings 9 (by decide) 66048 (by decide)]
  rfl
#print axioms shape100
def input101 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash101.message
def value101 : State := JFp_SHADigest.output JHc_Gr_M1.Hash101.result
theorem cast101_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash101.B00.input).map Fin.val=JHc_Gr_M1.Hash101.B00.input := by rfl
#print axioms cast101_0
theorem tail101 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash101.tail).map Fin.val=JHc_Gr_M1.Hash101.tail := by rfl
#print axioms tail101
theorem numeric101 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash101.message).map Fin.val=JHc_Gr_M1.Hash101.message := by
  simp only [JHc_Gr_M1.Hash101.message,JHc_Gr_M1.Hash101.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast101_0,tail101]
#print axioms numeric101
theorem hash101 : JFp_SHADigest.digest input101=value101 := by
  unfold input101 JFp_SHADigest.digest
  rw [numeric101,JHc_Gr_M1.Hash101.checked]
  rfl
#print axioms hash101
theorem address101 : BinMerkle32Path.nodeInput (children value091 (JGc_TX2_HashBytes.state [123,212,65,220,227,135,165,48,10,14,134,81,223,111,216,95,122,145,181,204,233,74,243,55,228,195,231,198,242,45,195,116]))=input101 := by rfl
#print axioms address101
def tree101 : Tree := .branch tree091 (.supplied (JGc_TX2_HashBytes.state [123,212,65,220,227,135,165,48,10,14,134,81,223,111,216,95,122,145,181,204,233,74,243,55,228,195,231,198,242,45,195,116]))
theorem root101 : root JFp_SHADigest.digest tree101=value101 := by
  rw [tree101,root,root091]
  exact (congrArg JFp_SHADigest.digest address101).trans hash101
#print axioms root101
theorem shape101 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 93184=tree101 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 93184)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape091 f g inputs siblings]
  rw [unoccupied f g 9 93696 (by decide),siblings 9 (by decide) 93696 (by decide)]
  rfl
#print axioms shape101
def input102 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash102.message
def value102 : State := JFp_SHADigest.output JHc_Gr_M1.Hash102.result
theorem cast102_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash102.B00.input).map Fin.val=JHc_Gr_M1.Hash102.B00.input := by rfl
#print axioms cast102_0
theorem tail102 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash102.tail).map Fin.val=JHc_Gr_M1.Hash102.tail := by rfl
#print axioms tail102
theorem numeric102 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash102.message).map Fin.val=JHc_Gr_M1.Hash102.message := by
  simp only [JHc_Gr_M1.Hash102.message,JHc_Gr_M1.Hash102.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast102_0,tail102]
#print axioms numeric102
theorem hash102 : JFp_SHADigest.digest input102=value102 := by
  unfold input102 JFp_SHADigest.digest
  rw [numeric102,JHc_Gr_M1.Hash102.checked]
  rfl
#print axioms hash102
theorem address102 : BinMerkle32Path.nodeInput (children value092 (JGc_TX2_HashBytes.state [105,41,192,88,96,73,217,61,90,149,168,78,2,247,208,1,169,49,116,37,15,146,137,252,165,203,84,179,141,144,47,178]))=input102 := by rfl
#print axioms address102
def tree102 : Tree := .branch tree092 (.supplied (JGc_TX2_HashBytes.state [105,41,192,88,96,73,217,61,90,149,168,78,2,247,208,1,169,49,116,37,15,146,137,252,165,203,84,179,141,144,47,178]))
theorem root102 : root JFp_SHADigest.digest tree102=value102 := by
  rw [tree102,root,root092]
  exact (congrArg JFp_SHADigest.digest address102).trans hash102
#print axioms root102
theorem shape102 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 147456=tree102 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 147456)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape092 f g inputs siblings]
  rw [unoccupied f g 9 147968 (by decide),siblings 9 (by decide) 147968 (by decide)]
  rfl
#print axioms shape102
def input103 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash103.message
def value103 : State := JFp_SHADigest.output JHc_Gr_M1.Hash103.result
theorem cast103_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash103.B00.input).map Fin.val=JHc_Gr_M1.Hash103.B00.input := by rfl
#print axioms cast103_0
theorem tail103 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash103.tail).map Fin.val=JHc_Gr_M1.Hash103.tail := by rfl
#print axioms tail103
theorem numeric103 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash103.message).map Fin.val=JHc_Gr_M1.Hash103.message := by
  simp only [JHc_Gr_M1.Hash103.message,JHc_Gr_M1.Hash103.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast103_0,tail103]
#print axioms numeric103
theorem hash103 : JFp_SHADigest.digest input103=value103 := by
  unfold input103 JFp_SHADigest.digest
  rw [numeric103,JHc_Gr_M1.Hash103.checked]
  rfl
#print axioms hash103
theorem address103 : BinMerkle32Path.nodeInput (children value093 (JGc_TX2_HashBytes.state [79,110,16,129,18,10,88,204,205,7,170,254,146,27,10,217,216,101,182,33,32,114,45,207,91,16,141,146,44,147,169,198]))=input103 := by rfl
#print axioms address103
def tree103 : Tree := .branch tree093 (.supplied (JGc_TX2_HashBytes.state [79,110,16,129,18,10,88,204,205,7,170,254,146,27,10,217,216,101,182,33,32,114,45,207,91,16,141,146,44,147,169,198]))
theorem root103 : root JFp_SHADigest.digest tree103=value103 := by
  rw [tree103,root,root093]
  exact (congrArg JFp_SHADigest.digest address103).trans hash103
#print axioms root103
theorem shape103 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 159744=tree103 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 159744)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape093 f g inputs siblings]
  rw [unoccupied f g 9 160256 (by decide),siblings 9 (by decide) 160256 (by decide)]
  rfl
#print axioms shape103
def input104 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash104.message
def value104 : State := JFp_SHADigest.output JHc_Gr_M1.Hash104.result
theorem cast104_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash104.B00.input).map Fin.val=JHc_Gr_M1.Hash104.B00.input := by rfl
#print axioms cast104_0
theorem tail104 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash104.tail).map Fin.val=JHc_Gr_M1.Hash104.tail := by rfl
#print axioms tail104
theorem numeric104 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash104.message).map Fin.val=JHc_Gr_M1.Hash104.message := by
  simp only [JHc_Gr_M1.Hash104.message,JHc_Gr_M1.Hash104.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast104_0,tail104]
#print axioms numeric104
theorem hash104 : JFp_SHADigest.digest input104=value104 := by
  unfold input104 JFp_SHADigest.digest
  rw [numeric104,JHc_Gr_M1.Hash104.checked]
  rfl
#print axioms hash104
theorem address104 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [11,211,99,36,92,115,16,181,114,150,174,18,232,7,212,203,202,159,103,225,65,179,95,167,92,166,67,145,5,238,42,44]) value094)=input104 := by rfl
#print axioms address104
def tree104 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [11,211,99,36,92,115,16,181,114,150,174,18,232,7,212,203,202,159,103,225,65,179,95,167,92,166,67,145,5,238,42,44])) tree094
theorem root104 : root JFp_SHADigest.digest tree104=value104 := by
  rw [tree104,root,root094]
  exact (congrArg JFp_SHADigest.digest address104).trans hash104
#print axioms root104
theorem shape104 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 183296=tree104 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 183296)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 9 183296 (by decide),siblings 9 (by decide) 183296 (by decide)]
  rw [shape094 f g inputs siblings]
  rfl
#print axioms shape104
def input105 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash105.message
def value105 : State := JFp_SHADigest.output JHc_Gr_M1.Hash105.result
theorem cast105_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash105.B00.input).map Fin.val=JHc_Gr_M1.Hash105.B00.input := by rfl
#print axioms cast105_0
theorem tail105 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash105.tail).map Fin.val=JHc_Gr_M1.Hash105.tail := by rfl
#print axioms tail105
theorem numeric105 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash105.message).map Fin.val=JHc_Gr_M1.Hash105.message := by
  simp only [JHc_Gr_M1.Hash105.message,JHc_Gr_M1.Hash105.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast105_0,tail105]
#print axioms numeric105
theorem hash105 : JFp_SHADigest.digest input105=value105 := by
  unfold input105 JFp_SHADigest.digest
  rw [numeric105,JHc_Gr_M1.Hash105.checked]
  rfl
#print axioms hash105
theorem address105 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [208,162,139,184,71,32,217,179,68,248,58,170,4,146,236,236,84,29,218,63,17,10,25,168,216,57,163,181,19,17,253,247]) value095)=input105 := by rfl
#print axioms address105
def tree105 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [208,162,139,184,71,32,217,179,68,248,58,170,4,146,236,236,84,29,218,63,17,10,25,168,216,57,163,181,19,17,253,247])) tree095
theorem root105 : root JFp_SHADigest.digest tree105=value105 := by
  rw [tree105,root,root095]
  exact (congrArg JFp_SHADigest.digest address105).trans hash105
#print axioms root105
theorem shape105 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 191488=tree105 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 191488)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 9 191488 (by decide),siblings 9 (by decide) 191488 (by decide)]
  rw [shape095 f g inputs siblings]
  rfl
#print axioms shape105
def input106 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash106.message
def value106 : State := JFp_SHADigest.output JHc_Gr_M1.Hash106.result
theorem cast106_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash106.B00.input).map Fin.val=JHc_Gr_M1.Hash106.B00.input := by rfl
#print axioms cast106_0
theorem tail106 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash106.tail).map Fin.val=JHc_Gr_M1.Hash106.tail := by rfl
#print axioms tail106
theorem numeric106 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash106.message).map Fin.val=JHc_Gr_M1.Hash106.message := by
  simp only [JHc_Gr_M1.Hash106.message,JHc_Gr_M1.Hash106.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast106_0,tail106]
#print axioms numeric106
theorem hash106 : JFp_SHADigest.digest input106=value106 := by
  unfold input106 JFp_SHADigest.digest
  rw [numeric106,JHc_Gr_M1.Hash106.checked]
  rfl
#print axioms hash106
theorem address106 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [60,103,59,209,113,130,229,235,243,97,45,115,125,45,43,4,217,213,119,152,92,68,200,106,165,187,222,51,4,211,153,18]) value096)=input106 := by rfl
#print axioms address106
def tree106 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [60,103,59,209,113,130,229,235,243,97,45,115,125,45,43,4,217,213,119,152,92,68,200,106,165,187,222,51,4,211,153,18])) tree096
theorem root106 : root JFp_SHADigest.digest tree106=value106 := by
  rw [tree106,root,root096]
  exact (congrArg JFp_SHADigest.digest address106).trans hash106
#print axioms root106
theorem shape106 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 192512=tree106 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 192512)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 9 192512 (by decide),siblings 9 (by decide) 192512 (by decide)]
  rw [shape096 f g inputs siblings]
  rfl
#print axioms shape106
def input107 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash107.message
def value107 : State := JFp_SHADigest.output JHc_Gr_M1.Hash107.result
theorem cast107_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash107.B00.input).map Fin.val=JHc_Gr_M1.Hash107.B00.input := by rfl
#print axioms cast107_0
theorem tail107 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash107.tail).map Fin.val=JHc_Gr_M1.Hash107.tail := by rfl
#print axioms tail107
theorem numeric107 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash107.message).map Fin.val=JHc_Gr_M1.Hash107.message := by
  simp only [JHc_Gr_M1.Hash107.message,JHc_Gr_M1.Hash107.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast107_0,tail107]
#print axioms numeric107
theorem hash107 : JFp_SHADigest.digest input107=value107 := by
  unfold input107 JFp_SHADigest.digest
  rw [numeric107,JHc_Gr_M1.Hash107.checked]
  rfl
#print axioms hash107
theorem address107 : BinMerkle32Path.nodeInput (children value097 (JGc_TX2_HashBytes.state [19,72,36,207,19,187,133,44,138,222,148,125,141,146,17,59,41,212,119,158,223,201,152,145,76,37,91,48,226,129,30,9]))=input107 := by rfl
#print axioms address107
def tree107 : Tree := .branch tree097 (.supplied (JGc_TX2_HashBytes.state [19,72,36,207,19,187,133,44,138,222,148,125,141,146,17,59,41,212,119,158,223,201,152,145,76,37,91,48,226,129,30,9]))
theorem root107 : root JFp_SHADigest.digest tree107=value107 := by
  rw [tree107,root,root097]
  exact (congrArg JFp_SHADigest.digest address107).trans hash107
#print axioms root107
theorem shape107 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 208896=tree107 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 208896)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape097 f g inputs siblings]
  rw [unoccupied f g 9 209408 (by decide),siblings 9 (by decide) 209408 (by decide)]
  rfl
#print axioms shape107
def input108 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash108.message
def value108 : State := JFp_SHADigest.output JHc_Gr_M1.Hash108.result
theorem cast108_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash108.B00.input).map Fin.val=JHc_Gr_M1.Hash108.B00.input := by rfl
#print axioms cast108_0
theorem tail108 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash108.tail).map Fin.val=JHc_Gr_M1.Hash108.tail := by rfl
#print axioms tail108
theorem numeric108 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash108.message).map Fin.val=JHc_Gr_M1.Hash108.message := by
  simp only [JHc_Gr_M1.Hash108.message,JHc_Gr_M1.Hash108.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast108_0,tail108]
#print axioms numeric108
theorem hash108 : JFp_SHADigest.digest input108=value108 := by
  unfold input108 JFp_SHADigest.digest
  rw [numeric108,JHc_Gr_M1.Hash108.checked]
  rfl
#print axioms hash108
theorem address108 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [186,33,168,206,73,137,127,197,84,223,139,201,20,128,251,0,154,250,60,123,141,245,74,52,213,26,143,116,98,102,120,146]) value098)=input108 := by rfl
#print axioms address108
def tree108 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [186,33,168,206,73,137,127,197,84,223,139,201,20,128,251,0,154,250,60,123,141,245,74,52,213,26,143,116,98,102,120,146])) tree098
theorem root108 : root JFp_SHADigest.digest tree108=value108 := by
  rw [tree108,root,root098]
  exact (congrArg JFp_SHADigest.digest address108).trans hash108
#print axioms root108
theorem shape108 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 216064=tree108 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 216064)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 9 216064 (by decide),siblings 9 (by decide) 216064 (by decide)]
  rw [shape098 f g inputs siblings]
  rfl
#print axioms shape108
def input109 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash109.message
def value109 : State := JFp_SHADigest.output JHc_Gr_M1.Hash109.result
theorem cast109_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash109.B00.input).map Fin.val=JHc_Gr_M1.Hash109.B00.input := by rfl
#print axioms cast109_0
theorem tail109 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash109.tail).map Fin.val=JHc_Gr_M1.Hash109.tail := by rfl
#print axioms tail109
theorem numeric109 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash109.message).map Fin.val=JHc_Gr_M1.Hash109.message := by
  simp only [JHc_Gr_M1.Hash109.message,JHc_Gr_M1.Hash109.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast109_0,tail109]
#print axioms numeric109
theorem hash109 : JFp_SHADigest.digest input109=value109 := by
  unfold input109 JFp_SHADigest.digest
  rw [numeric109,JHc_Gr_M1.Hash109.checked]
  rfl
#print axioms hash109
theorem address109 : BinMerkle32Path.nodeInput (children value099 (JGc_TX2_HashBytes.state [58,64,20,28,188,224,199,55,182,135,197,202,243,225,130,75,187,86,96,87,139,220,144,34,26,247,190,0,220,86,80,95]))=input109 := by rfl
#print axioms address109
def tree109 : Tree := .branch tree099 (.supplied (JGc_TX2_HashBytes.state [58,64,20,28,188,224,199,55,182,135,197,202,243,225,130,75,187,86,96,87,139,220,144,34,26,247,190,0,220,86,80,95]))
theorem root109 : root JFp_SHADigest.digest tree109=value109 := by
  rw [tree109,root,root099]
  exact (congrArg JFp_SHADigest.digest address109).trans hash109
#print axioms root109
theorem shape109 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 245760=tree109 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 245760)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape099 f g inputs siblings]
  rw [unoccupied f g 9 246272 (by decide),siblings 9 (by decide) 246272 (by decide)]
  rfl
#print axioms shape109
end AspisR1.JHc_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input110 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash110.message
def value110 : State := JFp_SHADigest.output JHc_Gr_M1.Hash110.result
theorem cast110_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash110.B00.input).map Fin.val=JHc_Gr_M1.Hash110.B00.input := by rfl
#print axioms cast110_0
theorem tail110 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash110.tail).map Fin.val=JHc_Gr_M1.Hash110.tail := by rfl
#print axioms tail110
theorem numeric110 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash110.message).map Fin.val=JHc_Gr_M1.Hash110.message := by
  simp only [JHc_Gr_M1.Hash110.message,JHc_Gr_M1.Hash110.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast110_0,tail110]
#print axioms numeric110
theorem hash110 : JFp_SHADigest.digest input110=value110 := by
  unfold input110 JFp_SHADigest.digest
  rw [numeric110,JHc_Gr_M1.Hash110.checked]
  rfl
#print axioms hash110
theorem address110 : BinMerkle32Path.nodeInput (children value100 (JGc_TX2_HashBytes.state [64,93,241,125,70,107,252,101,30,148,14,215,74,250,227,182,249,65,129,42,162,101,220,242,179,42,5,160,220,31,103,150]))=input110 := by rfl
#print axioms address110
def tree110 : Tree := .branch tree100 (.supplied (JGc_TX2_HashBytes.state [64,93,241,125,70,107,252,101,30,148,14,215,74,250,227,182,249,65,129,42,162,101,220,242,179,42,5,160,220,31,103,150]))
theorem root110 : root JFp_SHADigest.digest tree110=value110 := by
  rw [tree110,root,root100]
  exact (congrArg JFp_SHADigest.digest address110).trans hash110
#print axioms root110
theorem shape110 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 65536=tree110 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 65536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape100 f g inputs siblings]
  rw [unoccupied f g 10 66560 (by decide),siblings 10 (by decide) 66560 (by decide)]
  rfl
#print axioms shape110
def input111 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash111.message
def value111 : State := JFp_SHADigest.output JHc_Gr_M1.Hash111.result
theorem cast111_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash111.B00.input).map Fin.val=JHc_Gr_M1.Hash111.B00.input := by rfl
#print axioms cast111_0
theorem tail111 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash111.tail).map Fin.val=JHc_Gr_M1.Hash111.tail := by rfl
#print axioms tail111
theorem numeric111 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash111.message).map Fin.val=JHc_Gr_M1.Hash111.message := by
  simp only [JHc_Gr_M1.Hash111.message,JHc_Gr_M1.Hash111.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast111_0,tail111]
#print axioms numeric111
theorem hash111 : JFp_SHADigest.digest input111=value111 := by
  unfold input111 JFp_SHADigest.digest
  rw [numeric111,JHc_Gr_M1.Hash111.checked]
  rfl
#print axioms hash111
theorem address111 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [198,65,48,63,241,221,71,5,120,194,136,208,90,35,236,55,212,20,152,28,68,68,108,189,66,188,78,237,91,99,244,231]) value101)=input111 := by rfl
#print axioms address111
def tree111 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [198,65,48,63,241,221,71,5,120,194,136,208,90,35,236,55,212,20,152,28,68,68,108,189,66,188,78,237,91,99,244,231])) tree101
theorem root111 : root JFp_SHADigest.digest tree111=value111 := by
  rw [tree111,root,root101]
  exact (congrArg JFp_SHADigest.digest address111).trans hash111
#print axioms root111
theorem shape111 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 92160=tree111 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 92160)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 92160 (by decide),siblings 10 (by decide) 92160 (by decide)]
  rw [shape101 f g inputs siblings]
  rfl
#print axioms shape111
def input112 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash112.message
def value112 : State := JFp_SHADigest.output JHc_Gr_M1.Hash112.result
theorem cast112_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash112.B00.input).map Fin.val=JHc_Gr_M1.Hash112.B00.input := by rfl
#print axioms cast112_0
theorem tail112 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash112.tail).map Fin.val=JHc_Gr_M1.Hash112.tail := by rfl
#print axioms tail112
theorem numeric112 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash112.message).map Fin.val=JHc_Gr_M1.Hash112.message := by
  simp only [JHc_Gr_M1.Hash112.message,JHc_Gr_M1.Hash112.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast112_0,tail112]
#print axioms numeric112
theorem hash112 : JFp_SHADigest.digest input112=value112 := by
  unfold input112 JFp_SHADigest.digest
  rw [numeric112,JHc_Gr_M1.Hash112.checked]
  rfl
#print axioms hash112
theorem address112 : BinMerkle32Path.nodeInput (children value102 (JGc_TX2_HashBytes.state [164,41,120,158,16,43,175,133,186,191,175,18,223,41,66,159,126,137,11,165,228,232,46,160,78,239,53,218,10,204,109,142]))=input112 := by rfl
#print axioms address112
def tree112 : Tree := .branch tree102 (.supplied (JGc_TX2_HashBytes.state [164,41,120,158,16,43,175,133,186,191,175,18,223,41,66,159,126,137,11,165,228,232,46,160,78,239,53,218,10,204,109,142]))
theorem root112 : root JFp_SHADigest.digest tree112=value112 := by
  rw [tree112,root,root102]
  exact (congrArg JFp_SHADigest.digest address112).trans hash112
#print axioms root112
theorem shape112 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 147456=tree112 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 147456)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape102 f g inputs siblings]
  rw [unoccupied f g 10 148480 (by decide),siblings 10 (by decide) 148480 (by decide)]
  rfl
#print axioms shape112
def input113 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash113.message
def value113 : State := JFp_SHADigest.output JHc_Gr_M1.Hash113.result
theorem cast113_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash113.B00.input).map Fin.val=JHc_Gr_M1.Hash113.B00.input := by rfl
#print axioms cast113_0
theorem tail113 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash113.tail).map Fin.val=JHc_Gr_M1.Hash113.tail := by rfl
#print axioms tail113
theorem numeric113 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash113.message).map Fin.val=JHc_Gr_M1.Hash113.message := by
  simp only [JHc_Gr_M1.Hash113.message,JHc_Gr_M1.Hash113.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast113_0,tail113]
#print axioms numeric113
theorem hash113 : JFp_SHADigest.digest input113=value113 := by
  unfold input113 JFp_SHADigest.digest
  rw [numeric113,JHc_Gr_M1.Hash113.checked]
  rfl
#print axioms hash113
theorem address113 : BinMerkle32Path.nodeInput (children value103 (JGc_TX2_HashBytes.state [100,11,72,203,23,49,116,82,9,97,40,39,67,176,85,179,239,78,31,49,180,135,233,14,182,133,146,114,96,7,47,39]))=input113 := by rfl
#print axioms address113
def tree113 : Tree := .branch tree103 (.supplied (JGc_TX2_HashBytes.state [100,11,72,203,23,49,116,82,9,97,40,39,67,176,85,179,239,78,31,49,180,135,233,14,182,133,146,114,96,7,47,39]))
theorem root113 : root JFp_SHADigest.digest tree113=value113 := by
  rw [tree113,root,root103]
  exact (congrArg JFp_SHADigest.digest address113).trans hash113
#print axioms root113
theorem shape113 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 159744=tree113 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 159744)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape103 f g inputs siblings]
  rw [unoccupied f g 10 160768 (by decide),siblings 10 (by decide) 160768 (by decide)]
  rfl
#print axioms shape113
def input114 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash114.message
def value114 : State := JFp_SHADigest.output JHc_Gr_M1.Hash114.result
theorem cast114_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash114.B00.input).map Fin.val=JHc_Gr_M1.Hash114.B00.input := by rfl
#print axioms cast114_0
theorem tail114 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash114.tail).map Fin.val=JHc_Gr_M1.Hash114.tail := by rfl
#print axioms tail114
theorem numeric114 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash114.message).map Fin.val=JHc_Gr_M1.Hash114.message := by
  simp only [JHc_Gr_M1.Hash114.message,JHc_Gr_M1.Hash114.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast114_0,tail114]
#print axioms numeric114
theorem hash114 : JFp_SHADigest.digest input114=value114 := by
  unfold input114 JFp_SHADigest.digest
  rw [numeric114,JHc_Gr_M1.Hash114.checked]
  rfl
#print axioms hash114
theorem address114 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [184,18,54,84,108,157,180,156,80,20,210,100,117,102,246,78,234,211,56,215,194,254,92,204,54,91,195,240,221,94,111,149]) value104)=input114 := by rfl
#print axioms address114
def tree114 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [184,18,54,84,108,157,180,156,80,20,210,100,117,102,246,78,234,211,56,215,194,254,92,204,54,91,195,240,221,94,111,149])) tree104
theorem root114 : root JFp_SHADigest.digest tree114=value114 := by
  rw [tree114,root,root104]
  exact (congrArg JFp_SHADigest.digest address114).trans hash114
#print axioms root114
theorem shape114 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 182272=tree114 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 182272)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 182272 (by decide),siblings 10 (by decide) 182272 (by decide)]
  rw [shape104 f g inputs siblings]
  rfl
#print axioms shape114
def input115 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash115.message
def value115 : State := JFp_SHADigest.output JHc_Gr_M1.Hash115.result
theorem cast115_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash115.B00.input).map Fin.val=JHc_Gr_M1.Hash115.B00.input := by rfl
#print axioms cast115_0
theorem tail115 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash115.tail).map Fin.val=JHc_Gr_M1.Hash115.tail := by rfl
#print axioms tail115
theorem numeric115 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash115.message).map Fin.val=JHc_Gr_M1.Hash115.message := by
  simp only [JHc_Gr_M1.Hash115.message,JHc_Gr_M1.Hash115.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast115_0,tail115]
#print axioms numeric115
theorem hash115 : JFp_SHADigest.digest input115=value115 := by
  unfold input115 JFp_SHADigest.digest
  rw [numeric115,JHc_Gr_M1.Hash115.checked]
  rfl
#print axioms hash115
theorem address115 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [63,228,40,85,211,28,242,188,32,35,226,36,237,119,146,127,123,57,188,62,64,103,16,217,15,240,231,101,242,238,216,229]) value105)=input115 := by rfl
#print axioms address115
def tree115 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [63,228,40,85,211,28,242,188,32,35,226,36,237,119,146,127,123,57,188,62,64,103,16,217,15,240,231,101,242,238,216,229])) tree105
theorem root115 : root JFp_SHADigest.digest tree115=value115 := by
  rw [tree115,root,root105]
  exact (congrArg JFp_SHADigest.digest address115).trans hash115
#print axioms root115
theorem shape115 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 190464=tree115 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 190464)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 190464 (by decide),siblings 10 (by decide) 190464 (by decide)]
  rw [shape105 f g inputs siblings]
  rfl
#print axioms shape115
def input116 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash116.message
def value116 : State := JFp_SHADigest.output JHc_Gr_M1.Hash116.result
theorem cast116_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash116.B00.input).map Fin.val=JHc_Gr_M1.Hash116.B00.input := by rfl
#print axioms cast116_0
theorem tail116 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash116.tail).map Fin.val=JHc_Gr_M1.Hash116.tail := by rfl
#print axioms tail116
theorem numeric116 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash116.message).map Fin.val=JHc_Gr_M1.Hash116.message := by
  simp only [JHc_Gr_M1.Hash116.message,JHc_Gr_M1.Hash116.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast116_0,tail116]
#print axioms numeric116
theorem hash116 : JFp_SHADigest.digest input116=value116 := by
  unfold input116 JFp_SHADigest.digest
  rw [numeric116,JHc_Gr_M1.Hash116.checked]
  rfl
#print axioms hash116
theorem address116 : BinMerkle32Path.nodeInput (children value106 (JGc_TX2_HashBytes.state [130,69,10,242,115,118,110,253,30,219,254,90,113,163,245,178,100,145,233,86,77,1,166,132,100,215,190,224,34,250,87,35]))=input116 := by rfl
#print axioms address116
def tree116 : Tree := .branch tree106 (.supplied (JGc_TX2_HashBytes.state [130,69,10,242,115,118,110,253,30,219,254,90,113,163,245,178,100,145,233,86,77,1,166,132,100,215,190,224,34,250,87,35]))
theorem root116 : root JFp_SHADigest.digest tree116=value116 := by
  rw [tree116,root,root106]
  exact (congrArg JFp_SHADigest.digest address116).trans hash116
#print axioms root116
theorem shape116 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 192512=tree116 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 192512)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape106 f g inputs siblings]
  rw [unoccupied f g 10 193536 (by decide),siblings 10 (by decide) 193536 (by decide)]
  rfl
#print axioms shape116
def input117 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash117.message
def value117 : State := JFp_SHADigest.output JHc_Gr_M1.Hash117.result
theorem cast117_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash117.B00.input).map Fin.val=JHc_Gr_M1.Hash117.B00.input := by rfl
#print axioms cast117_0
theorem tail117 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash117.tail).map Fin.val=JHc_Gr_M1.Hash117.tail := by rfl
#print axioms tail117
theorem numeric117 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash117.message).map Fin.val=JHc_Gr_M1.Hash117.message := by
  simp only [JHc_Gr_M1.Hash117.message,JHc_Gr_M1.Hash117.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast117_0,tail117]
#print axioms numeric117
theorem hash117 : JFp_SHADigest.digest input117=value117 := by
  unfold input117 JFp_SHADigest.digest
  rw [numeric117,JHc_Gr_M1.Hash117.checked]
  rfl
#print axioms hash117
theorem address117 : BinMerkle32Path.nodeInput (children value107 (JGc_TX2_HashBytes.state [112,24,125,244,37,57,3,138,146,193,211,93,237,176,196,152,131,55,166,189,57,218,132,5,116,252,78,158,63,50,109,12]))=input117 := by rfl
#print axioms address117
def tree117 : Tree := .branch tree107 (.supplied (JGc_TX2_HashBytes.state [112,24,125,244,37,57,3,138,146,193,211,93,237,176,196,152,131,55,166,189,57,218,132,5,116,252,78,158,63,50,109,12]))
theorem root117 : root JFp_SHADigest.digest tree117=value117 := by
  rw [tree117,root,root107]
  exact (congrArg JFp_SHADigest.digest address117).trans hash117
#print axioms root117
theorem shape117 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 208896=tree117 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 208896)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape107 f g inputs siblings]
  rw [unoccupied f g 10 209920 (by decide),siblings 10 (by decide) 209920 (by decide)]
  rfl
#print axioms shape117
def input118 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash118.message
def value118 : State := JFp_SHADigest.output JHc_Gr_M1.Hash118.result
theorem cast118_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash118.B00.input).map Fin.val=JHc_Gr_M1.Hash118.B00.input := by rfl
#print axioms cast118_0
theorem tail118 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash118.tail).map Fin.val=JHc_Gr_M1.Hash118.tail := by rfl
#print axioms tail118
theorem numeric118 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash118.message).map Fin.val=JHc_Gr_M1.Hash118.message := by
  simp only [JHc_Gr_M1.Hash118.message,JHc_Gr_M1.Hash118.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast118_0,tail118]
#print axioms numeric118
theorem hash118 : JFp_SHADigest.digest input118=value118 := by
  unfold input118 JFp_SHADigest.digest
  rw [numeric118,JHc_Gr_M1.Hash118.checked]
  rfl
#print axioms hash118
theorem address118 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [215,230,177,31,18,107,67,128,173,64,143,244,114,180,207,188,65,56,143,94,43,60,198,20,173,93,12,193,37,52,52,140]) value108)=input118 := by rfl
#print axioms address118
def tree118 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [215,230,177,31,18,107,67,128,173,64,143,244,114,180,207,188,65,56,143,94,43,60,198,20,173,93,12,193,37,52,52,140])) tree108
theorem root118 : root JFp_SHADigest.digest tree118=value118 := by
  rw [tree118,root,root108]
  exact (congrArg JFp_SHADigest.digest address118).trans hash118
#print axioms root118
theorem shape118 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 215040=tree118 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 215040)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 215040 (by decide),siblings 10 (by decide) 215040 (by decide)]
  rw [shape108 f g inputs siblings]
  rfl
#print axioms shape118
def input119 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash119.message
def value119 : State := JFp_SHADigest.output JHc_Gr_M1.Hash119.result
theorem cast119_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash119.B00.input).map Fin.val=JHc_Gr_M1.Hash119.B00.input := by rfl
#print axioms cast119_0
theorem tail119 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash119.tail).map Fin.val=JHc_Gr_M1.Hash119.tail := by rfl
#print axioms tail119
theorem numeric119 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash119.message).map Fin.val=JHc_Gr_M1.Hash119.message := by
  simp only [JHc_Gr_M1.Hash119.message,JHc_Gr_M1.Hash119.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast119_0,tail119]
#print axioms numeric119
theorem hash119 : JFp_SHADigest.digest input119=value119 := by
  unfold input119 JFp_SHADigest.digest
  rw [numeric119,JHc_Gr_M1.Hash119.checked]
  rfl
#print axioms hash119
theorem address119 : BinMerkle32Path.nodeInput (children value109 (JGc_TX2_HashBytes.state [103,164,167,122,243,231,22,164,230,111,87,102,49,233,9,71,238,122,34,122,154,242,71,9,153,52,13,204,21,144,129,141]))=input119 := by rfl
#print axioms address119
def tree119 : Tree := .branch tree109 (.supplied (JGc_TX2_HashBytes.state [103,164,167,122,243,231,22,164,230,111,87,102,49,233,9,71,238,122,34,122,154,242,71,9,153,52,13,204,21,144,129,141]))
theorem root119 : root JFp_SHADigest.digest tree119=value119 := by
  rw [tree119,root,root109]
  exact (congrArg JFp_SHADigest.digest address119).trans hash119
#print axioms root119
theorem shape119 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 245760=tree119 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 245760)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape109 f g inputs siblings]
  rw [unoccupied f g 10 246784 (by decide),siblings 10 (by decide) 246784 (by decide)]
  rfl
#print axioms shape119
end AspisR1.JHc_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input120 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash120.message
def value120 : State := JFp_SHADigest.output JHc_Gr_M1.Hash120.result
theorem cast120_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash120.B00.input).map Fin.val=JHc_Gr_M1.Hash120.B00.input := by rfl
#print axioms cast120_0
theorem tail120 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash120.tail).map Fin.val=JHc_Gr_M1.Hash120.tail := by rfl
#print axioms tail120
theorem numeric120 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash120.message).map Fin.val=JHc_Gr_M1.Hash120.message := by
  simp only [JHc_Gr_M1.Hash120.message,JHc_Gr_M1.Hash120.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast120_0,tail120]
#print axioms numeric120
theorem hash120 : JFp_SHADigest.digest input120=value120 := by
  unfold input120 JFp_SHADigest.digest
  rw [numeric120,JHc_Gr_M1.Hash120.checked]
  rfl
#print axioms hash120
theorem address120 : BinMerkle32Path.nodeInput (children value110 (JGc_TX2_HashBytes.state [217,175,196,100,106,166,4,160,30,133,139,241,21,195,125,114,222,108,239,37,188,97,229,163,164,197,201,14,71,43,175,9]))=input120 := by rfl
#print axioms address120
def tree120 : Tree := .branch tree110 (.supplied (JGc_TX2_HashBytes.state [217,175,196,100,106,166,4,160,30,133,139,241,21,195,125,114,222,108,239,37,188,97,229,163,164,197,201,14,71,43,175,9]))
theorem root120 : root JFp_SHADigest.digest tree120=value120 := by
  rw [tree120,root,root110]
  exact (congrArg JFp_SHADigest.digest address120).trans hash120
#print axioms root120
theorem shape120 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 65536=tree120 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 65536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape110 f g inputs siblings]
  rw [unoccupied f g 11 67584 (by decide),siblings 11 (by decide) 67584 (by decide)]
  rfl
#print axioms shape120
def input121 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash121.message
def value121 : State := JFp_SHADigest.output JHc_Gr_M1.Hash121.result
theorem cast121_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash121.B00.input).map Fin.val=JHc_Gr_M1.Hash121.B00.input := by rfl
#print axioms cast121_0
theorem tail121 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash121.tail).map Fin.val=JHc_Gr_M1.Hash121.tail := by rfl
#print axioms tail121
theorem numeric121 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash121.message).map Fin.val=JHc_Gr_M1.Hash121.message := by
  simp only [JHc_Gr_M1.Hash121.message,JHc_Gr_M1.Hash121.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast121_0,tail121]
#print axioms numeric121
theorem hash121 : JFp_SHADigest.digest input121=value121 := by
  unfold input121 JFp_SHADigest.digest
  rw [numeric121,JHc_Gr_M1.Hash121.checked]
  rfl
#print axioms hash121
theorem address121 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [245,86,191,21,128,168,40,91,146,136,112,192,222,80,59,237,196,147,226,240,168,112,253,192,150,7,143,51,196,9,248,37]) value111)=input121 := by rfl
#print axioms address121
def tree121 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [245,86,191,21,128,168,40,91,146,136,112,192,222,80,59,237,196,147,226,240,168,112,253,192,150,7,143,51,196,9,248,37])) tree111
theorem root121 : root JFp_SHADigest.digest tree121=value121 := by
  rw [tree121,root,root111]
  exact (congrArg JFp_SHADigest.digest address121).trans hash121
#print axioms root121
theorem shape121 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 90112=tree121 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 90112)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 11 90112 (by decide),siblings 11 (by decide) 90112 (by decide)]
  rw [shape111 f g inputs siblings]
  rfl
#print axioms shape121
def input122 : Bytes := JGh_TX2_M1Roots.input150
def value122 : State := JGh_TX2_M1Roots.value150
theorem hash122 : JFp_SHADigest.digest input122=value122 := JGh_TX2_M1Roots.hash150
#print axioms hash122
theorem address122 : BinMerkle32Path.nodeInput (children value112 (JGc_TX2_HashBytes.state [211,15,11,17,227,198,215,231,129,25,99,34,247,62,244,155,62,104,100,207,187,196,141,130,8,193,86,21,253,129,202,143]))=input122 := by rfl
#print axioms address122
def tree122 : Tree := .branch tree112 (.supplied (JGc_TX2_HashBytes.state [211,15,11,17,227,198,215,231,129,25,99,34,247,62,244,155,62,104,100,207,187,196,141,130,8,193,86,21,253,129,202,143]))
theorem root122 : root JFp_SHADigest.digest tree122=value122 := by
  rw [tree122,root,root112]
  exact (congrArg JFp_SHADigest.digest address122).trans hash122
#print axioms root122
theorem shape122 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 147456=tree122 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 147456)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape112 f g inputs siblings]
  rw [unoccupied f g 11 149504 (by decide),siblings 11 (by decide) 149504 (by decide)]
  rfl
#print axioms shape122
def input123 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash123.message
def value123 : State := JFp_SHADigest.output JHc_Gr_M1.Hash123.result
theorem cast123_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash123.B00.input).map Fin.val=JHc_Gr_M1.Hash123.B00.input := by rfl
#print axioms cast123_0
theorem tail123 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash123.tail).map Fin.val=JHc_Gr_M1.Hash123.tail := by rfl
#print axioms tail123
theorem numeric123 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash123.message).map Fin.val=JHc_Gr_M1.Hash123.message := by
  simp only [JHc_Gr_M1.Hash123.message,JHc_Gr_M1.Hash123.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast123_0,tail123]
#print axioms numeric123
theorem hash123 : JFp_SHADigest.digest input123=value123 := by
  unfold input123 JFp_SHADigest.digest
  rw [numeric123,JHc_Gr_M1.Hash123.checked]
  rfl
#print axioms hash123
theorem address123 : BinMerkle32Path.nodeInput (children value113 (JGc_TX2_HashBytes.state [15,101,120,74,113,3,178,205,140,1,22,242,63,68,171,18,163,88,82,90,84,49,24,53,10,48,240,86,180,229,195,57]))=input123 := by rfl
#print axioms address123
def tree123 : Tree := .branch tree113 (.supplied (JGc_TX2_HashBytes.state [15,101,120,74,113,3,178,205,140,1,22,242,63,68,171,18,163,88,82,90,84,49,24,53,10,48,240,86,180,229,195,57]))
theorem root123 : root JFp_SHADigest.digest tree123=value123 := by
  rw [tree123,root,root113]
  exact (congrArg JFp_SHADigest.digest address123).trans hash123
#print axioms root123
theorem shape123 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 159744=tree123 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 159744)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape113 f g inputs siblings]
  rw [unoccupied f g 11 161792 (by decide),siblings 11 (by decide) 161792 (by decide)]
  rfl
#print axioms shape123
def input124 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash124.message
def value124 : State := JFp_SHADigest.output JHc_Gr_M1.Hash124.result
theorem cast124_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash124.B00.input).map Fin.val=JHc_Gr_M1.Hash124.B00.input := by rfl
#print axioms cast124_0
theorem tail124 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash124.tail).map Fin.val=JHc_Gr_M1.Hash124.tail := by rfl
#print axioms tail124
theorem numeric124 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash124.message).map Fin.val=JHc_Gr_M1.Hash124.message := by
  simp only [JHc_Gr_M1.Hash124.message,JHc_Gr_M1.Hash124.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast124_0,tail124]
#print axioms numeric124
theorem hash124 : JFp_SHADigest.digest input124=value124 := by
  unfold input124 JFp_SHADigest.digest
  rw [numeric124,JHc_Gr_M1.Hash124.checked]
  rfl
#print axioms hash124
theorem address124 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [196,176,224,63,58,66,146,38,214,180,92,204,177,20,194,41,249,159,205,160,145,250,27,12,85,20,34,52,29,203,225,93]) value114)=input124 := by rfl
#print axioms address124
def tree124 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [196,176,224,63,58,66,146,38,214,180,92,204,177,20,194,41,249,159,205,160,145,250,27,12,85,20,34,52,29,203,225,93])) tree114
theorem root124 : root JFp_SHADigest.digest tree124=value124 := by
  rw [tree124,root,root114]
  exact (congrArg JFp_SHADigest.digest address124).trans hash124
#print axioms root124
theorem shape124 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 180224=tree124 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 180224)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 11 180224 (by decide),siblings 11 (by decide) 180224 (by decide)]
  rw [shape114 f g inputs siblings]
  rfl
#print axioms shape124
def input125 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash125.message
def value125 : State := JFp_SHADigest.output JHc_Gr_M1.Hash125.result
theorem cast125_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash125.B00.input).map Fin.val=JHc_Gr_M1.Hash125.B00.input := by rfl
#print axioms cast125_0
theorem tail125 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash125.tail).map Fin.val=JHc_Gr_M1.Hash125.tail := by rfl
#print axioms tail125
theorem numeric125 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash125.message).map Fin.val=JHc_Gr_M1.Hash125.message := by
  simp only [JHc_Gr_M1.Hash125.message,JHc_Gr_M1.Hash125.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast125_0,tail125]
#print axioms numeric125
theorem hash125 : JFp_SHADigest.digest input125=value125 := by
  unfold input125 JFp_SHADigest.digest
  rw [numeric125,JHc_Gr_M1.Hash125.checked]
  rfl
#print axioms hash125
theorem address125 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [167,124,21,206,95,202,120,7,203,62,13,33,133,95,118,113,8,86,18,144,249,35,80,206,151,128,245,184,149,62,143,89]) value115)=input125 := by rfl
#print axioms address125
def tree125 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [167,124,21,206,95,202,120,7,203,62,13,33,133,95,118,113,8,86,18,144,249,35,80,206,151,128,245,184,149,62,143,89])) tree115
theorem root125 : root JFp_SHADigest.digest tree125=value125 := by
  rw [tree125,root,root115]
  exact (congrArg JFp_SHADigest.digest address125).trans hash125
#print axioms root125
theorem shape125 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 188416=tree125 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 188416)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 11 188416 (by decide),siblings 11 (by decide) 188416 (by decide)]
  rw [shape115 f g inputs siblings]
  rfl
#print axioms shape125
def input126 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash126.message
def value126 : State := JFp_SHADigest.output JHc_Gr_M1.Hash126.result
theorem cast126_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash126.B00.input).map Fin.val=JHc_Gr_M1.Hash126.B00.input := by rfl
#print axioms cast126_0
theorem tail126 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash126.tail).map Fin.val=JHc_Gr_M1.Hash126.tail := by rfl
#print axioms tail126
theorem numeric126 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash126.message).map Fin.val=JHc_Gr_M1.Hash126.message := by
  simp only [JHc_Gr_M1.Hash126.message,JHc_Gr_M1.Hash126.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast126_0,tail126]
#print axioms numeric126
theorem hash126 : JFp_SHADigest.digest input126=value126 := by
  unfold input126 JFp_SHADigest.digest
  rw [numeric126,JHc_Gr_M1.Hash126.checked]
  rfl
#print axioms hash126
theorem address126 : BinMerkle32Path.nodeInput (children value116 (JGc_TX2_HashBytes.state [40,24,99,188,225,201,92,11,125,146,207,221,1,133,77,170,92,32,179,180,208,97,222,61,235,239,136,46,164,100,6,189]))=input126 := by rfl
#print axioms address126
def tree126 : Tree := .branch tree116 (.supplied (JGc_TX2_HashBytes.state [40,24,99,188,225,201,92,11,125,146,207,221,1,133,77,170,92,32,179,180,208,97,222,61,235,239,136,46,164,100,6,189]))
theorem root126 : root JFp_SHADigest.digest tree126=value126 := by
  rw [tree126,root,root116]
  exact (congrArg JFp_SHADigest.digest address126).trans hash126
#print axioms root126
theorem shape126 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 192512=tree126 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 192512)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape116 f g inputs siblings]
  rw [unoccupied f g 11 194560 (by decide),siblings 11 (by decide) 194560 (by decide)]
  rfl
#print axioms shape126
def input127 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash127.message
def value127 : State := JFp_SHADigest.output JHc_Gr_M1.Hash127.result
theorem cast127_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash127.B00.input).map Fin.val=JHc_Gr_M1.Hash127.B00.input := by rfl
#print axioms cast127_0
theorem tail127 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash127.tail).map Fin.val=JHc_Gr_M1.Hash127.tail := by rfl
#print axioms tail127
theorem numeric127 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash127.message).map Fin.val=JHc_Gr_M1.Hash127.message := by
  simp only [JHc_Gr_M1.Hash127.message,JHc_Gr_M1.Hash127.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast127_0,tail127]
#print axioms numeric127
theorem hash127 : JFp_SHADigest.digest input127=value127 := by
  unfold input127 JFp_SHADigest.digest
  rw [numeric127,JHc_Gr_M1.Hash127.checked]
  rfl
#print axioms hash127
theorem address127 : BinMerkle32Path.nodeInput (children value117 (JGc_TX2_HashBytes.state [108,85,77,126,24,37,128,176,24,222,208,119,252,7,77,71,162,105,159,240,41,58,2,199,0,136,85,41,86,124,234,35]))=input127 := by rfl
#print axioms address127
def tree127 : Tree := .branch tree117 (.supplied (JGc_TX2_HashBytes.state [108,85,77,126,24,37,128,176,24,222,208,119,252,7,77,71,162,105,159,240,41,58,2,199,0,136,85,41,86,124,234,35]))
theorem root127 : root JFp_SHADigest.digest tree127=value127 := by
  rw [tree127,root,root117]
  exact (congrArg JFp_SHADigest.digest address127).trans hash127
#print axioms root127
theorem shape127 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 208896=tree127 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 208896)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape117 f g inputs siblings]
  rw [unoccupied f g 11 210944 (by decide),siblings 11 (by decide) 210944 (by decide)]
  rfl
#print axioms shape127
def input128 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash128.message
def value128 : State := JFp_SHADigest.output JHc_Gr_M1.Hash128.result
theorem cast128_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash128.B00.input).map Fin.val=JHc_Gr_M1.Hash128.B00.input := by rfl
#print axioms cast128_0
theorem tail128 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash128.tail).map Fin.val=JHc_Gr_M1.Hash128.tail := by rfl
#print axioms tail128
theorem numeric128 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash128.message).map Fin.val=JHc_Gr_M1.Hash128.message := by
  simp only [JHc_Gr_M1.Hash128.message,JHc_Gr_M1.Hash128.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast128_0,tail128]
#print axioms numeric128
theorem hash128 : JFp_SHADigest.digest input128=value128 := by
  unfold input128 JFp_SHADigest.digest
  rw [numeric128,JHc_Gr_M1.Hash128.checked]
  rfl
#print axioms hash128
theorem address128 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [210,204,100,222,46,98,83,84,247,179,170,243,109,102,248,130,215,145,18,205,170,10,130,187,6,137,151,18,195,62,117,160]) value118)=input128 := by rfl
#print axioms address128
def tree128 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [210,204,100,222,46,98,83,84,247,179,170,243,109,102,248,130,215,145,18,205,170,10,130,187,6,137,151,18,195,62,117,160])) tree118
theorem root128 : root JFp_SHADigest.digest tree128=value128 := by
  rw [tree128,root,root118]
  exact (congrArg JFp_SHADigest.digest address128).trans hash128
#print axioms root128
theorem shape128 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 212992=tree128 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 212992)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 11 212992 (by decide),siblings 11 (by decide) 212992 (by decide)]
  rw [shape118 f g inputs siblings]
  rfl
#print axioms shape128
def input129 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash129.message
def value129 : State := JFp_SHADigest.output JHc_Gr_M1.Hash129.result
theorem cast129_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash129.B00.input).map Fin.val=JHc_Gr_M1.Hash129.B00.input := by rfl
#print axioms cast129_0
theorem tail129 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash129.tail).map Fin.val=JHc_Gr_M1.Hash129.tail := by rfl
#print axioms tail129
theorem numeric129 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash129.message).map Fin.val=JHc_Gr_M1.Hash129.message := by
  simp only [JHc_Gr_M1.Hash129.message,JHc_Gr_M1.Hash129.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast129_0,tail129]
#print axioms numeric129
theorem hash129 : JFp_SHADigest.digest input129=value129 := by
  unfold input129 JFp_SHADigest.digest
  rw [numeric129,JHc_Gr_M1.Hash129.checked]
  rfl
#print axioms hash129
theorem address129 : BinMerkle32Path.nodeInput (children value119 (JGc_TX2_HashBytes.state [36,122,216,128,213,83,7,55,28,214,71,249,243,137,72,100,98,181,52,193,77,132,94,236,71,30,38,228,18,154,155,76]))=input129 := by rfl
#print axioms address129
def tree129 : Tree := .branch tree119 (.supplied (JGc_TX2_HashBytes.state [36,122,216,128,213,83,7,55,28,214,71,249,243,137,72,100,98,181,52,193,77,132,94,236,71,30,38,228,18,154,155,76]))
theorem root129 : root JFp_SHADigest.digest tree129=value129 := by
  rw [tree129,root,root119]
  exact (congrArg JFp_SHADigest.digest address129).trans hash129
#print axioms root129
theorem shape129 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 245760=tree129 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 245760)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape119 f g inputs siblings]
  rw [unoccupied f g 11 247808 (by decide),siblings 11 (by decide) 247808 (by decide)]
  rfl
#print axioms shape129
end AspisR1.JHc_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input130 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash130.message
def value130 : State := JFp_SHADigest.output JHc_Gr_M1.Hash130.result
theorem cast130_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash130.B00.input).map Fin.val=JHc_Gr_M1.Hash130.B00.input := by rfl
#print axioms cast130_0
theorem tail130 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash130.tail).map Fin.val=JHc_Gr_M1.Hash130.tail := by rfl
#print axioms tail130
theorem numeric130 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash130.message).map Fin.val=JHc_Gr_M1.Hash130.message := by
  simp only [JHc_Gr_M1.Hash130.message,JHc_Gr_M1.Hash130.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast130_0,tail130]
#print axioms numeric130
theorem hash130 : JFp_SHADigest.digest input130=value130 := by
  unfold input130 JFp_SHADigest.digest
  rw [numeric130,JHc_Gr_M1.Hash130.checked]
  rfl
#print axioms hash130
theorem address130 : BinMerkle32Path.nodeInput (children value120 (JGc_TX2_HashBytes.state [19,103,232,182,95,97,172,122,95,102,130,230,233,176,203,8,117,127,219,234,112,18,233,156,196,18,149,209,241,77,161,56]))=input130 := by rfl
#print axioms address130
def tree130 : Tree := .branch tree120 (.supplied (JGc_TX2_HashBytes.state [19,103,232,182,95,97,172,122,95,102,130,230,233,176,203,8,117,127,219,234,112,18,233,156,196,18,149,209,241,77,161,56]))
theorem root130 : root JFp_SHADigest.digest tree130=value130 := by
  rw [tree130,root,root120]
  exact (congrArg JFp_SHADigest.digest address130).trans hash130
#print axioms root130
theorem shape130 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 65536=tree130 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 65536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape120 f g inputs siblings]
  rw [unoccupied f g 12 69632 (by decide),siblings 12 (by decide) 69632 (by decide)]
  rfl
#print axioms shape130
def input131 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash131.message
def value131 : State := JFp_SHADigest.output JHc_Gr_M1.Hash131.result
theorem cast131_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash131.B00.input).map Fin.val=JHc_Gr_M1.Hash131.B00.input := by rfl
#print axioms cast131_0
theorem tail131 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash131.tail).map Fin.val=JHc_Gr_M1.Hash131.tail := by rfl
#print axioms tail131
theorem numeric131 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash131.message).map Fin.val=JHc_Gr_M1.Hash131.message := by
  simp only [JHc_Gr_M1.Hash131.message,JHc_Gr_M1.Hash131.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast131_0,tail131]
#print axioms numeric131
theorem hash131 : JFp_SHADigest.digest input131=value131 := by
  unfold input131 JFp_SHADigest.digest
  rw [numeric131,JHc_Gr_M1.Hash131.checked]
  rfl
#print axioms hash131
theorem address131 : BinMerkle32Path.nodeInput (children value121 (JGc_TX2_HashBytes.state [110,25,47,112,26,76,158,29,84,93,93,101,136,114,133,182,113,217,50,169,101,168,154,202,147,239,155,119,156,1,149,227]))=input131 := by rfl
#print axioms address131
def tree131 : Tree := .branch tree121 (.supplied (JGc_TX2_HashBytes.state [110,25,47,112,26,76,158,29,84,93,93,101,136,114,133,182,113,217,50,169,101,168,154,202,147,239,155,119,156,1,149,227]))
theorem root131 : root JFp_SHADigest.digest tree131=value131 := by
  rw [tree131,root,root121]
  exact (congrArg JFp_SHADigest.digest address131).trans hash131
#print axioms root131
theorem shape131 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 90112=tree131 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 90112)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape121 f g inputs siblings]
  rw [unoccupied f g 12 94208 (by decide),siblings 12 (by decide) 94208 (by decide)]
  rfl
#print axioms shape131
def input132 : Bytes := JGh_TX2_M1Roots.input161
def value132 : State := JGh_TX2_M1Roots.value161
theorem hash132 : JFp_SHADigest.digest input132=value132 := JGh_TX2_M1Roots.hash161
#print axioms hash132
theorem address132 : BinMerkle32Path.nodeInput (children value122 (JGc_TX2_HashBytes.state [125,179,140,223,84,63,248,207,79,4,254,76,50,105,252,113,154,218,31,6,172,77,212,91,67,94,96,253,37,229,243,212]))=input132 := by rfl
#print axioms address132
def tree132 : Tree := .branch tree122 (.supplied (JGc_TX2_HashBytes.state [125,179,140,223,84,63,248,207,79,4,254,76,50,105,252,113,154,218,31,6,172,77,212,91,67,94,96,253,37,229,243,212]))
theorem root132 : root JFp_SHADigest.digest tree132=value132 := by
  rw [tree132,root,root122]
  exact (congrArg JFp_SHADigest.digest address132).trans hash132
#print axioms root132
theorem shape132 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 147456=tree132 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 147456)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape122 f g inputs siblings]
  rw [unoccupied f g 12 151552 (by decide),siblings 12 (by decide) 151552 (by decide)]
  rfl
#print axioms shape132
def input133 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash133.message
def value133 : State := JFp_SHADigest.output JHc_Gr_M1.Hash133.result
theorem cast133_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash133.B00.input).map Fin.val=JHc_Gr_M1.Hash133.B00.input := by rfl
#print axioms cast133_0
theorem tail133 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash133.tail).map Fin.val=JHc_Gr_M1.Hash133.tail := by rfl
#print axioms tail133
theorem numeric133 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash133.message).map Fin.val=JHc_Gr_M1.Hash133.message := by
  simp only [JHc_Gr_M1.Hash133.message,JHc_Gr_M1.Hash133.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast133_0,tail133]
#print axioms numeric133
theorem hash133 : JFp_SHADigest.digest input133=value133 := by
  unfold input133 JFp_SHADigest.digest
  rw [numeric133,JHc_Gr_M1.Hash133.checked]
  rfl
#print axioms hash133
theorem address133 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [202,244,232,254,150,185,96,120,137,19,88,126,27,134,33,218,94,250,191,155,104,44,152,222,79,170,78,156,230,59,10,83]) value123)=input133 := by rfl
#print axioms address133
def tree133 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [202,244,232,254,150,185,96,120,137,19,88,126,27,134,33,218,94,250,191,155,104,44,152,222,79,170,78,156,230,59,10,83])) tree123
theorem root133 : root JFp_SHADigest.digest tree133=value133 := by
  rw [tree133,root,root123]
  exact (congrArg JFp_SHADigest.digest address133).trans hash133
#print axioms root133
theorem shape133 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 155648=tree133 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 155648)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 12 155648 (by decide),siblings 12 (by decide) 155648 (by decide)]
  rw [shape123 f g inputs siblings]
  rfl
#print axioms shape133
def input134 : Bytes := JGh_TX2_M1Roots.input164
def value134 : State := JGh_TX2_M1Roots.value164
theorem hash134 : JFp_SHADigest.digest input134=value134 := JGh_TX2_M1Roots.hash164
#print axioms hash134
theorem address134 : BinMerkle32Path.nodeInput (children value124 (JGc_TX2_HashBytes.state [166,50,145,224,172,240,239,69,50,244,235,90,162,220,82,237,69,91,183,14,206,124,87,33,164,12,204,235,137,70,174,5]))=input134 := by rfl
#print axioms address134
def tree134 : Tree := .branch tree124 (.supplied (JGc_TX2_HashBytes.state [166,50,145,224,172,240,239,69,50,244,235,90,162,220,82,237,69,91,183,14,206,124,87,33,164,12,204,235,137,70,174,5]))
theorem root134 : root JFp_SHADigest.digest tree134=value134 := by
  rw [tree134,root,root124]
  exact (congrArg JFp_SHADigest.digest address134).trans hash134
#print axioms root134
theorem shape134 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 180224=tree134 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 180224)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape124 f g inputs siblings]
  rw [unoccupied f g 12 184320 (by decide),siblings 12 (by decide) 184320 (by decide)]
  rfl
#print axioms shape134
def input135 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash135.message
def value135 : State := JFp_SHADigest.output JHc_Gr_M1.Hash135.result
theorem cast135_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash135.B00.input).map Fin.val=JHc_Gr_M1.Hash135.B00.input := by rfl
#print axioms cast135_0
theorem tail135 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash135.tail).map Fin.val=JHc_Gr_M1.Hash135.tail := by rfl
#print axioms tail135
theorem numeric135 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash135.message).map Fin.val=JHc_Gr_M1.Hash135.message := by
  simp only [JHc_Gr_M1.Hash135.message,JHc_Gr_M1.Hash135.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast135_0,tail135]
#print axioms numeric135
theorem hash135 : JFp_SHADigest.digest input135=value135 := by
  unfold input135 JFp_SHADigest.digest
  rw [numeric135,JHc_Gr_M1.Hash135.checked]
  rfl
#print axioms hash135
theorem address135 : BinMerkle32Path.nodeInput (children value125 value126)=input135 := by rfl
#print axioms address135
def tree135 : Tree := .branch tree125 tree126
theorem root135 : root JFp_SHADigest.digest tree135=value135 := by
  rw [tree135,root,root125,root126]
  exact (congrArg JFp_SHADigest.digest address135).trans hash135
#print axioms root135
theorem shape135 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 188416=tree135 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 188416)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape125 f g inputs siblings]
  rw [shape126 f g inputs siblings]
  rfl
#print axioms shape135
def input136 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash136.message
def value136 : State := JFp_SHADigest.output JHc_Gr_M1.Hash136.result
theorem cast136_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash136.B00.input).map Fin.val=JHc_Gr_M1.Hash136.B00.input := by rfl
#print axioms cast136_0
theorem tail136 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash136.tail).map Fin.val=JHc_Gr_M1.Hash136.tail := by rfl
#print axioms tail136
theorem numeric136 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash136.message).map Fin.val=JHc_Gr_M1.Hash136.message := by
  simp only [JHc_Gr_M1.Hash136.message,JHc_Gr_M1.Hash136.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast136_0,tail136]
#print axioms numeric136
theorem hash136 : JFp_SHADigest.digest input136=value136 := by
  unfold input136 JFp_SHADigest.digest
  rw [numeric136,JHc_Gr_M1.Hash136.checked]
  rfl
#print axioms hash136
theorem address136 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [153,133,221,15,146,6,115,140,230,185,130,26,225,15,86,62,76,251,182,229,99,145,33,151,46,29,16,78,20,210,184,89]) value127)=input136 := by rfl
#print axioms address136
def tree136 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [153,133,221,15,146,6,115,140,230,185,130,26,225,15,86,62,76,251,182,229,99,145,33,151,46,29,16,78,20,210,184,89])) tree127
theorem root136 : root JFp_SHADigest.digest tree136=value136 := by
  rw [tree136,root,root127]
  exact (congrArg JFp_SHADigest.digest address136).trans hash136
#print axioms root136
theorem shape136 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 204800=tree136 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 204800)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 12 204800 (by decide),siblings 12 (by decide) 204800 (by decide)]
  rw [shape127 f g inputs siblings]
  rfl
#print axioms shape136
def input137 : Bytes := JGh_TX2_M1Roots.input165
def value137 : State := JGh_TX2_M1Roots.value165
theorem hash137 : JFp_SHADigest.digest input137=value137 := JGh_TX2_M1Roots.hash165
#print axioms hash137
theorem address137 : BinMerkle32Path.nodeInput (children value128 (JGc_TX2_HashBytes.state [66,199,69,31,236,191,95,45,107,250,179,40,169,78,64,209,27,26,172,83,225,86,252,237,38,168,176,210,39,212,103,98]))=input137 := by rfl
#print axioms address137
def tree137 : Tree := .branch tree128 (.supplied (JGc_TX2_HashBytes.state [66,199,69,31,236,191,95,45,107,250,179,40,169,78,64,209,27,26,172,83,225,86,252,237,38,168,176,210,39,212,103,98]))
theorem root137 : root JFp_SHADigest.digest tree137=value137 := by
  rw [tree137,root,root128]
  exact (congrArg JFp_SHADigest.digest address137).trans hash137
#print axioms root137
theorem shape137 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 212992=tree137 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 212992)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape128 f g inputs siblings]
  rw [unoccupied f g 12 217088 (by decide),siblings 12 (by decide) 217088 (by decide)]
  rfl
#print axioms shape137
def input138 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash138.message
def value138 : State := JFp_SHADigest.output JHc_Gr_M1.Hash138.result
theorem cast138_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash138.B00.input).map Fin.val=JHc_Gr_M1.Hash138.B00.input := by rfl
#print axioms cast138_0
theorem tail138 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash138.tail).map Fin.val=JHc_Gr_M1.Hash138.tail := by rfl
#print axioms tail138
theorem numeric138 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash138.message).map Fin.val=JHc_Gr_M1.Hash138.message := by
  simp only [JHc_Gr_M1.Hash138.message,JHc_Gr_M1.Hash138.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast138_0,tail138]
#print axioms numeric138
theorem hash138 : JFp_SHADigest.digest input138=value138 := by
  unfold input138 JFp_SHADigest.digest
  rw [numeric138,JHc_Gr_M1.Hash138.checked]
  rfl
#print axioms hash138
theorem address138 : BinMerkle32Path.nodeInput (children value129 (JGc_TX2_HashBytes.state [235,175,68,146,148,50,230,240,90,237,138,62,236,194,107,145,48,135,75,194,84,203,138,124,153,6,202,37,189,117,252,127]))=input138 := by rfl
#print axioms address138
def tree138 : Tree := .branch tree129 (.supplied (JGc_TX2_HashBytes.state [235,175,68,146,148,50,230,240,90,237,138,62,236,194,107,145,48,135,75,194,84,203,138,124,153,6,202,37,189,117,252,127]))
theorem root138 : root JFp_SHADigest.digest tree138=value138 := by
  rw [tree138,root,root129]
  exact (congrArg JFp_SHADigest.digest address138).trans hash138
#print axioms root138
theorem shape138 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 245760=tree138 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 245760)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape129 f g inputs siblings]
  rw [unoccupied f g 12 249856 (by decide),siblings 12 (by decide) 249856 (by decide)]
  rfl
#print axioms shape138
end AspisR1.JHc_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input139 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash139.message
def value139 : State := JFp_SHADigest.output JHc_Gr_M1.Hash139.result
theorem cast139_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash139.B00.input).map Fin.val=JHc_Gr_M1.Hash139.B00.input := by rfl
#print axioms cast139_0
theorem tail139 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash139.tail).map Fin.val=JHc_Gr_M1.Hash139.tail := by rfl
#print axioms tail139
theorem numeric139 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash139.message).map Fin.val=JHc_Gr_M1.Hash139.message := by
  simp only [JHc_Gr_M1.Hash139.message,JHc_Gr_M1.Hash139.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast139_0,tail139]
#print axioms numeric139
theorem hash139 : JFp_SHADigest.digest input139=value139 := by
  unfold input139 JFp_SHADigest.digest
  rw [numeric139,JHc_Gr_M1.Hash139.checked]
  rfl
#print axioms hash139
theorem address139 : BinMerkle32Path.nodeInput (children value130 (JGc_TX2_HashBytes.state [177,255,241,39,63,158,40,191,219,173,167,140,60,212,238,89,156,75,131,173,118,46,23,106,164,61,132,56,29,231,180,242]))=input139 := by rfl
#print axioms address139
def tree139 : Tree := .branch tree130 (.supplied (JGc_TX2_HashBytes.state [177,255,241,39,63,158,40,191,219,173,167,140,60,212,238,89,156,75,131,173,118,46,23,106,164,61,132,56,29,231,180,242]))
theorem root139 : root JFp_SHADigest.digest tree139=value139 := by
  rw [tree139,root,root130]
  exact (congrArg JFp_SHADigest.digest address139).trans hash139
#print axioms root139
theorem shape139 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 65536=tree139 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 65536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape130 f g inputs siblings]
  rw [unoccupied f g 13 73728 (by decide),siblings 13 (by decide) 73728 (by decide)]
  rfl
#print axioms shape139
def input140 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash140.message
def value140 : State := JFp_SHADigest.output JHc_Gr_M1.Hash140.result
theorem cast140_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash140.B00.input).map Fin.val=JHc_Gr_M1.Hash140.B00.input := by rfl
#print axioms cast140_0
theorem tail140 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash140.tail).map Fin.val=JHc_Gr_M1.Hash140.tail := by rfl
#print axioms tail140
theorem numeric140 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash140.message).map Fin.val=JHc_Gr_M1.Hash140.message := by
  simp only [JHc_Gr_M1.Hash140.message,JHc_Gr_M1.Hash140.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast140_0,tail140]
#print axioms numeric140
theorem hash140 : JFp_SHADigest.digest input140=value140 := by
  unfold input140 JFp_SHADigest.digest
  rw [numeric140,JHc_Gr_M1.Hash140.checked]
  rfl
#print axioms hash140
theorem address140 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [148,97,246,244,46,229,113,211,171,213,134,17,121,11,39,232,115,93,64,237,78,176,97,138,178,248,71,111,201,205,160,225]) value131)=input140 := by rfl
#print axioms address140
def tree140 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [148,97,246,244,46,229,113,211,171,213,134,17,121,11,39,232,115,93,64,237,78,176,97,138,178,248,71,111,201,205,160,225])) tree131
theorem root140 : root JFp_SHADigest.digest tree140=value140 := by
  rw [tree140,root,root131]
  exact (congrArg JFp_SHADigest.digest address140).trans hash140
#print axioms root140
theorem shape140 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 81920=tree140 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 81920)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 13 81920 (by decide),siblings 13 (by decide) 81920 (by decide)]
  rw [shape131 f g inputs siblings]
  rfl
#print axioms shape140
def input141 : Bytes := JGh_TX2_M1Roots.input171
def value141 : State := JGh_TX2_M1Roots.value171
theorem hash141 : JFp_SHADigest.digest input141=value141 := JGh_TX2_M1Roots.hash171
#print axioms hash141
theorem address141 : BinMerkle32Path.nodeInput (children value132 value133)=input141 := by rfl
#print axioms address141
def tree141 : Tree := .branch tree132 tree133
theorem root141 : root JFp_SHADigest.digest tree141=value141 := by
  rw [tree141,root,root132,root133]
  exact (congrArg JFp_SHADigest.digest address141).trans hash141
#print axioms root141
theorem shape141 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 147456=tree141 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 147456)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape132 f g inputs siblings]
  rw [shape133 f g inputs siblings]
  rfl
#print axioms shape141
def input142 : Bytes := JGh_TX2_M1Roots.input173
def value142 : State := JGh_TX2_M1Roots.value173
theorem hash142 : JFp_SHADigest.digest input142=value142 := JGh_TX2_M1Roots.hash173
#print axioms hash142
theorem address142 : BinMerkle32Path.nodeInput (children value134 value135)=input142 := by rfl
#print axioms address142
def tree142 : Tree := .branch tree134 tree135
theorem root142 : root JFp_SHADigest.digest tree142=value142 := by
  rw [tree142,root,root134,root135]
  exact (congrArg JFp_SHADigest.digest address142).trans hash142
#print axioms root142
theorem shape142 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 180224=tree142 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 180224)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape134 f g inputs siblings]
  rw [shape135 f g inputs siblings]
  rfl
#print axioms shape142
def input143 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash143.message
def value143 : State := JFp_SHADigest.output JHc_Gr_M1.Hash143.result
theorem cast143_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash143.B00.input).map Fin.val=JHc_Gr_M1.Hash143.B00.input := by rfl
#print axioms cast143_0
theorem tail143 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash143.tail).map Fin.val=JHc_Gr_M1.Hash143.tail := by rfl
#print axioms tail143
theorem numeric143 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash143.message).map Fin.val=JHc_Gr_M1.Hash143.message := by
  simp only [JHc_Gr_M1.Hash143.message,JHc_Gr_M1.Hash143.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast143_0,tail143]
#print axioms numeric143
theorem hash143 : JFp_SHADigest.digest input143=value143 := by
  unfold input143 JFp_SHADigest.digest
  rw [numeric143,JHc_Gr_M1.Hash143.checked]
  rfl
#print axioms hash143
theorem address143 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [241,9,125,109,23,20,73,46,243,31,183,201,254,168,254,9,17,216,58,151,34,255,100,136,213,89,115,87,251,31,157,167]) value136)=input143 := by rfl
#print axioms address143
def tree143 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [241,9,125,109,23,20,73,46,243,31,183,201,254,168,254,9,17,216,58,151,34,255,100,136,213,89,115,87,251,31,157,167])) tree136
theorem root143 : root JFp_SHADigest.digest tree143=value143 := by
  rw [tree143,root,root136]
  exact (congrArg JFp_SHADigest.digest address143).trans hash143
#print axioms root143
theorem shape143 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 196608=tree143 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 196608)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 13 196608 (by decide),siblings 13 (by decide) 196608 (by decide)]
  rw [shape136 f g inputs siblings]
  rfl
#print axioms shape143
def input144 : Bytes := JGh_TX2_M1Roots.input174
def value144 : State := JGh_TX2_M1Roots.value174
theorem hash144 : JFp_SHADigest.digest input144=value144 := JGh_TX2_M1Roots.hash174
#print axioms hash144
theorem address144 : BinMerkle32Path.nodeInput (children value137 (JGc_TX2_HashBytes.state [231,175,9,73,193,151,78,114,131,10,124,215,162,10,201,179,141,208,35,230,20,155,240,194,241,32,103,192,199,110,107,27]))=input144 := by rfl
#print axioms address144
def tree144 : Tree := .branch tree137 (.supplied (JGc_TX2_HashBytes.state [231,175,9,73,193,151,78,114,131,10,124,215,162,10,201,179,141,208,35,230,20,155,240,194,241,32,103,192,199,110,107,27]))
theorem root144 : root JFp_SHADigest.digest tree144=value144 := by
  rw [tree144,root,root137]
  exact (congrArg JFp_SHADigest.digest address144).trans hash144
#print axioms root144
theorem shape144 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 212992=tree144 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 212992)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape137 f g inputs siblings]
  rw [unoccupied f g 13 221184 (by decide),siblings 13 (by decide) 221184 (by decide)]
  rfl
#print axioms shape144
def input145 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash145.message
def value145 : State := JFp_SHADigest.output JHc_Gr_M1.Hash145.result
theorem cast145_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash145.B00.input).map Fin.val=JHc_Gr_M1.Hash145.B00.input := by rfl
#print axioms cast145_0
theorem tail145 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash145.tail).map Fin.val=JHc_Gr_M1.Hash145.tail := by rfl
#print axioms tail145
theorem numeric145 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash145.message).map Fin.val=JHc_Gr_M1.Hash145.message := by
  simp only [JHc_Gr_M1.Hash145.message,JHc_Gr_M1.Hash145.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast145_0,tail145]
#print axioms numeric145
theorem hash145 : JFp_SHADigest.digest input145=value145 := by
  unfold input145 JFp_SHADigest.digest
  rw [numeric145,JHc_Gr_M1.Hash145.checked]
  rfl
#print axioms hash145
theorem address145 : BinMerkle32Path.nodeInput (children value138 (JGc_TX2_HashBytes.state [105,88,192,232,209,36,116,6,166,207,65,248,208,208,199,3,9,32,125,251,202,216,178,45,163,37,132,171,119,243,170,2]))=input145 := by rfl
#print axioms address145
def tree145 : Tree := .branch tree138 (.supplied (JGc_TX2_HashBytes.state [105,88,192,232,209,36,116,6,166,207,65,248,208,208,199,3,9,32,125,251,202,216,178,45,163,37,132,171,119,243,170,2]))
theorem root145 : root JFp_SHADigest.digest tree145=value145 := by
  rw [tree145,root,root138]
  exact (congrArg JFp_SHADigest.digest address145).trans hash145
#print axioms root145
theorem shape145 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 14 245760=tree145 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 14 245760)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape138 f g inputs siblings]
  rw [unoccupied f g 13 253952 (by decide),siblings 13 (by decide) 253952 (by decide)]
  rfl
#print axioms shape145
end AspisR1.JHc_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input146 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash146.message
def value146 : State := JFp_SHADigest.output JHc_Gr_M1.Hash146.result
theorem cast146_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash146.B00.input).map Fin.val=JHc_Gr_M1.Hash146.B00.input := by rfl
#print axioms cast146_0
theorem tail146 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash146.tail).map Fin.val=JHc_Gr_M1.Hash146.tail := by rfl
#print axioms tail146
theorem numeric146 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash146.message).map Fin.val=JHc_Gr_M1.Hash146.message := by
  simp only [JHc_Gr_M1.Hash146.message,JHc_Gr_M1.Hash146.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast146_0,tail146]
#print axioms numeric146
theorem hash146 : JFp_SHADigest.digest input146=value146 := by
  unfold input146 JFp_SHADigest.digest
  rw [numeric146,JHc_Gr_M1.Hash146.checked]
  rfl
#print axioms hash146
theorem address146 : BinMerkle32Path.nodeInput (children value139 value140)=input146 := by rfl
#print axioms address146
def tree146 : Tree := .branch tree139 tree140
theorem root146 : root JFp_SHADigest.digest tree146=value146 := by
  rw [tree146,root,root139,root140]
  exact (congrArg JFp_SHADigest.digest address146).trans hash146
#print axioms root146
theorem shape146 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 15 65536=tree146 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 15 65536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape139 f g inputs siblings]
  rw [shape140 f g inputs siblings]
  rfl
#print axioms shape146
def input147 : Bytes := JGh_TX2_M1Roots.input177
def value147 : State := JGh_TX2_M1Roots.value177
theorem hash147 : JFp_SHADigest.digest input147=value147 := JGh_TX2_M1Roots.hash177
#print axioms hash147
theorem address147 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [77,119,158,98,145,125,73,201,211,192,209,42,9,218,8,172,52,75,152,66,203,147,195,144,242,0,78,78,51,239,33,225]) value141)=input147 := by rfl
#print axioms address147
def tree147 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [77,119,158,98,145,125,73,201,211,192,209,42,9,218,8,172,52,75,152,66,203,147,195,144,242,0,78,78,51,239,33,225])) tree141
theorem root147 : root JFp_SHADigest.digest tree147=value147 := by
  rw [tree147,root,root141]
  exact (congrArg JFp_SHADigest.digest address147).trans hash147
#print axioms root147
theorem shape147 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 15 131072=tree147 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 15 131072)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 14 131072 (by decide),siblings 14 (by decide) 131072 (by decide)]
  rw [shape141 f g inputs siblings]
  rfl
#print axioms shape147
def input148 : Bytes := JGh_TX2_M1Roots.input178
def value148 : State := JGh_TX2_M1Roots.value178
theorem hash148 : JFp_SHADigest.digest input148=value148 := JGh_TX2_M1Roots.hash178
#print axioms hash148
theorem address148 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [157,235,230,58,63,44,109,204,141,127,215,154,149,77,102,74,49,129,237,95,214,147,79,111,35,41,106,166,126,167,43,139]) value142)=input148 := by rfl
#print axioms address148
def tree148 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [157,235,230,58,63,44,109,204,141,127,215,154,149,77,102,74,49,129,237,95,214,147,79,111,35,41,106,166,126,167,43,139])) tree142
theorem root148 : root JFp_SHADigest.digest tree148=value148 := by
  rw [tree148,root,root142]
  exact (congrArg JFp_SHADigest.digest address148).trans hash148
#print axioms root148
theorem shape148 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 15 163840=tree148 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 15 163840)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 14 163840 (by decide),siblings 14 (by decide) 163840 (by decide)]
  rw [shape142 f g inputs siblings]
  rfl
#print axioms shape148
def input149 : Bytes := JGh_TX2_M1Roots.input179
def value149 : State := JGh_TX2_M1Roots.value179
theorem hash149 : JFp_SHADigest.digest input149=value149 := JGh_TX2_M1Roots.hash179
#print axioms hash149
theorem address149 : BinMerkle32Path.nodeInput (children value143 value144)=input149 := by rfl
#print axioms address149
def tree149 : Tree := .branch tree143 tree144
theorem root149 : root JFp_SHADigest.digest tree149=value149 := by
  rw [tree149,root,root143,root144]
  exact (congrArg JFp_SHADigest.digest address149).trans hash149
#print axioms root149
theorem shape149 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 15 196608=tree149 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 15 196608)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape143 f g inputs siblings]
  rw [shape144 f g inputs siblings]
  rfl
#print axioms shape149
def input150 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash150.message
def value150 : State := JFp_SHADigest.output JHc_Gr_M1.Hash150.result
theorem cast150_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash150.B00.input).map Fin.val=JHc_Gr_M1.Hash150.B00.input := by rfl
#print axioms cast150_0
theorem tail150 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash150.tail).map Fin.val=JHc_Gr_M1.Hash150.tail := by rfl
#print axioms tail150
theorem numeric150 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash150.message).map Fin.val=JHc_Gr_M1.Hash150.message := by
  simp only [JHc_Gr_M1.Hash150.message,JHc_Gr_M1.Hash150.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast150_0,tail150]
#print axioms numeric150
theorem hash150 : JFp_SHADigest.digest input150=value150 := by
  unfold input150 JFp_SHADigest.digest
  rw [numeric150,JHc_Gr_M1.Hash150.checked]
  rfl
#print axioms hash150
theorem address150 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [103,29,162,204,20,167,88,231,167,150,223,135,176,35,230,214,140,125,223,169,142,173,29,189,226,61,203,233,25,171,3,193]) value145)=input150 := by rfl
#print axioms address150
def tree150 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [103,29,162,204,20,167,88,231,167,150,223,135,176,35,230,214,140,125,223,169,142,173,29,189,226,61,203,233,25,171,3,193])) tree145
theorem root150 : root JFp_SHADigest.digest tree150=value150 := by
  rw [tree150,root,root145]
  exact (congrArg JFp_SHADigest.digest address150).trans hash150
#print axioms root150
theorem shape150 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 15 229376=tree150 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 15 229376)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 14 229376 (by decide),siblings 14 (by decide) 229376 (by decide)]
  rw [shape145 f g inputs siblings]
  rfl
#print axioms shape150
end AspisR1.JHc_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input151 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash151.message
def value151 : State := JFp_SHADigest.output JHc_Gr_M1.Hash151.result
theorem cast151_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash151.B00.input).map Fin.val=JHc_Gr_M1.Hash151.B00.input := by rfl
#print axioms cast151_0
theorem tail151 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash151.tail).map Fin.val=JHc_Gr_M1.Hash151.tail := by rfl
#print axioms tail151
theorem numeric151 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash151.message).map Fin.val=JHc_Gr_M1.Hash151.message := by
  simp only [JHc_Gr_M1.Hash151.message,JHc_Gr_M1.Hash151.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast151_0,tail151]
#print axioms numeric151
theorem hash151 : JFp_SHADigest.digest input151=value151 := by
  unfold input151 JFp_SHADigest.digest
  rw [numeric151,JHc_Gr_M1.Hash151.checked]
  rfl
#print axioms hash151
theorem address151 : BinMerkle32Path.nodeInput (children value146 (JGc_TX2_HashBytes.state [169,24,176,242,33,202,155,23,158,103,13,74,131,251,160,53,65,59,10,90,129,75,172,213,105,163,148,32,103,32,15,160]))=input151 := by rfl
#print axioms address151
def tree151 : Tree := .branch tree146 (.supplied (JGc_TX2_HashBytes.state [169,24,176,242,33,202,155,23,158,103,13,74,131,251,160,53,65,59,10,90,129,75,172,213,105,163,148,32,103,32,15,160]))
theorem root151 : root JFp_SHADigest.digest tree151=value151 := by
  rw [tree151,root,root146]
  exact (congrArg JFp_SHADigest.digest address151).trans hash151
#print axioms root151
theorem shape151 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 16 65536=tree151 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 16 65536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape146 f g inputs siblings]
  rw [unoccupied f g 15 98304 (by decide),siblings 15 (by decide) 98304 (by decide)]
  rfl
#print axioms shape151
def input152 : Bytes := JGh_TX2_M1Roots.input181
def value152 : State := JGh_TX2_M1Roots.value181
theorem hash152 : JFp_SHADigest.digest input152=value152 := JGh_TX2_M1Roots.hash181
#print axioms hash152
theorem address152 : BinMerkle32Path.nodeInput (children value147 value148)=input152 := by rfl
#print axioms address152
def tree152 : Tree := .branch tree147 tree148
theorem root152 : root JFp_SHADigest.digest tree152=value152 := by
  rw [tree152,root,root147,root148]
  exact (congrArg JFp_SHADigest.digest address152).trans hash152
#print axioms root152
theorem shape152 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 16 131072=tree152 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 16 131072)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape147 f g inputs siblings]
  rw [shape148 f g inputs siblings]
  rfl
#print axioms shape152
def input153 : Bytes := JGh_TX2_M1Roots.input182
def value153 : State := JGh_TX2_M1Roots.value182
theorem hash153 : JFp_SHADigest.digest input153=value153 := JGh_TX2_M1Roots.hash182
#print axioms hash153
theorem address153 : BinMerkle32Path.nodeInput (children value149 value150)=input153 := by rfl
#print axioms address153
def tree153 : Tree := .branch tree149 tree150
theorem root153 : root JFp_SHADigest.digest tree153=value153 := by
  rw [tree153,root,root149,root150]
  exact (congrArg JFp_SHADigest.digest address153).trans hash153
#print axioms root153
theorem shape153 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 16 196608=tree153 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 16 196608)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape149 f g inputs siblings]
  rw [shape150 f g inputs siblings]
  rfl
#print axioms shape153
end AspisR1.JHc_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input154 : Bytes := JGh_TX2_M1Roots.input183
def value154 : State := JGh_TX2_M1Roots.value183
theorem hash154 : JFp_SHADigest.digest input154=value154 := JGh_TX2_M1Roots.hash183
#print axioms hash154
theorem address154 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [141,210,29,143,172,113,121,140,232,80,9,198,209,48,160,240,216,160,117,117,21,164,211,65,104,173,187,170,81,120,182,252]) value151)=input154 := by rfl
#print axioms address154
def tree154 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [141,210,29,143,172,113,121,140,232,80,9,198,209,48,160,240,216,160,117,117,21,164,211,65,104,173,187,170,81,120,182,252])) tree151
theorem root154 : root JFp_SHADigest.digest tree154=value154 := by
  rw [tree154,root,root151]
  exact (congrArg JFp_SHADigest.digest address154).trans hash154
#print axioms root154
theorem shape154 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 17 0=tree154 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 17 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 16 0 (by decide),siblings 16 (by decide) 0 (by decide)]
  rw [shape151 f g inputs siblings]
  rfl
#print axioms shape154
def input155 : Bytes := JGh_TX2_M1Roots.input184
def value155 : State := JGh_TX2_M1Roots.value184
theorem hash155 : JFp_SHADigest.digest input155=value155 := JGh_TX2_M1Roots.hash184
#print axioms hash155
theorem address155 : BinMerkle32Path.nodeInput (children value152 value153)=input155 := by rfl
#print axioms address155
def tree155 : Tree := .branch tree152 tree153
theorem root155 : root JFp_SHADigest.digest tree155=value155 := by
  rw [tree155,root,root152,root153]
  exact (congrArg JFp_SHADigest.digest address155).trans hash155
#print axioms root155
theorem shape155 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 17 131072=tree155 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 17 131072)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape152 f g inputs siblings]
  rw [shape153 f g inputs siblings]
  rfl
#print axioms shape155
end AspisR1.JHc_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input156 : Bytes := JGh_TX2_M1Roots.input185
def value156 : State := JGh_TX2_M1Roots.value185
theorem hash156 : JFp_SHADigest.digest input156=value156 := JGh_TX2_M1Roots.hash185
#print axioms hash156
theorem address156 : BinMerkle32Path.nodeInput (children value154 value155)=input156 := by rfl
#print axioms address156
def tree156 : Tree := .branch tree154 tree155
theorem root156 : root JFp_SHADigest.digest tree156=value156 := by
  rw [tree156,root,root154,root155]
  exact (congrArg JFp_SHADigest.digest address156).trans hash156
#print axioms root156
theorem shape156 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 18 0=tree156 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 18 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape154 f g inputs siblings]
  rw [shape155 f g inputs siblings]
  rfl
#print axioms shape156
end AspisR1.JHc_Gr_M1Roots
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M1Root
open Aeneas Aeneas.Std
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiBuild OracleDecisionMultiTree JHc_Gr_M1Roots

def retainedRoot : State := JGh_TX2_M1Root.retainedRoot

theorem value_eq : value156=retainedRoot := by
  funext i
  fin_cases i <;> rfl
#print axioms value_eq

theorem source (f : Nat → Bytes) (g : Nat → Nat → State)
    (inputs : InputLaw f) (siblings : SiblingLaw g) :
    root JFp_SHADigest.digest (build indices f g 18 0)=retainedRoot := by
  rw [shape156 f g inputs siblings,root156,value_eq]
#print axioms source

theorem selected_queries : OraclePortSelectedDraft.selected
    (Port4B_KeyInstall.queries JFo_Prepared.value.queries) 0 1=indices := rfl
#print axioms selected_queries

theorem inhabited : ∃ (f : Nat → Bytes) (g : Nat → Nat → State),
    InputLaw f ∧ SiblingLaw g ∧
    root JFp_SHADigest.digest (build indices f g 18 0)=retainedRoot :=
  ⟨inputAt,siblingAt,(by intro b _;rfl),(by intro h _ b _;rfl),
    source inputAt siblingAt (by intro b _;rfl) (by intro h _ b _;rfl)⟩
#print axioms inhabited
end AspisR1.JHc_Gr_M1Root
end
