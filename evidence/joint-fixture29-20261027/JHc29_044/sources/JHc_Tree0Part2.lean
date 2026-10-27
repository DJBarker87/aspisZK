import JHc_Tree0Part1
import JHc_Certs0_11
import JHc_Certs0_12
import JGf_TX2_M0Root
import JHc_Certs0_13
import JHc_Certs0_14
import JGe_View
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input100 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash100.message
def value100 : State := JFp_SHADigest.output JHc_Gr_M0.Hash100.result
theorem cast100_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash100.B00.input).map Fin.val=JHc_Gr_M0.Hash100.B00.input := by rfl
#print axioms cast100_0
theorem tail100 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash100.tail).map Fin.val=JHc_Gr_M0.Hash100.tail := by rfl
#print axioms tail100
theorem numeric100 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash100.message).map Fin.val=JHc_Gr_M0.Hash100.message := by
  simp only [JHc_Gr_M0.Hash100.message,JHc_Gr_M0.Hash100.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast100_0,tail100]
#print axioms numeric100
theorem hash100 : JFp_SHADigest.digest input100=value100 := by
  unfold input100 JFp_SHADigest.digest
  rw [numeric100,JHc_Gr_M0.Hash100.checked]
  rfl
#print axioms hash100
theorem address100 : BinMerkle32Path.nodeInput (children value090 (JGc_TX2_HashBytes.state [23,74,195,49,213,135,245,27,57,199,58,222,148,196,183,123,71,5,192,127,140,213,208,209,54,153,86,127,135,105,132,180]))=input100 := by rfl
#print axioms address100
def tree100 : Tree := .branch tree090 (.supplied (JGc_TX2_HashBytes.state [23,74,195,49,213,135,245,27,57,199,58,222,148,196,183,123,71,5,192,127,140,213,208,209,54,153,86,127,135,105,132,180]))
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
def input101 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash101.message
def value101 : State := JFp_SHADigest.output JHc_Gr_M0.Hash101.result
theorem cast101_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash101.B00.input).map Fin.val=JHc_Gr_M0.Hash101.B00.input := by rfl
#print axioms cast101_0
theorem tail101 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash101.tail).map Fin.val=JHc_Gr_M0.Hash101.tail := by rfl
#print axioms tail101
theorem numeric101 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash101.message).map Fin.val=JHc_Gr_M0.Hash101.message := by
  simp only [JHc_Gr_M0.Hash101.message,JHc_Gr_M0.Hash101.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast101_0,tail101]
#print axioms numeric101
theorem hash101 : JFp_SHADigest.digest input101=value101 := by
  unfold input101 JFp_SHADigest.digest
  rw [numeric101,JHc_Gr_M0.Hash101.checked]
  rfl
#print axioms hash101
theorem address101 : BinMerkle32Path.nodeInput (children value091 (JGc_TX2_HashBytes.state [247,170,236,136,32,227,215,1,30,170,171,104,222,196,102,119,141,43,224,250,73,121,228,110,63,169,195,18,64,55,103,111]))=input101 := by rfl
#print axioms address101
def tree101 : Tree := .branch tree091 (.supplied (JGc_TX2_HashBytes.state [247,170,236,136,32,227,215,1,30,170,171,104,222,196,102,119,141,43,224,250,73,121,228,110,63,169,195,18,64,55,103,111]))
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
def input102 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash102.message
def value102 : State := JFp_SHADigest.output JHc_Gr_M0.Hash102.result
theorem cast102_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash102.B00.input).map Fin.val=JHc_Gr_M0.Hash102.B00.input := by rfl
#print axioms cast102_0
theorem tail102 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash102.tail).map Fin.val=JHc_Gr_M0.Hash102.tail := by rfl
#print axioms tail102
theorem numeric102 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash102.message).map Fin.val=JHc_Gr_M0.Hash102.message := by
  simp only [JHc_Gr_M0.Hash102.message,JHc_Gr_M0.Hash102.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast102_0,tail102]
#print axioms numeric102
theorem hash102 : JFp_SHADigest.digest input102=value102 := by
  unfold input102 JFp_SHADigest.digest
  rw [numeric102,JHc_Gr_M0.Hash102.checked]
  rfl
#print axioms hash102
theorem address102 : BinMerkle32Path.nodeInput (children value092 (JGc_TX2_HashBytes.state [190,108,13,171,84,192,94,96,227,48,105,48,244,245,190,168,224,83,16,169,249,226,55,97,180,229,154,227,86,36,50,122]))=input102 := by rfl
#print axioms address102
def tree102 : Tree := .branch tree092 (.supplied (JGc_TX2_HashBytes.state [190,108,13,171,84,192,94,96,227,48,105,48,244,245,190,168,224,83,16,169,249,226,55,97,180,229,154,227,86,36,50,122]))
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
def input103 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash103.message
def value103 : State := JFp_SHADigest.output JHc_Gr_M0.Hash103.result
theorem cast103_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash103.B00.input).map Fin.val=JHc_Gr_M0.Hash103.B00.input := by rfl
#print axioms cast103_0
theorem tail103 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash103.tail).map Fin.val=JHc_Gr_M0.Hash103.tail := by rfl
#print axioms tail103
theorem numeric103 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash103.message).map Fin.val=JHc_Gr_M0.Hash103.message := by
  simp only [JHc_Gr_M0.Hash103.message,JHc_Gr_M0.Hash103.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast103_0,tail103]
#print axioms numeric103
theorem hash103 : JFp_SHADigest.digest input103=value103 := by
  unfold input103 JFp_SHADigest.digest
  rw [numeric103,JHc_Gr_M0.Hash103.checked]
  rfl
#print axioms hash103
theorem address103 : BinMerkle32Path.nodeInput (children value093 (JGc_TX2_HashBytes.state [157,66,177,205,179,25,156,253,216,204,238,141,248,146,126,57,146,197,187,130,191,130,41,226,29,137,114,88,159,239,90,188]))=input103 := by rfl
#print axioms address103
def tree103 : Tree := .branch tree093 (.supplied (JGc_TX2_HashBytes.state [157,66,177,205,179,25,156,253,216,204,238,141,248,146,126,57,146,197,187,130,191,130,41,226,29,137,114,88,159,239,90,188]))
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
def input104 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash104.message
def value104 : State := JFp_SHADigest.output JHc_Gr_M0.Hash104.result
theorem cast104_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash104.B00.input).map Fin.val=JHc_Gr_M0.Hash104.B00.input := by rfl
#print axioms cast104_0
theorem tail104 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash104.tail).map Fin.val=JHc_Gr_M0.Hash104.tail := by rfl
#print axioms tail104
theorem numeric104 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash104.message).map Fin.val=JHc_Gr_M0.Hash104.message := by
  simp only [JHc_Gr_M0.Hash104.message,JHc_Gr_M0.Hash104.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast104_0,tail104]
#print axioms numeric104
theorem hash104 : JFp_SHADigest.digest input104=value104 := by
  unfold input104 JFp_SHADigest.digest
  rw [numeric104,JHc_Gr_M0.Hash104.checked]
  rfl
#print axioms hash104
theorem address104 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [79,115,19,153,165,205,224,136,61,186,168,120,162,67,201,141,134,174,172,243,21,240,241,100,42,229,53,233,153,170,42,41]) value094)=input104 := by rfl
#print axioms address104
def tree104 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [79,115,19,153,165,205,224,136,61,186,168,120,162,67,201,141,134,174,172,243,21,240,241,100,42,229,53,233,153,170,42,41])) tree094
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
def input105 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash105.message
def value105 : State := JFp_SHADigest.output JHc_Gr_M0.Hash105.result
theorem cast105_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash105.B00.input).map Fin.val=JHc_Gr_M0.Hash105.B00.input := by rfl
#print axioms cast105_0
theorem tail105 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash105.tail).map Fin.val=JHc_Gr_M0.Hash105.tail := by rfl
#print axioms tail105
theorem numeric105 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash105.message).map Fin.val=JHc_Gr_M0.Hash105.message := by
  simp only [JHc_Gr_M0.Hash105.message,JHc_Gr_M0.Hash105.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast105_0,tail105]
#print axioms numeric105
theorem hash105 : JFp_SHADigest.digest input105=value105 := by
  unfold input105 JFp_SHADigest.digest
  rw [numeric105,JHc_Gr_M0.Hash105.checked]
  rfl
#print axioms hash105
theorem address105 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [148,43,99,22,57,180,71,36,176,106,37,117,42,190,120,213,40,143,126,3,58,186,68,221,194,74,60,125,229,230,106,79]) value095)=input105 := by rfl
#print axioms address105
def tree105 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [148,43,99,22,57,180,71,36,176,106,37,117,42,190,120,213,40,143,126,3,58,186,68,221,194,74,60,125,229,230,106,79])) tree095
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
def input106 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash106.message
def value106 : State := JFp_SHADigest.output JHc_Gr_M0.Hash106.result
theorem cast106_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash106.B00.input).map Fin.val=JHc_Gr_M0.Hash106.B00.input := by rfl
#print axioms cast106_0
theorem tail106 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash106.tail).map Fin.val=JHc_Gr_M0.Hash106.tail := by rfl
#print axioms tail106
theorem numeric106 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash106.message).map Fin.val=JHc_Gr_M0.Hash106.message := by
  simp only [JHc_Gr_M0.Hash106.message,JHc_Gr_M0.Hash106.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast106_0,tail106]
#print axioms numeric106
theorem hash106 : JFp_SHADigest.digest input106=value106 := by
  unfold input106 JFp_SHADigest.digest
  rw [numeric106,JHc_Gr_M0.Hash106.checked]
  rfl
#print axioms hash106
theorem address106 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [207,102,135,191,134,26,82,182,249,62,205,164,72,118,227,234,90,100,188,183,151,160,216,216,200,245,4,24,126,19,178,5]) value096)=input106 := by rfl
#print axioms address106
def tree106 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [207,102,135,191,134,26,82,182,249,62,205,164,72,118,227,234,90,100,188,183,151,160,216,216,200,245,4,24,126,19,178,5])) tree096
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
def input107 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash107.message
def value107 : State := JFp_SHADigest.output JHc_Gr_M0.Hash107.result
theorem cast107_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash107.B00.input).map Fin.val=JHc_Gr_M0.Hash107.B00.input := by rfl
#print axioms cast107_0
theorem tail107 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash107.tail).map Fin.val=JHc_Gr_M0.Hash107.tail := by rfl
#print axioms tail107
theorem numeric107 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash107.message).map Fin.val=JHc_Gr_M0.Hash107.message := by
  simp only [JHc_Gr_M0.Hash107.message,JHc_Gr_M0.Hash107.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast107_0,tail107]
#print axioms numeric107
theorem hash107 : JFp_SHADigest.digest input107=value107 := by
  unfold input107 JFp_SHADigest.digest
  rw [numeric107,JHc_Gr_M0.Hash107.checked]
  rfl
#print axioms hash107
theorem address107 : BinMerkle32Path.nodeInput (children value097 (JGc_TX2_HashBytes.state [136,24,60,241,94,194,126,24,120,244,56,48,145,68,42,168,200,103,87,128,189,66,104,116,209,245,141,65,97,81,150,11]))=input107 := by rfl
#print axioms address107
def tree107 : Tree := .branch tree097 (.supplied (JGc_TX2_HashBytes.state [136,24,60,241,94,194,126,24,120,244,56,48,145,68,42,168,200,103,87,128,189,66,104,116,209,245,141,65,97,81,150,11]))
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
def input108 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash108.message
def value108 : State := JFp_SHADigest.output JHc_Gr_M0.Hash108.result
theorem cast108_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash108.B00.input).map Fin.val=JHc_Gr_M0.Hash108.B00.input := by rfl
#print axioms cast108_0
theorem tail108 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash108.tail).map Fin.val=JHc_Gr_M0.Hash108.tail := by rfl
#print axioms tail108
theorem numeric108 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash108.message).map Fin.val=JHc_Gr_M0.Hash108.message := by
  simp only [JHc_Gr_M0.Hash108.message,JHc_Gr_M0.Hash108.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast108_0,tail108]
#print axioms numeric108
theorem hash108 : JFp_SHADigest.digest input108=value108 := by
  unfold input108 JFp_SHADigest.digest
  rw [numeric108,JHc_Gr_M0.Hash108.checked]
  rfl
#print axioms hash108
theorem address108 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [236,224,3,7,229,22,125,66,186,131,47,131,187,123,43,166,14,188,255,80,197,222,226,154,83,187,231,109,201,152,99,74]) value098)=input108 := by rfl
#print axioms address108
def tree108 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [236,224,3,7,229,22,125,66,186,131,47,131,187,123,43,166,14,188,255,80,197,222,226,154,83,187,231,109,201,152,99,74])) tree098
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
def input109 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash109.message
def value109 : State := JFp_SHADigest.output JHc_Gr_M0.Hash109.result
theorem cast109_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash109.B00.input).map Fin.val=JHc_Gr_M0.Hash109.B00.input := by rfl
#print axioms cast109_0
theorem tail109 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash109.tail).map Fin.val=JHc_Gr_M0.Hash109.tail := by rfl
#print axioms tail109
theorem numeric109 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash109.message).map Fin.val=JHc_Gr_M0.Hash109.message := by
  simp only [JHc_Gr_M0.Hash109.message,JHc_Gr_M0.Hash109.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast109_0,tail109]
#print axioms numeric109
theorem hash109 : JFp_SHADigest.digest input109=value109 := by
  unfold input109 JFp_SHADigest.digest
  rw [numeric109,JHc_Gr_M0.Hash109.checked]
  rfl
#print axioms hash109
theorem address109 : BinMerkle32Path.nodeInput (children value099 (JGc_TX2_HashBytes.state [129,168,53,62,31,143,67,207,71,169,96,123,137,17,208,1,3,164,237,62,64,109,62,71,117,71,184,169,224,169,104,142]))=input109 := by rfl
#print axioms address109
def tree109 : Tree := .branch tree099 (.supplied (JGc_TX2_HashBytes.state [129,168,53,62,31,143,67,207,71,169,96,123,137,17,208,1,3,164,237,62,64,109,62,71,117,71,184,169,224,169,104,142]))
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
end AspisR1.JHc_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input110 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash110.message
def value110 : State := JFp_SHADigest.output JHc_Gr_M0.Hash110.result
theorem cast110_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash110.B00.input).map Fin.val=JHc_Gr_M0.Hash110.B00.input := by rfl
#print axioms cast110_0
theorem tail110 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash110.tail).map Fin.val=JHc_Gr_M0.Hash110.tail := by rfl
#print axioms tail110
theorem numeric110 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash110.message).map Fin.val=JHc_Gr_M0.Hash110.message := by
  simp only [JHc_Gr_M0.Hash110.message,JHc_Gr_M0.Hash110.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast110_0,tail110]
#print axioms numeric110
theorem hash110 : JFp_SHADigest.digest input110=value110 := by
  unfold input110 JFp_SHADigest.digest
  rw [numeric110,JHc_Gr_M0.Hash110.checked]
  rfl
#print axioms hash110
theorem address110 : BinMerkle32Path.nodeInput (children value100 (JGc_TX2_HashBytes.state [152,162,255,196,212,132,122,99,218,255,12,162,24,58,6,29,109,82,79,82,141,97,174,54,239,110,201,1,108,154,177,68]))=input110 := by rfl
#print axioms address110
def tree110 : Tree := .branch tree100 (.supplied (JGc_TX2_HashBytes.state [152,162,255,196,212,132,122,99,218,255,12,162,24,58,6,29,109,82,79,82,141,97,174,54,239,110,201,1,108,154,177,68]))
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
def input111 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash111.message
def value111 : State := JFp_SHADigest.output JHc_Gr_M0.Hash111.result
theorem cast111_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash111.B00.input).map Fin.val=JHc_Gr_M0.Hash111.B00.input := by rfl
#print axioms cast111_0
theorem tail111 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash111.tail).map Fin.val=JHc_Gr_M0.Hash111.tail := by rfl
#print axioms tail111
theorem numeric111 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash111.message).map Fin.val=JHc_Gr_M0.Hash111.message := by
  simp only [JHc_Gr_M0.Hash111.message,JHc_Gr_M0.Hash111.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast111_0,tail111]
#print axioms numeric111
theorem hash111 : JFp_SHADigest.digest input111=value111 := by
  unfold input111 JFp_SHADigest.digest
  rw [numeric111,JHc_Gr_M0.Hash111.checked]
  rfl
#print axioms hash111
theorem address111 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [241,229,149,152,170,27,18,61,206,161,98,30,225,40,233,53,46,62,50,48,254,208,247,99,208,150,81,200,50,240,48,143]) value101)=input111 := by rfl
#print axioms address111
def tree111 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [241,229,149,152,170,27,18,61,206,161,98,30,225,40,233,53,46,62,50,48,254,208,247,99,208,150,81,200,50,240,48,143])) tree101
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
def input112 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash112.message
def value112 : State := JFp_SHADigest.output JHc_Gr_M0.Hash112.result
theorem cast112_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash112.B00.input).map Fin.val=JHc_Gr_M0.Hash112.B00.input := by rfl
#print axioms cast112_0
theorem tail112 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash112.tail).map Fin.val=JHc_Gr_M0.Hash112.tail := by rfl
#print axioms tail112
theorem numeric112 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash112.message).map Fin.val=JHc_Gr_M0.Hash112.message := by
  simp only [JHc_Gr_M0.Hash112.message,JHc_Gr_M0.Hash112.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast112_0,tail112]
#print axioms numeric112
theorem hash112 : JFp_SHADigest.digest input112=value112 := by
  unfold input112 JFp_SHADigest.digest
  rw [numeric112,JHc_Gr_M0.Hash112.checked]
  rfl
#print axioms hash112
theorem address112 : BinMerkle32Path.nodeInput (children value102 (JGc_TX2_HashBytes.state [207,160,0,107,107,203,186,65,189,180,20,58,15,97,7,28,17,81,82,78,101,147,184,188,37,229,216,233,181,44,255,192]))=input112 := by rfl
#print axioms address112
def tree112 : Tree := .branch tree102 (.supplied (JGc_TX2_HashBytes.state [207,160,0,107,107,203,186,65,189,180,20,58,15,97,7,28,17,81,82,78,101,147,184,188,37,229,216,233,181,44,255,192]))
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
def input113 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash113.message
def value113 : State := JFp_SHADigest.output JHc_Gr_M0.Hash113.result
theorem cast113_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash113.B00.input).map Fin.val=JHc_Gr_M0.Hash113.B00.input := by rfl
#print axioms cast113_0
theorem tail113 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash113.tail).map Fin.val=JHc_Gr_M0.Hash113.tail := by rfl
#print axioms tail113
theorem numeric113 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash113.message).map Fin.val=JHc_Gr_M0.Hash113.message := by
  simp only [JHc_Gr_M0.Hash113.message,JHc_Gr_M0.Hash113.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast113_0,tail113]
#print axioms numeric113
theorem hash113 : JFp_SHADigest.digest input113=value113 := by
  unfold input113 JFp_SHADigest.digest
  rw [numeric113,JHc_Gr_M0.Hash113.checked]
  rfl
#print axioms hash113
theorem address113 : BinMerkle32Path.nodeInput (children value103 (JGc_TX2_HashBytes.state [123,0,162,188,126,191,227,58,109,189,247,38,102,61,157,69,230,4,19,213,18,43,156,113,160,76,253,162,235,123,98,2]))=input113 := by rfl
#print axioms address113
def tree113 : Tree := .branch tree103 (.supplied (JGc_TX2_HashBytes.state [123,0,162,188,126,191,227,58,109,189,247,38,102,61,157,69,230,4,19,213,18,43,156,113,160,76,253,162,235,123,98,2]))
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
def input114 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash114.message
def value114 : State := JFp_SHADigest.output JHc_Gr_M0.Hash114.result
theorem cast114_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash114.B00.input).map Fin.val=JHc_Gr_M0.Hash114.B00.input := by rfl
#print axioms cast114_0
theorem tail114 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash114.tail).map Fin.val=JHc_Gr_M0.Hash114.tail := by rfl
#print axioms tail114
theorem numeric114 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash114.message).map Fin.val=JHc_Gr_M0.Hash114.message := by
  simp only [JHc_Gr_M0.Hash114.message,JHc_Gr_M0.Hash114.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast114_0,tail114]
#print axioms numeric114
theorem hash114 : JFp_SHADigest.digest input114=value114 := by
  unfold input114 JFp_SHADigest.digest
  rw [numeric114,JHc_Gr_M0.Hash114.checked]
  rfl
#print axioms hash114
theorem address114 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [26,34,190,23,233,18,66,255,141,224,173,247,208,54,188,241,221,59,100,97,57,196,21,248,129,34,192,76,118,155,221,240]) value104)=input114 := by rfl
#print axioms address114
def tree114 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [26,34,190,23,233,18,66,255,141,224,173,247,208,54,188,241,221,59,100,97,57,196,21,248,129,34,192,76,118,155,221,240])) tree104
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
def input115 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash115.message
def value115 : State := JFp_SHADigest.output JHc_Gr_M0.Hash115.result
theorem cast115_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash115.B00.input).map Fin.val=JHc_Gr_M0.Hash115.B00.input := by rfl
#print axioms cast115_0
theorem tail115 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash115.tail).map Fin.val=JHc_Gr_M0.Hash115.tail := by rfl
#print axioms tail115
theorem numeric115 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash115.message).map Fin.val=JHc_Gr_M0.Hash115.message := by
  simp only [JHc_Gr_M0.Hash115.message,JHc_Gr_M0.Hash115.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast115_0,tail115]
#print axioms numeric115
theorem hash115 : JFp_SHADigest.digest input115=value115 := by
  unfold input115 JFp_SHADigest.digest
  rw [numeric115,JHc_Gr_M0.Hash115.checked]
  rfl
#print axioms hash115
theorem address115 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [187,161,232,81,61,204,163,255,108,96,207,42,203,160,95,178,216,58,192,25,156,191,241,239,172,147,29,95,154,104,197,242]) value105)=input115 := by rfl
#print axioms address115
def tree115 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [187,161,232,81,61,204,163,255,108,96,207,42,203,160,95,178,216,58,192,25,156,191,241,239,172,147,29,95,154,104,197,242])) tree105
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
def input116 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash116.message
def value116 : State := JFp_SHADigest.output JHc_Gr_M0.Hash116.result
theorem cast116_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash116.B00.input).map Fin.val=JHc_Gr_M0.Hash116.B00.input := by rfl
#print axioms cast116_0
theorem tail116 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash116.tail).map Fin.val=JHc_Gr_M0.Hash116.tail := by rfl
#print axioms tail116
theorem numeric116 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash116.message).map Fin.val=JHc_Gr_M0.Hash116.message := by
  simp only [JHc_Gr_M0.Hash116.message,JHc_Gr_M0.Hash116.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast116_0,tail116]
#print axioms numeric116
theorem hash116 : JFp_SHADigest.digest input116=value116 := by
  unfold input116 JFp_SHADigest.digest
  rw [numeric116,JHc_Gr_M0.Hash116.checked]
  rfl
#print axioms hash116
theorem address116 : BinMerkle32Path.nodeInput (children value106 (JGc_TX2_HashBytes.state [112,136,211,124,72,204,53,180,236,108,229,56,210,88,160,196,172,44,115,159,237,211,216,230,73,10,77,132,61,136,48,224]))=input116 := by rfl
#print axioms address116
def tree116 : Tree := .branch tree106 (.supplied (JGc_TX2_HashBytes.state [112,136,211,124,72,204,53,180,236,108,229,56,210,88,160,196,172,44,115,159,237,211,216,230,73,10,77,132,61,136,48,224]))
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
def input117 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash117.message
def value117 : State := JFp_SHADigest.output JHc_Gr_M0.Hash117.result
theorem cast117_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash117.B00.input).map Fin.val=JHc_Gr_M0.Hash117.B00.input := by rfl
#print axioms cast117_0
theorem tail117 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash117.tail).map Fin.val=JHc_Gr_M0.Hash117.tail := by rfl
#print axioms tail117
theorem numeric117 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash117.message).map Fin.val=JHc_Gr_M0.Hash117.message := by
  simp only [JHc_Gr_M0.Hash117.message,JHc_Gr_M0.Hash117.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast117_0,tail117]
#print axioms numeric117
theorem hash117 : JFp_SHADigest.digest input117=value117 := by
  unfold input117 JFp_SHADigest.digest
  rw [numeric117,JHc_Gr_M0.Hash117.checked]
  rfl
#print axioms hash117
theorem address117 : BinMerkle32Path.nodeInput (children value107 (JGc_TX2_HashBytes.state [68,125,166,81,87,6,116,93,85,44,114,64,254,221,200,45,38,25,196,77,234,200,255,231,247,107,222,180,48,23,31,85]))=input117 := by rfl
#print axioms address117
def tree117 : Tree := .branch tree107 (.supplied (JGc_TX2_HashBytes.state [68,125,166,81,87,6,116,93,85,44,114,64,254,221,200,45,38,25,196,77,234,200,255,231,247,107,222,180,48,23,31,85]))
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
def input118 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash118.message
def value118 : State := JFp_SHADigest.output JHc_Gr_M0.Hash118.result
theorem cast118_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash118.B00.input).map Fin.val=JHc_Gr_M0.Hash118.B00.input := by rfl
#print axioms cast118_0
theorem tail118 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash118.tail).map Fin.val=JHc_Gr_M0.Hash118.tail := by rfl
#print axioms tail118
theorem numeric118 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash118.message).map Fin.val=JHc_Gr_M0.Hash118.message := by
  simp only [JHc_Gr_M0.Hash118.message,JHc_Gr_M0.Hash118.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast118_0,tail118]
#print axioms numeric118
theorem hash118 : JFp_SHADigest.digest input118=value118 := by
  unfold input118 JFp_SHADigest.digest
  rw [numeric118,JHc_Gr_M0.Hash118.checked]
  rfl
#print axioms hash118
theorem address118 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [77,126,21,65,26,159,97,38,195,165,185,168,141,30,194,190,83,101,161,199,214,33,229,162,241,59,159,235,156,208,67,0]) value108)=input118 := by rfl
#print axioms address118
def tree118 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [77,126,21,65,26,159,97,38,195,165,185,168,141,30,194,190,83,101,161,199,214,33,229,162,241,59,159,235,156,208,67,0])) tree108
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
def input119 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash119.message
def value119 : State := JFp_SHADigest.output JHc_Gr_M0.Hash119.result
theorem cast119_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash119.B00.input).map Fin.val=JHc_Gr_M0.Hash119.B00.input := by rfl
#print axioms cast119_0
theorem tail119 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash119.tail).map Fin.val=JHc_Gr_M0.Hash119.tail := by rfl
#print axioms tail119
theorem numeric119 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash119.message).map Fin.val=JHc_Gr_M0.Hash119.message := by
  simp only [JHc_Gr_M0.Hash119.message,JHc_Gr_M0.Hash119.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast119_0,tail119]
#print axioms numeric119
theorem hash119 : JFp_SHADigest.digest input119=value119 := by
  unfold input119 JFp_SHADigest.digest
  rw [numeric119,JHc_Gr_M0.Hash119.checked]
  rfl
#print axioms hash119
theorem address119 : BinMerkle32Path.nodeInput (children value109 (JGc_TX2_HashBytes.state [119,215,118,217,83,7,90,172,138,108,205,252,152,230,120,183,250,105,16,42,20,115,89,179,235,222,70,56,78,50,213,22]))=input119 := by rfl
#print axioms address119
def tree119 : Tree := .branch tree109 (.supplied (JGc_TX2_HashBytes.state [119,215,118,217,83,7,90,172,138,108,205,252,152,230,120,183,250,105,16,42,20,115,89,179,235,222,70,56,78,50,213,22]))
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
end AspisR1.JHc_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input120 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash120.message
def value120 : State := JFp_SHADigest.output JHc_Gr_M0.Hash120.result
theorem cast120_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash120.B00.input).map Fin.val=JHc_Gr_M0.Hash120.B00.input := by rfl
#print axioms cast120_0
theorem tail120 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash120.tail).map Fin.val=JHc_Gr_M0.Hash120.tail := by rfl
#print axioms tail120
theorem numeric120 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash120.message).map Fin.val=JHc_Gr_M0.Hash120.message := by
  simp only [JHc_Gr_M0.Hash120.message,JHc_Gr_M0.Hash120.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast120_0,tail120]
#print axioms numeric120
theorem hash120 : JFp_SHADigest.digest input120=value120 := by
  unfold input120 JFp_SHADigest.digest
  rw [numeric120,JHc_Gr_M0.Hash120.checked]
  rfl
#print axioms hash120
theorem address120 : BinMerkle32Path.nodeInput (children value110 (JGc_TX2_HashBytes.state [164,65,78,40,106,51,231,38,125,149,75,249,27,93,238,7,155,254,36,78,118,136,30,42,179,250,247,120,7,81,21,144]))=input120 := by rfl
#print axioms address120
def tree120 : Tree := .branch tree110 (.supplied (JGc_TX2_HashBytes.state [164,65,78,40,106,51,231,38,125,149,75,249,27,93,238,7,155,254,36,78,118,136,30,42,179,250,247,120,7,81,21,144]))
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
def input121 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash121.message
def value121 : State := JFp_SHADigest.output JHc_Gr_M0.Hash121.result
theorem cast121_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash121.B00.input).map Fin.val=JHc_Gr_M0.Hash121.B00.input := by rfl
#print axioms cast121_0
theorem tail121 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash121.tail).map Fin.val=JHc_Gr_M0.Hash121.tail := by rfl
#print axioms tail121
theorem numeric121 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash121.message).map Fin.val=JHc_Gr_M0.Hash121.message := by
  simp only [JHc_Gr_M0.Hash121.message,JHc_Gr_M0.Hash121.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast121_0,tail121]
#print axioms numeric121
theorem hash121 : JFp_SHADigest.digest input121=value121 := by
  unfold input121 JFp_SHADigest.digest
  rw [numeric121,JHc_Gr_M0.Hash121.checked]
  rfl
#print axioms hash121
theorem address121 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [211,245,58,70,112,158,59,164,73,134,77,204,94,119,107,22,183,105,32,45,41,61,170,17,107,25,88,255,149,122,164,95]) value111)=input121 := by rfl
#print axioms address121
def tree121 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [211,245,58,70,112,158,59,164,73,134,77,204,94,119,107,22,183,105,32,45,41,61,170,17,107,25,88,255,149,122,164,95])) tree111
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
def input122 : Bytes := JGf_TX2_M0Roots.input150
def value122 : State := JGf_TX2_M0Roots.value150
theorem hash122 : JFp_SHADigest.digest input122=value122 := JGf_TX2_M0Roots.hash150
#print axioms hash122
theorem address122 : BinMerkle32Path.nodeInput (children value112 (JGc_TX2_HashBytes.state [202,64,14,6,35,96,78,97,222,124,133,255,162,222,235,186,63,243,32,144,64,134,253,43,104,226,220,66,124,185,92,7]))=input122 := by rfl
#print axioms address122
def tree122 : Tree := .branch tree112 (.supplied (JGc_TX2_HashBytes.state [202,64,14,6,35,96,78,97,222,124,133,255,162,222,235,186,63,243,32,144,64,134,253,43,104,226,220,66,124,185,92,7]))
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
def input123 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash123.message
def value123 : State := JFp_SHADigest.output JHc_Gr_M0.Hash123.result
theorem cast123_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash123.B00.input).map Fin.val=JHc_Gr_M0.Hash123.B00.input := by rfl
#print axioms cast123_0
theorem tail123 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash123.tail).map Fin.val=JHc_Gr_M0.Hash123.tail := by rfl
#print axioms tail123
theorem numeric123 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash123.message).map Fin.val=JHc_Gr_M0.Hash123.message := by
  simp only [JHc_Gr_M0.Hash123.message,JHc_Gr_M0.Hash123.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast123_0,tail123]
#print axioms numeric123
theorem hash123 : JFp_SHADigest.digest input123=value123 := by
  unfold input123 JFp_SHADigest.digest
  rw [numeric123,JHc_Gr_M0.Hash123.checked]
  rfl
#print axioms hash123
theorem address123 : BinMerkle32Path.nodeInput (children value113 (JGc_TX2_HashBytes.state [247,131,116,212,93,146,215,2,194,179,95,254,35,17,63,19,206,90,55,80,187,155,124,170,167,224,151,27,162,66,130,234]))=input123 := by rfl
#print axioms address123
def tree123 : Tree := .branch tree113 (.supplied (JGc_TX2_HashBytes.state [247,131,116,212,93,146,215,2,194,179,95,254,35,17,63,19,206,90,55,80,187,155,124,170,167,224,151,27,162,66,130,234]))
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
def input124 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash124.message
def value124 : State := JFp_SHADigest.output JHc_Gr_M0.Hash124.result
theorem cast124_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash124.B00.input).map Fin.val=JHc_Gr_M0.Hash124.B00.input := by rfl
#print axioms cast124_0
theorem tail124 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash124.tail).map Fin.val=JHc_Gr_M0.Hash124.tail := by rfl
#print axioms tail124
theorem numeric124 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash124.message).map Fin.val=JHc_Gr_M0.Hash124.message := by
  simp only [JHc_Gr_M0.Hash124.message,JHc_Gr_M0.Hash124.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast124_0,tail124]
#print axioms numeric124
theorem hash124 : JFp_SHADigest.digest input124=value124 := by
  unfold input124 JFp_SHADigest.digest
  rw [numeric124,JHc_Gr_M0.Hash124.checked]
  rfl
#print axioms hash124
theorem address124 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [210,253,93,83,135,24,182,107,129,24,45,138,60,15,178,254,10,77,18,68,97,47,12,113,104,75,135,148,129,15,201,143]) value114)=input124 := by rfl
#print axioms address124
def tree124 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [210,253,93,83,135,24,182,107,129,24,45,138,60,15,178,254,10,77,18,68,97,47,12,113,104,75,135,148,129,15,201,143])) tree114
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
def input125 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash125.message
def value125 : State := JFp_SHADigest.output JHc_Gr_M0.Hash125.result
theorem cast125_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash125.B00.input).map Fin.val=JHc_Gr_M0.Hash125.B00.input := by rfl
#print axioms cast125_0
theorem tail125 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash125.tail).map Fin.val=JHc_Gr_M0.Hash125.tail := by rfl
#print axioms tail125
theorem numeric125 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash125.message).map Fin.val=JHc_Gr_M0.Hash125.message := by
  simp only [JHc_Gr_M0.Hash125.message,JHc_Gr_M0.Hash125.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast125_0,tail125]
#print axioms numeric125
theorem hash125 : JFp_SHADigest.digest input125=value125 := by
  unfold input125 JFp_SHADigest.digest
  rw [numeric125,JHc_Gr_M0.Hash125.checked]
  rfl
#print axioms hash125
theorem address125 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [108,30,109,110,34,215,172,38,88,37,207,120,123,70,8,40,222,202,101,229,33,117,10,142,69,118,38,35,142,15,136,99]) value115)=input125 := by rfl
#print axioms address125
def tree125 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [108,30,109,110,34,215,172,38,88,37,207,120,123,70,8,40,222,202,101,229,33,117,10,142,69,118,38,35,142,15,136,99])) tree115
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
def input126 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash126.message
def value126 : State := JFp_SHADigest.output JHc_Gr_M0.Hash126.result
theorem cast126_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash126.B00.input).map Fin.val=JHc_Gr_M0.Hash126.B00.input := by rfl
#print axioms cast126_0
theorem tail126 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash126.tail).map Fin.val=JHc_Gr_M0.Hash126.tail := by rfl
#print axioms tail126
theorem numeric126 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash126.message).map Fin.val=JHc_Gr_M0.Hash126.message := by
  simp only [JHc_Gr_M0.Hash126.message,JHc_Gr_M0.Hash126.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast126_0,tail126]
#print axioms numeric126
theorem hash126 : JFp_SHADigest.digest input126=value126 := by
  unfold input126 JFp_SHADigest.digest
  rw [numeric126,JHc_Gr_M0.Hash126.checked]
  rfl
#print axioms hash126
theorem address126 : BinMerkle32Path.nodeInput (children value116 (JGc_TX2_HashBytes.state [163,133,73,137,234,254,224,77,43,180,89,181,80,182,68,145,168,49,120,172,255,240,170,6,191,185,169,251,210,212,116,243]))=input126 := by rfl
#print axioms address126
def tree126 : Tree := .branch tree116 (.supplied (JGc_TX2_HashBytes.state [163,133,73,137,234,254,224,77,43,180,89,181,80,182,68,145,168,49,120,172,255,240,170,6,191,185,169,251,210,212,116,243]))
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
def input127 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash127.message
def value127 : State := JFp_SHADigest.output JHc_Gr_M0.Hash127.result
theorem cast127_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash127.B00.input).map Fin.val=JHc_Gr_M0.Hash127.B00.input := by rfl
#print axioms cast127_0
theorem tail127 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash127.tail).map Fin.val=JHc_Gr_M0.Hash127.tail := by rfl
#print axioms tail127
theorem numeric127 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash127.message).map Fin.val=JHc_Gr_M0.Hash127.message := by
  simp only [JHc_Gr_M0.Hash127.message,JHc_Gr_M0.Hash127.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast127_0,tail127]
#print axioms numeric127
theorem hash127 : JFp_SHADigest.digest input127=value127 := by
  unfold input127 JFp_SHADigest.digest
  rw [numeric127,JHc_Gr_M0.Hash127.checked]
  rfl
#print axioms hash127
theorem address127 : BinMerkle32Path.nodeInput (children value117 (JGc_TX2_HashBytes.state [129,75,194,226,75,93,208,230,67,98,126,175,55,174,113,122,34,52,245,123,168,194,155,56,57,111,31,104,119,113,135,71]))=input127 := by rfl
#print axioms address127
def tree127 : Tree := .branch tree117 (.supplied (JGc_TX2_HashBytes.state [129,75,194,226,75,93,208,230,67,98,126,175,55,174,113,122,34,52,245,123,168,194,155,56,57,111,31,104,119,113,135,71]))
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
def input128 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash128.message
def value128 : State := JFp_SHADigest.output JHc_Gr_M0.Hash128.result
theorem cast128_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash128.B00.input).map Fin.val=JHc_Gr_M0.Hash128.B00.input := by rfl
#print axioms cast128_0
theorem tail128 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash128.tail).map Fin.val=JHc_Gr_M0.Hash128.tail := by rfl
#print axioms tail128
theorem numeric128 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash128.message).map Fin.val=JHc_Gr_M0.Hash128.message := by
  simp only [JHc_Gr_M0.Hash128.message,JHc_Gr_M0.Hash128.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast128_0,tail128]
#print axioms numeric128
theorem hash128 : JFp_SHADigest.digest input128=value128 := by
  unfold input128 JFp_SHADigest.digest
  rw [numeric128,JHc_Gr_M0.Hash128.checked]
  rfl
#print axioms hash128
theorem address128 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [56,117,174,192,243,180,43,166,2,52,80,21,16,203,229,105,85,214,216,157,123,230,248,209,219,21,217,60,60,150,184,141]) value118)=input128 := by rfl
#print axioms address128
def tree128 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [56,117,174,192,243,180,43,166,2,52,80,21,16,203,229,105,85,214,216,157,123,230,248,209,219,21,217,60,60,150,184,141])) tree118
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
def input129 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash129.message
def value129 : State := JFp_SHADigest.output JHc_Gr_M0.Hash129.result
theorem cast129_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash129.B00.input).map Fin.val=JHc_Gr_M0.Hash129.B00.input := by rfl
#print axioms cast129_0
theorem tail129 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash129.tail).map Fin.val=JHc_Gr_M0.Hash129.tail := by rfl
#print axioms tail129
theorem numeric129 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash129.message).map Fin.val=JHc_Gr_M0.Hash129.message := by
  simp only [JHc_Gr_M0.Hash129.message,JHc_Gr_M0.Hash129.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast129_0,tail129]
#print axioms numeric129
theorem hash129 : JFp_SHADigest.digest input129=value129 := by
  unfold input129 JFp_SHADigest.digest
  rw [numeric129,JHc_Gr_M0.Hash129.checked]
  rfl
#print axioms hash129
theorem address129 : BinMerkle32Path.nodeInput (children value119 (JGc_TX2_HashBytes.state [109,231,155,150,47,42,48,122,18,218,72,65,211,238,180,205,145,47,143,73,158,94,97,67,253,155,2,166,178,50,203,27]))=input129 := by rfl
#print axioms address129
def tree129 : Tree := .branch tree119 (.supplied (JGc_TX2_HashBytes.state [109,231,155,150,47,42,48,122,18,218,72,65,211,238,180,205,145,47,143,73,158,94,97,67,253,155,2,166,178,50,203,27]))
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
end AspisR1.JHc_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input130 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash130.message
def value130 : State := JFp_SHADigest.output JHc_Gr_M0.Hash130.result
theorem cast130_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash130.B00.input).map Fin.val=JHc_Gr_M0.Hash130.B00.input := by rfl
#print axioms cast130_0
theorem tail130 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash130.tail).map Fin.val=JHc_Gr_M0.Hash130.tail := by rfl
#print axioms tail130
theorem numeric130 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash130.message).map Fin.val=JHc_Gr_M0.Hash130.message := by
  simp only [JHc_Gr_M0.Hash130.message,JHc_Gr_M0.Hash130.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast130_0,tail130]
#print axioms numeric130
theorem hash130 : JFp_SHADigest.digest input130=value130 := by
  unfold input130 JFp_SHADigest.digest
  rw [numeric130,JHc_Gr_M0.Hash130.checked]
  rfl
#print axioms hash130
theorem address130 : BinMerkle32Path.nodeInput (children value120 (JGc_TX2_HashBytes.state [254,14,130,135,247,205,115,79,107,166,89,198,117,201,141,89,5,159,55,163,8,155,248,77,113,14,97,138,39,216,58,208]))=input130 := by rfl
#print axioms address130
def tree130 : Tree := .branch tree120 (.supplied (JGc_TX2_HashBytes.state [254,14,130,135,247,205,115,79,107,166,89,198,117,201,141,89,5,159,55,163,8,155,248,77,113,14,97,138,39,216,58,208]))
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
def input131 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash131.message
def value131 : State := JFp_SHADigest.output JHc_Gr_M0.Hash131.result
theorem cast131_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash131.B00.input).map Fin.val=JHc_Gr_M0.Hash131.B00.input := by rfl
#print axioms cast131_0
theorem tail131 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash131.tail).map Fin.val=JHc_Gr_M0.Hash131.tail := by rfl
#print axioms tail131
theorem numeric131 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash131.message).map Fin.val=JHc_Gr_M0.Hash131.message := by
  simp only [JHc_Gr_M0.Hash131.message,JHc_Gr_M0.Hash131.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast131_0,tail131]
#print axioms numeric131
theorem hash131 : JFp_SHADigest.digest input131=value131 := by
  unfold input131 JFp_SHADigest.digest
  rw [numeric131,JHc_Gr_M0.Hash131.checked]
  rfl
#print axioms hash131
theorem address131 : BinMerkle32Path.nodeInput (children value121 (JGc_TX2_HashBytes.state [66,225,29,27,146,87,4,138,36,32,56,196,112,123,143,15,189,101,254,171,108,124,109,6,10,176,21,23,227,251,248,124]))=input131 := by rfl
#print axioms address131
def tree131 : Tree := .branch tree121 (.supplied (JGc_TX2_HashBytes.state [66,225,29,27,146,87,4,138,36,32,56,196,112,123,143,15,189,101,254,171,108,124,109,6,10,176,21,23,227,251,248,124]))
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
def input132 : Bytes := JGf_TX2_M0Roots.input161
def value132 : State := JGf_TX2_M0Roots.value161
theorem hash132 : JFp_SHADigest.digest input132=value132 := JGf_TX2_M0Roots.hash161
#print axioms hash132
theorem address132 : BinMerkle32Path.nodeInput (children value122 (JGc_TX2_HashBytes.state [211,48,75,83,168,253,130,42,18,106,192,164,216,10,63,11,154,197,231,229,193,137,184,83,8,108,208,85,178,162,241,238]))=input132 := by rfl
#print axioms address132
def tree132 : Tree := .branch tree122 (.supplied (JGc_TX2_HashBytes.state [211,48,75,83,168,253,130,42,18,106,192,164,216,10,63,11,154,197,231,229,193,137,184,83,8,108,208,85,178,162,241,238]))
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
def input133 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash133.message
def value133 : State := JFp_SHADigest.output JHc_Gr_M0.Hash133.result
theorem cast133_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash133.B00.input).map Fin.val=JHc_Gr_M0.Hash133.B00.input := by rfl
#print axioms cast133_0
theorem tail133 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash133.tail).map Fin.val=JHc_Gr_M0.Hash133.tail := by rfl
#print axioms tail133
theorem numeric133 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash133.message).map Fin.val=JHc_Gr_M0.Hash133.message := by
  simp only [JHc_Gr_M0.Hash133.message,JHc_Gr_M0.Hash133.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast133_0,tail133]
#print axioms numeric133
theorem hash133 : JFp_SHADigest.digest input133=value133 := by
  unfold input133 JFp_SHADigest.digest
  rw [numeric133,JHc_Gr_M0.Hash133.checked]
  rfl
#print axioms hash133
theorem address133 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [188,195,79,74,213,254,47,21,205,195,209,166,40,141,13,9,97,84,152,93,102,191,158,16,165,158,96,183,21,248,100,55]) value123)=input133 := by rfl
#print axioms address133
def tree133 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [188,195,79,74,213,254,47,21,205,195,209,166,40,141,13,9,97,84,152,93,102,191,158,16,165,158,96,183,21,248,100,55])) tree123
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
def input134 : Bytes := JGf_TX2_M0Roots.input164
def value134 : State := JGf_TX2_M0Roots.value164
theorem hash134 : JFp_SHADigest.digest input134=value134 := JGf_TX2_M0Roots.hash164
#print axioms hash134
theorem address134 : BinMerkle32Path.nodeInput (children value124 (JGc_TX2_HashBytes.state [187,76,51,74,59,158,50,38,87,85,221,77,230,156,105,93,240,119,203,74,247,195,29,178,103,62,94,105,26,121,227,113]))=input134 := by rfl
#print axioms address134
def tree134 : Tree := .branch tree124 (.supplied (JGc_TX2_HashBytes.state [187,76,51,74,59,158,50,38,87,85,221,77,230,156,105,93,240,119,203,74,247,195,29,178,103,62,94,105,26,121,227,113]))
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
def input135 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash135.message
def value135 : State := JFp_SHADigest.output JHc_Gr_M0.Hash135.result
theorem cast135_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash135.B00.input).map Fin.val=JHc_Gr_M0.Hash135.B00.input := by rfl
#print axioms cast135_0
theorem tail135 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash135.tail).map Fin.val=JHc_Gr_M0.Hash135.tail := by rfl
#print axioms tail135
theorem numeric135 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash135.message).map Fin.val=JHc_Gr_M0.Hash135.message := by
  simp only [JHc_Gr_M0.Hash135.message,JHc_Gr_M0.Hash135.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast135_0,tail135]
#print axioms numeric135
theorem hash135 : JFp_SHADigest.digest input135=value135 := by
  unfold input135 JFp_SHADigest.digest
  rw [numeric135,JHc_Gr_M0.Hash135.checked]
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
def input136 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash136.message
def value136 : State := JFp_SHADigest.output JHc_Gr_M0.Hash136.result
theorem cast136_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash136.B00.input).map Fin.val=JHc_Gr_M0.Hash136.B00.input := by rfl
#print axioms cast136_0
theorem tail136 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash136.tail).map Fin.val=JHc_Gr_M0.Hash136.tail := by rfl
#print axioms tail136
theorem numeric136 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash136.message).map Fin.val=JHc_Gr_M0.Hash136.message := by
  simp only [JHc_Gr_M0.Hash136.message,JHc_Gr_M0.Hash136.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast136_0,tail136]
#print axioms numeric136
theorem hash136 : JFp_SHADigest.digest input136=value136 := by
  unfold input136 JFp_SHADigest.digest
  rw [numeric136,JHc_Gr_M0.Hash136.checked]
  rfl
#print axioms hash136
theorem address136 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [73,20,30,234,180,192,147,217,52,97,111,104,183,231,180,130,207,5,13,223,218,43,82,64,97,51,35,212,32,222,55,133]) value127)=input136 := by rfl
#print axioms address136
def tree136 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [73,20,30,234,180,192,147,217,52,97,111,104,183,231,180,130,207,5,13,223,218,43,82,64,97,51,35,212,32,222,55,133])) tree127
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
def input137 : Bytes := JGf_TX2_M0Roots.input165
def value137 : State := JGf_TX2_M0Roots.value165
theorem hash137 : JFp_SHADigest.digest input137=value137 := JGf_TX2_M0Roots.hash165
#print axioms hash137
theorem address137 : BinMerkle32Path.nodeInput (children value128 (JGc_TX2_HashBytes.state [216,39,125,52,179,150,49,41,23,46,71,20,106,158,77,0,176,105,197,0,58,234,126,198,61,27,243,66,155,192,133,151]))=input137 := by rfl
#print axioms address137
def tree137 : Tree := .branch tree128 (.supplied (JGc_TX2_HashBytes.state [216,39,125,52,179,150,49,41,23,46,71,20,106,158,77,0,176,105,197,0,58,234,126,198,61,27,243,66,155,192,133,151]))
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
def input138 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash138.message
def value138 : State := JFp_SHADigest.output JHc_Gr_M0.Hash138.result
theorem cast138_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash138.B00.input).map Fin.val=JHc_Gr_M0.Hash138.B00.input := by rfl
#print axioms cast138_0
theorem tail138 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash138.tail).map Fin.val=JHc_Gr_M0.Hash138.tail := by rfl
#print axioms tail138
theorem numeric138 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash138.message).map Fin.val=JHc_Gr_M0.Hash138.message := by
  simp only [JHc_Gr_M0.Hash138.message,JHc_Gr_M0.Hash138.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast138_0,tail138]
#print axioms numeric138
theorem hash138 : JFp_SHADigest.digest input138=value138 := by
  unfold input138 JFp_SHADigest.digest
  rw [numeric138,JHc_Gr_M0.Hash138.checked]
  rfl
#print axioms hash138
theorem address138 : BinMerkle32Path.nodeInput (children value129 (JGc_TX2_HashBytes.state [24,83,241,162,249,154,230,253,165,145,84,5,188,201,216,39,216,112,35,240,228,235,23,16,186,131,61,83,162,137,67,145]))=input138 := by rfl
#print axioms address138
def tree138 : Tree := .branch tree129 (.supplied (JGc_TX2_HashBytes.state [24,83,241,162,249,154,230,253,165,145,84,5,188,201,216,39,216,112,35,240,228,235,23,16,186,131,61,83,162,137,67,145]))
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
end AspisR1.JHc_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input139 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash139.message
def value139 : State := JFp_SHADigest.output JHc_Gr_M0.Hash139.result
theorem cast139_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash139.B00.input).map Fin.val=JHc_Gr_M0.Hash139.B00.input := by rfl
#print axioms cast139_0
theorem tail139 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash139.tail).map Fin.val=JHc_Gr_M0.Hash139.tail := by rfl
#print axioms tail139
theorem numeric139 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash139.message).map Fin.val=JHc_Gr_M0.Hash139.message := by
  simp only [JHc_Gr_M0.Hash139.message,JHc_Gr_M0.Hash139.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast139_0,tail139]
#print axioms numeric139
theorem hash139 : JFp_SHADigest.digest input139=value139 := by
  unfold input139 JFp_SHADigest.digest
  rw [numeric139,JHc_Gr_M0.Hash139.checked]
  rfl
#print axioms hash139
theorem address139 : BinMerkle32Path.nodeInput (children value130 (JGc_TX2_HashBytes.state [223,231,93,243,187,222,217,220,41,38,7,106,101,167,239,80,245,56,246,60,210,149,142,25,64,43,210,121,95,194,190,127]))=input139 := by rfl
#print axioms address139
def tree139 : Tree := .branch tree130 (.supplied (JGc_TX2_HashBytes.state [223,231,93,243,187,222,217,220,41,38,7,106,101,167,239,80,245,56,246,60,210,149,142,25,64,43,210,121,95,194,190,127]))
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
def input140 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash140.message
def value140 : State := JFp_SHADigest.output JHc_Gr_M0.Hash140.result
theorem cast140_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash140.B00.input).map Fin.val=JHc_Gr_M0.Hash140.B00.input := by rfl
#print axioms cast140_0
theorem tail140 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash140.tail).map Fin.val=JHc_Gr_M0.Hash140.tail := by rfl
#print axioms tail140
theorem numeric140 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash140.message).map Fin.val=JHc_Gr_M0.Hash140.message := by
  simp only [JHc_Gr_M0.Hash140.message,JHc_Gr_M0.Hash140.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast140_0,tail140]
#print axioms numeric140
theorem hash140 : JFp_SHADigest.digest input140=value140 := by
  unfold input140 JFp_SHADigest.digest
  rw [numeric140,JHc_Gr_M0.Hash140.checked]
  rfl
#print axioms hash140
theorem address140 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [229,54,3,47,115,163,190,8,7,45,5,100,244,76,80,249,22,225,43,200,84,178,81,224,91,144,25,21,23,167,131,241]) value131)=input140 := by rfl
#print axioms address140
def tree140 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [229,54,3,47,115,163,190,8,7,45,5,100,244,76,80,249,22,225,43,200,84,178,81,224,91,144,25,21,23,167,131,241])) tree131
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
def input141 : Bytes := JGf_TX2_M0Roots.input171
def value141 : State := JGf_TX2_M0Roots.value171
theorem hash141 : JFp_SHADigest.digest input141=value141 := JGf_TX2_M0Roots.hash171
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
def input142 : Bytes := JGf_TX2_M0Roots.input173
def value142 : State := JGf_TX2_M0Roots.value173
theorem hash142 : JFp_SHADigest.digest input142=value142 := JGf_TX2_M0Roots.hash173
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
def input143 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash143.message
def value143 : State := JFp_SHADigest.output JHc_Gr_M0.Hash143.result
theorem cast143_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash143.B00.input).map Fin.val=JHc_Gr_M0.Hash143.B00.input := by rfl
#print axioms cast143_0
theorem tail143 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash143.tail).map Fin.val=JHc_Gr_M0.Hash143.tail := by rfl
#print axioms tail143
theorem numeric143 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash143.message).map Fin.val=JHc_Gr_M0.Hash143.message := by
  simp only [JHc_Gr_M0.Hash143.message,JHc_Gr_M0.Hash143.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast143_0,tail143]
#print axioms numeric143
theorem hash143 : JFp_SHADigest.digest input143=value143 := by
  unfold input143 JFp_SHADigest.digest
  rw [numeric143,JHc_Gr_M0.Hash143.checked]
  rfl
#print axioms hash143
theorem address143 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [213,15,157,39,47,184,77,71,127,84,62,42,216,50,94,250,30,227,120,165,40,142,232,125,140,191,184,70,132,206,159,228]) value136)=input143 := by rfl
#print axioms address143
def tree143 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [213,15,157,39,47,184,77,71,127,84,62,42,216,50,94,250,30,227,120,165,40,142,232,125,140,191,184,70,132,206,159,228])) tree136
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
def input144 : Bytes := JGf_TX2_M0Roots.input174
def value144 : State := JGf_TX2_M0Roots.value174
theorem hash144 : JFp_SHADigest.digest input144=value144 := JGf_TX2_M0Roots.hash174
#print axioms hash144
theorem address144 : BinMerkle32Path.nodeInput (children value137 (JGc_TX2_HashBytes.state [144,204,223,168,76,216,166,74,227,194,185,212,243,3,52,220,59,216,34,129,248,243,249,25,126,67,141,62,64,65,71,59]))=input144 := by rfl
#print axioms address144
def tree144 : Tree := .branch tree137 (.supplied (JGc_TX2_HashBytes.state [144,204,223,168,76,216,166,74,227,194,185,212,243,3,52,220,59,216,34,129,248,243,249,25,126,67,141,62,64,65,71,59]))
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
def input145 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash145.message
def value145 : State := JFp_SHADigest.output JHc_Gr_M0.Hash145.result
theorem cast145_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash145.B00.input).map Fin.val=JHc_Gr_M0.Hash145.B00.input := by rfl
#print axioms cast145_0
theorem tail145 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash145.tail).map Fin.val=JHc_Gr_M0.Hash145.tail := by rfl
#print axioms tail145
theorem numeric145 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash145.message).map Fin.val=JHc_Gr_M0.Hash145.message := by
  simp only [JHc_Gr_M0.Hash145.message,JHc_Gr_M0.Hash145.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast145_0,tail145]
#print axioms numeric145
theorem hash145 : JFp_SHADigest.digest input145=value145 := by
  unfold input145 JFp_SHADigest.digest
  rw [numeric145,JHc_Gr_M0.Hash145.checked]
  rfl
#print axioms hash145
theorem address145 : BinMerkle32Path.nodeInput (children value138 (JGc_TX2_HashBytes.state [78,208,3,215,108,77,215,153,252,92,186,74,30,93,232,95,87,47,70,138,104,13,138,115,161,80,31,90,248,143,34,113]))=input145 := by rfl
#print axioms address145
def tree145 : Tree := .branch tree138 (.supplied (JGc_TX2_HashBytes.state [78,208,3,215,108,77,215,153,252,92,186,74,30,93,232,95,87,47,70,138,104,13,138,115,161,80,31,90,248,143,34,113]))
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
end AspisR1.JHc_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input146 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash146.message
def value146 : State := JFp_SHADigest.output JHc_Gr_M0.Hash146.result
theorem cast146_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash146.B00.input).map Fin.val=JHc_Gr_M0.Hash146.B00.input := by rfl
#print axioms cast146_0
theorem tail146 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash146.tail).map Fin.val=JHc_Gr_M0.Hash146.tail := by rfl
#print axioms tail146
theorem numeric146 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash146.message).map Fin.val=JHc_Gr_M0.Hash146.message := by
  simp only [JHc_Gr_M0.Hash146.message,JHc_Gr_M0.Hash146.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast146_0,tail146]
#print axioms numeric146
theorem hash146 : JFp_SHADigest.digest input146=value146 := by
  unfold input146 JFp_SHADigest.digest
  rw [numeric146,JHc_Gr_M0.Hash146.checked]
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
def input147 : Bytes := JGf_TX2_M0Roots.input177
def value147 : State := JGf_TX2_M0Roots.value177
theorem hash147 : JFp_SHADigest.digest input147=value147 := JGf_TX2_M0Roots.hash177
#print axioms hash147
theorem address147 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [76,205,219,41,141,231,162,252,144,59,33,119,50,181,0,227,188,209,249,74,188,31,19,122,76,172,71,94,11,48,185,91]) value141)=input147 := by rfl
#print axioms address147
def tree147 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [76,205,219,41,141,231,162,252,144,59,33,119,50,181,0,227,188,209,249,74,188,31,19,122,76,172,71,94,11,48,185,91])) tree141
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
def input148 : Bytes := JGf_TX2_M0Roots.input178
def value148 : State := JGf_TX2_M0Roots.value178
theorem hash148 : JFp_SHADigest.digest input148=value148 := JGf_TX2_M0Roots.hash178
#print axioms hash148
theorem address148 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [195,209,74,206,189,24,33,14,245,28,250,102,99,222,20,28,120,118,240,28,23,39,12,127,80,80,115,112,100,54,252,25]) value142)=input148 := by rfl
#print axioms address148
def tree148 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [195,209,74,206,189,24,33,14,245,28,250,102,99,222,20,28,120,118,240,28,23,39,12,127,80,80,115,112,100,54,252,25])) tree142
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
def input149 : Bytes := JGf_TX2_M0Roots.input179
def value149 : State := JGf_TX2_M0Roots.value179
theorem hash149 : JFp_SHADigest.digest input149=value149 := JGf_TX2_M0Roots.hash179
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
def input150 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash150.message
def value150 : State := JFp_SHADigest.output JHc_Gr_M0.Hash150.result
theorem cast150_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash150.B00.input).map Fin.val=JHc_Gr_M0.Hash150.B00.input := by rfl
#print axioms cast150_0
theorem tail150 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash150.tail).map Fin.val=JHc_Gr_M0.Hash150.tail := by rfl
#print axioms tail150
theorem numeric150 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash150.message).map Fin.val=JHc_Gr_M0.Hash150.message := by
  simp only [JHc_Gr_M0.Hash150.message,JHc_Gr_M0.Hash150.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast150_0,tail150]
#print axioms numeric150
theorem hash150 : JFp_SHADigest.digest input150=value150 := by
  unfold input150 JFp_SHADigest.digest
  rw [numeric150,JHc_Gr_M0.Hash150.checked]
  rfl
#print axioms hash150
theorem address150 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [118,94,98,240,13,109,219,74,220,141,201,122,136,79,63,121,122,39,87,235,183,208,228,91,25,215,28,91,198,59,225,224]) value145)=input150 := by rfl
#print axioms address150
def tree150 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [118,94,98,240,13,109,219,74,220,141,201,122,136,79,63,121,122,39,87,235,183,208,228,91,25,215,28,91,198,59,225,224])) tree145
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
end AspisR1.JHc_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input151 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash151.message
def value151 : State := JFp_SHADigest.output JHc_Gr_M0.Hash151.result
theorem cast151_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash151.B00.input).map Fin.val=JHc_Gr_M0.Hash151.B00.input := by rfl
#print axioms cast151_0
theorem tail151 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash151.tail).map Fin.val=JHc_Gr_M0.Hash151.tail := by rfl
#print axioms tail151
theorem numeric151 : (JGc_TX2_HashBytes.bytes JHc_Gr_M0.Hash151.message).map Fin.val=JHc_Gr_M0.Hash151.message := by
  simp only [JHc_Gr_M0.Hash151.message,JHc_Gr_M0.Hash151.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast151_0,tail151]
#print axioms numeric151
theorem hash151 : JFp_SHADigest.digest input151=value151 := by
  unfold input151 JFp_SHADigest.digest
  rw [numeric151,JHc_Gr_M0.Hash151.checked]
  rfl
#print axioms hash151
theorem address151 : BinMerkle32Path.nodeInput (children value146 (JGc_TX2_HashBytes.state [252,122,11,56,39,253,242,99,6,187,217,125,119,182,47,156,200,119,4,163,152,112,165,102,7,195,55,25,110,238,3,173]))=input151 := by rfl
#print axioms address151
def tree151 : Tree := .branch tree146 (.supplied (JGc_TX2_HashBytes.state [252,122,11,56,39,253,242,99,6,187,217,125,119,182,47,156,200,119,4,163,152,112,165,102,7,195,55,25,110,238,3,173]))
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
def input152 : Bytes := JGf_TX2_M0Roots.input181
def value152 : State := JGf_TX2_M0Roots.value181
theorem hash152 : JFp_SHADigest.digest input152=value152 := JGf_TX2_M0Roots.hash181
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
def input153 : Bytes := JGf_TX2_M0Roots.input182
def value153 : State := JGf_TX2_M0Roots.value182
theorem hash153 : JFp_SHADigest.digest input153=value153 := JGf_TX2_M0Roots.hash182
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
end AspisR1.JHc_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input154 : Bytes := JGf_TX2_M0Roots.input183
def value154 : State := JGf_TX2_M0Roots.value183
theorem hash154 : JFp_SHADigest.digest input154=value154 := JGf_TX2_M0Roots.hash183
#print axioms hash154
theorem address154 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [186,70,164,226,215,82,40,99,140,117,51,93,72,25,161,89,123,6,162,192,130,252,253,134,91,166,4,240,224,19,155,103]) value151)=input154 := by rfl
#print axioms address154
def tree154 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [186,70,164,226,215,82,40,99,140,117,51,93,72,25,161,89,123,6,162,192,130,252,253,134,91,166,4,240,224,19,155,103])) tree151
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
def input155 : Bytes := JGf_TX2_M0Roots.input184
def value155 : State := JGf_TX2_M0Roots.value184
theorem hash155 : JFp_SHADigest.digest input155=value155 := JGf_TX2_M0Roots.hash184
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
end AspisR1.JHc_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input156 : Bytes := JGf_TX2_M0Roots.input185
def value156 : State := JGf_TX2_M0Roots.value185
theorem hash156 : JFp_SHADigest.digest input156=value156 := JGf_TX2_M0Roots.hash185
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
end AspisR1.JHc_Gr_M0Roots
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M0Root
open Aeneas Aeneas.Std
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiBuild OracleDecisionMultiTree JHc_Gr_M0Roots

def retainedRoot : State := JGf_TX2_M0Root.retainedRoot

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
    (Port4B_KeyInstall.queries JFo_Prepared.value.queries) 0 0=indices := rfl
#print axioms selected_queries

theorem inhabited : ∃ (f : Nat → Bytes) (g : Nat → Nat → State),
    InputLaw f ∧ SiblingLaw g ∧
    root JFp_SHADigest.digest (build indices f g 18 0)=retainedRoot :=
  ⟨inputAt,siblingAt,(by intro b _;rfl),(by intro h _ b _;rfl),
    source inputAt siblingAt (by intro b _;rfl) (by intro h _ b _;rfl)⟩
#print axioms inhabited
end AspisR1.JHc_Gr_M0Root
end
