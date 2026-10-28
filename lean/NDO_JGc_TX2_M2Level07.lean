import NDO_JGc_TX2_M2Level06
import NDO_JGc_TX2_M2H096
import NDO_JGc_TX2_M2H100
import NDO_JGc_TX2_M2H104
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input096 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash096.message
def value096 : State := JFp_SHADigest.output JGc_TX2_M2.Hash096.result
theorem cast096_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash096.B00.input).map Fin.val=JGc_TX2_M2.Hash096.B00.input := by rfl
#print axioms cast096_0
theorem tail096 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash096.tail).map Fin.val=JGc_TX2_M2.Hash096.tail := by rfl
#print axioms tail096
theorem numeric096 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash096.message).map Fin.val=JGc_TX2_M2.Hash096.message := by
  simp only [JGc_TX2_M2.Hash096.message,JGc_TX2_M2.Hash096.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast096_0,tail096]
#print axioms numeric096
theorem hash096 : JFp_SHADigest.digest input096=value096 := by
  unfold input096 JFp_SHADigest.digest
  rw [numeric096,JGc_TX2_M2.Hash096.checked]
  rfl
#print axioms hash096
theorem address096 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [28,225,90,243,30,224,184,236,100,56,105,28,167,74,193,122,16,144,67,130,138,62,220,132,53,95,243,22,171,197,183,159]) value084)=input096 := by rfl
#print axioms address096
def tree096 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [28,225,90,243,30,224,184,236,100,56,105,28,167,74,193,122,16,144,67,130,138,62,220,132,53,95,243,22,171,197,183,159])) tree084
theorem root096 : root JFp_SHADigest.digest tree096=value096 := by
  rw [tree096,root,root084]
  exact (congrArg JFp_SHADigest.digest address096).trans hash096
#print axioms root096
theorem shape096 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 3328=tree096 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 3328)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 7 3328 (by decide),siblings 7 (by decide) 3328 (by decide)]
  rw [shape084 f g inputs siblings]
  rfl
#print axioms shape096
def input097 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash097.message
def value097 : State := JFp_SHADigest.output JGc_TX2_M2.Hash097.result
theorem cast097_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash097.B00.input).map Fin.val=JGc_TX2_M2.Hash097.B00.input := by rfl
#print axioms cast097_0
theorem tail097 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash097.tail).map Fin.val=JGc_TX2_M2.Hash097.tail := by rfl
#print axioms tail097
theorem numeric097 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash097.message).map Fin.val=JGc_TX2_M2.Hash097.message := by
  simp only [JGc_TX2_M2.Hash097.message,JGc_TX2_M2.Hash097.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast097_0,tail097]
#print axioms numeric097
theorem hash097 : JFp_SHADigest.digest input097=value097 := by
  unfold input097 JFp_SHADigest.digest
  rw [numeric097,JGc_TX2_M2.Hash097.checked]
  rfl
#print axioms hash097
theorem address097 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [238,220,194,247,220,113,10,193,83,254,24,213,25,97,228,44,24,11,158,49,197,226,85,214,15,227,129,115,153,176,254,173]) value085)=input097 := by rfl
#print axioms address097
def tree097 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [238,220,194,247,220,113,10,193,83,254,24,213,25,97,228,44,24,11,158,49,197,226,85,214,15,227,129,115,153,176,254,173])) tree085
theorem root097 : root JFp_SHADigest.digest tree097=value097 := by
  rw [tree097,root,root085]
  exact (congrArg JFp_SHADigest.digest address097).trans hash097
#print axioms root097
theorem shape097 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 5120=tree097 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 5120)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 7 5120 (by decide),siblings 7 (by decide) 5120 (by decide)]
  rw [shape085 f g inputs siblings]
  rfl
#print axioms shape097
def input098 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash098.message
def value098 : State := JFp_SHADigest.output JGc_TX2_M2.Hash098.result
theorem cast098_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash098.B00.input).map Fin.val=JGc_TX2_M2.Hash098.B00.input := by rfl
#print axioms cast098_0
theorem tail098 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash098.tail).map Fin.val=JGc_TX2_M2.Hash098.tail := by rfl
#print axioms tail098
theorem numeric098 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash098.message).map Fin.val=JGc_TX2_M2.Hash098.message := by
  simp only [JGc_TX2_M2.Hash098.message,JGc_TX2_M2.Hash098.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast098_0,tail098]
#print axioms numeric098
theorem hash098 : JFp_SHADigest.digest input098=value098 := by
  unfold input098 JFp_SHADigest.digest
  rw [numeric098,JGc_TX2_M2.Hash098.checked]
  rfl
#print axioms hash098
theorem address098 : BinMerkle32Path.nodeInput (children value086 (JGc_TX2_HashBytes.state [165,208,220,121,159,171,133,193,69,163,45,70,217,40,69,135,88,52,31,124,84,162,15,25,45,173,154,0,216,0,141,11]))=input098 := by rfl
#print axioms address098
def tree098 : Tree := .branch tree086 (.supplied (JGc_TX2_HashBytes.state [165,208,220,121,159,171,133,193,69,163,45,70,217,40,69,135,88,52,31,124,84,162,15,25,45,173,154,0,216,0,141,11]))
theorem root098 : root JFp_SHADigest.digest tree098=value098 := by
  rw [tree098,root,root086]
  exact (congrArg JFp_SHADigest.digest address098).trans hash098
#print axioms root098
theorem shape098 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 10496=tree098 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 10496)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape086 f g inputs siblings]
  rw [unoccupied f g 7 10624 (by decide),siblings 7 (by decide) 10624 (by decide)]
  rfl
#print axioms shape098
def input099 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash099.message
def value099 : State := JFp_SHADigest.output JGc_TX2_M2.Hash099.result
theorem cast099_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash099.B00.input).map Fin.val=JGc_TX2_M2.Hash099.B00.input := by rfl
#print axioms cast099_0
theorem tail099 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash099.tail).map Fin.val=JGc_TX2_M2.Hash099.tail := by rfl
#print axioms tail099
theorem numeric099 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash099.message).map Fin.val=JGc_TX2_M2.Hash099.message := by
  simp only [JGc_TX2_M2.Hash099.message,JGc_TX2_M2.Hash099.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast099_0,tail099]
#print axioms numeric099
theorem hash099 : JFp_SHADigest.digest input099=value099 := by
  unfold input099 JFp_SHADigest.digest
  rw [numeric099,JGc_TX2_M2.Hash099.checked]
  rfl
#print axioms hash099
theorem address099 : BinMerkle32Path.nodeInput (children value087 (JGc_TX2_HashBytes.state [181,134,27,199,27,153,152,160,151,172,193,101,189,121,139,86,98,252,193,123,48,72,219,191,30,176,244,28,55,4,98,67]))=input099 := by rfl
#print axioms address099
def tree099 : Tree := .branch tree087 (.supplied (JGc_TX2_HashBytes.state [181,134,27,199,27,153,152,160,151,172,193,101,189,121,139,86,98,252,193,123,48,72,219,191,30,176,244,28,55,4,98,67]))
theorem root099 : root JFp_SHADigest.digest tree099=value099 := by
  rw [tree099,root,root087]
  exact (congrArg JFp_SHADigest.digest address099).trans hash099
#print axioms root099
theorem shape099 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 13824=tree099 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 13824)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape087 f g inputs siblings]
  rw [unoccupied f g 7 13952 (by decide),siblings 7 (by decide) 13952 (by decide)]
  rfl
#print axioms shape099
def input100 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash100.message
def value100 : State := JFp_SHADigest.output JGc_TX2_M2.Hash100.result
theorem cast100_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash100.B00.input).map Fin.val=JGc_TX2_M2.Hash100.B00.input := by rfl
#print axioms cast100_0
theorem tail100 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash100.tail).map Fin.val=JGc_TX2_M2.Hash100.tail := by rfl
#print axioms tail100
theorem numeric100 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash100.message).map Fin.val=JGc_TX2_M2.Hash100.message := by
  simp only [JGc_TX2_M2.Hash100.message,JGc_TX2_M2.Hash100.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast100_0,tail100]
#print axioms numeric100
theorem hash100 : JFp_SHADigest.digest input100=value100 := by
  unfold input100 JFp_SHADigest.digest
  rw [numeric100,JGc_TX2_M2.Hash100.checked]
  rfl
#print axioms hash100
theorem address100 : BinMerkle32Path.nodeInput (children value088 (JGc_TX2_HashBytes.state [80,66,201,51,69,64,10,163,166,246,107,3,44,151,202,88,245,141,199,134,77,93,250,72,77,129,167,150,35,71,159,47]))=input100 := by rfl
#print axioms address100
def tree100 : Tree := .branch tree088 (.supplied (JGc_TX2_HashBytes.state [80,66,201,51,69,64,10,163,166,246,107,3,44,151,202,88,245,141,199,134,77,93,250,72,77,129,167,150,35,71,159,47]))
theorem root100 : root JFp_SHADigest.digest tree100=value100 := by
  rw [tree100,root,root088]
  exact (congrArg JFp_SHADigest.digest address100).trans hash100
#print axioms root100
theorem shape100 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 15872=tree100 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 15872)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape088 f g inputs siblings]
  rw [unoccupied f g 7 16000 (by decide),siblings 7 (by decide) 16000 (by decide)]
  rfl
#print axioms shape100
def input101 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash101.message
def value101 : State := JFp_SHADigest.output JGc_TX2_M2.Hash101.result
theorem cast101_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash101.B00.input).map Fin.val=JGc_TX2_M2.Hash101.B00.input := by rfl
#print axioms cast101_0
theorem tail101 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash101.tail).map Fin.val=JGc_TX2_M2.Hash101.tail := by rfl
#print axioms tail101
theorem numeric101 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash101.message).map Fin.val=JGc_TX2_M2.Hash101.message := by
  simp only [JGc_TX2_M2.Hash101.message,JGc_TX2_M2.Hash101.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast101_0,tail101]
#print axioms numeric101
theorem hash101 : JFp_SHADigest.digest input101=value101 := by
  unfold input101 JFp_SHADigest.digest
  rw [numeric101,JGc_TX2_M2.Hash101.checked]
  rfl
#print axioms hash101
theorem address101 : BinMerkle32Path.nodeInput (children value089 (JGc_TX2_HashBytes.state [230,98,146,253,69,100,172,136,68,130,136,171,59,228,136,184,211,17,245,188,24,246,209,56,68,162,124,40,218,43,58,97]))=input101 := by rfl
#print axioms address101
def tree101 : Tree := .branch tree089 (.supplied (JGc_TX2_HashBytes.state [230,98,146,253,69,100,172,136,68,130,136,171,59,228,136,184,211,17,245,188,24,246,209,56,68,162,124,40,218,43,58,97]))
theorem root101 : root JFp_SHADigest.digest tree101=value101 := by
  rw [tree101,root,root089]
  exact (congrArg JFp_SHADigest.digest address101).trans hash101
#print axioms root101
theorem shape101 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 33024=tree101 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 33024)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape089 f g inputs siblings]
  rw [unoccupied f g 7 33152 (by decide),siblings 7 (by decide) 33152 (by decide)]
  rfl
#print axioms shape101
def input102 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash102.message
def value102 : State := JFp_SHADigest.output JGc_TX2_M2.Hash102.result
theorem cast102_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash102.B00.input).map Fin.val=JGc_TX2_M2.Hash102.B00.input := by rfl
#print axioms cast102_0
theorem tail102 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash102.tail).map Fin.val=JGc_TX2_M2.Hash102.tail := by rfl
#print axioms tail102
theorem numeric102 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash102.message).map Fin.val=JGc_TX2_M2.Hash102.message := by
  simp only [JGc_TX2_M2.Hash102.message,JGc_TX2_M2.Hash102.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast102_0,tail102]
#print axioms numeric102
theorem hash102 : JFp_SHADigest.digest input102=value102 := by
  unfold input102 JFp_SHADigest.digest
  rw [numeric102,JGc_TX2_M2.Hash102.checked]
  rfl
#print axioms hash102
theorem address102 : BinMerkle32Path.nodeInput (children value090 (JGc_TX2_HashBytes.state [222,217,218,60,104,155,183,240,243,200,122,75,48,50,180,108,168,24,222,175,197,78,202,150,66,190,85,119,101,185,43,183]))=input102 := by rfl
#print axioms address102
def tree102 : Tree := .branch tree090 (.supplied (JGc_TX2_HashBytes.state [222,217,218,60,104,155,183,240,243,200,122,75,48,50,180,108,168,24,222,175,197,78,202,150,66,190,85,119,101,185,43,183]))
theorem root102 : root JFp_SHADigest.digest tree102=value102 := by
  rw [tree102,root,root090]
  exact (congrArg JFp_SHADigest.digest address102).trans hash102
#print axioms root102
theorem shape102 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 37376=tree102 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 37376)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape090 f g inputs siblings]
  rw [unoccupied f g 7 37504 (by decide),siblings 7 (by decide) 37504 (by decide)]
  rfl
#print axioms shape102
def input103 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash103.message
def value103 : State := JFp_SHADigest.output JGc_TX2_M2.Hash103.result
theorem cast103_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash103.B00.input).map Fin.val=JGc_TX2_M2.Hash103.B00.input := by rfl
#print axioms cast103_0
theorem tail103 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash103.tail).map Fin.val=JGc_TX2_M2.Hash103.tail := by rfl
#print axioms tail103
theorem numeric103 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash103.message).map Fin.val=JGc_TX2_M2.Hash103.message := by
  simp only [JGc_TX2_M2.Hash103.message,JGc_TX2_M2.Hash103.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast103_0,tail103]
#print axioms numeric103
theorem hash103 : JFp_SHADigest.digest input103=value103 := by
  unfold input103 JFp_SHADigest.digest
  rw [numeric103,JGc_TX2_M2.Hash103.checked]
  rfl
#print axioms hash103
theorem address103 : BinMerkle32Path.nodeInput (children value091 (JGc_TX2_HashBytes.state [162,5,212,188,194,167,122,102,84,157,42,38,46,218,75,216,87,68,242,59,22,98,241,109,81,0,119,7,13,147,116,188]))=input103 := by rfl
#print axioms address103
def tree103 : Tree := .branch tree091 (.supplied (JGc_TX2_HashBytes.state [162,5,212,188,194,167,122,102,84,157,42,38,46,218,75,216,87,68,242,59,22,98,241,109,81,0,119,7,13,147,116,188]))
theorem root103 : root JFp_SHADigest.digest tree103=value103 := by
  rw [tree103,root,root091]
  exact (congrArg JFp_SHADigest.digest address103).trans hash103
#print axioms root103
theorem shape103 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 41472=tree103 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 41472)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape091 f g inputs siblings]
  rw [unoccupied f g 7 41600 (by decide),siblings 7 (by decide) 41600 (by decide)]
  rfl
#print axioms shape103
def input104 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash104.message
def value104 : State := JFp_SHADigest.output JGc_TX2_M2.Hash104.result
theorem cast104_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash104.B00.input).map Fin.val=JGc_TX2_M2.Hash104.B00.input := by rfl
#print axioms cast104_0
theorem tail104 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash104.tail).map Fin.val=JGc_TX2_M2.Hash104.tail := by rfl
#print axioms tail104
theorem numeric104 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash104.message).map Fin.val=JGc_TX2_M2.Hash104.message := by
  simp only [JGc_TX2_M2.Hash104.message,JGc_TX2_M2.Hash104.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast104_0,tail104]
#print axioms numeric104
theorem hash104 : JFp_SHADigest.digest input104=value104 := by
  unfold input104 JFp_SHADigest.digest
  rw [numeric104,JGc_TX2_M2.Hash104.checked]
  rfl
#print axioms hash104
theorem address104 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [122,57,168,107,66,194,103,147,118,118,44,1,155,155,88,156,33,129,100,45,191,233,217,135,208,132,159,96,64,19,246,232]) value092)=input104 := by rfl
#print axioms address104
def tree104 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [122,57,168,107,66,194,103,147,118,118,44,1,155,155,88,156,33,129,100,45,191,233,217,135,208,132,159,96,64,19,246,232])) tree092
theorem root104 : root JFp_SHADigest.digest tree104=value104 := by
  rw [tree104,root,root092]
  exact (congrArg JFp_SHADigest.digest address104).trans hash104
#print axioms root104
theorem shape104 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 44288=tree104 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 44288)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 7 44288 (by decide),siblings 7 (by decide) 44288 (by decide)]
  rw [shape092 f g inputs siblings]
  rfl
#print axioms shape104
def input105 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash105.message
def value105 : State := JFp_SHADigest.output JGc_TX2_M2.Hash105.result
theorem cast105_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash105.B00.input).map Fin.val=JGc_TX2_M2.Hash105.B00.input := by rfl
#print axioms cast105_0
theorem tail105 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash105.tail).map Fin.val=JGc_TX2_M2.Hash105.tail := by rfl
#print axioms tail105
theorem numeric105 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash105.message).map Fin.val=JGc_TX2_M2.Hash105.message := by
  simp only [JGc_TX2_M2.Hash105.message,JGc_TX2_M2.Hash105.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast105_0,tail105]
#print axioms numeric105
theorem hash105 : JFp_SHADigest.digest input105=value105 := by
  unfold input105 JFp_SHADigest.digest
  rw [numeric105,JGc_TX2_M2.Hash105.checked]
  rfl
#print axioms hash105
theorem address105 : BinMerkle32Path.nodeInput (children value093 (JGc_TX2_HashBytes.state [189,161,193,33,154,45,28,203,161,12,72,108,194,138,192,165,225,205,107,216,142,84,22,99,213,113,73,173,137,38,197,93]))=input105 := by rfl
#print axioms address105
def tree105 : Tree := .branch tree093 (.supplied (JGc_TX2_HashBytes.state [189,161,193,33,154,45,28,203,161,12,72,108,194,138,192,165,225,205,107,216,142,84,22,99,213,113,73,173,137,38,197,93]))
theorem root105 : root JFp_SHADigest.digest tree105=value105 := by
  rw [tree105,root,root093]
  exact (congrArg JFp_SHADigest.digest address105).trans hash105
#print axioms root105
theorem shape105 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 44800=tree105 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 44800)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape093 f g inputs siblings]
  rw [unoccupied f g 7 44928 (by decide),siblings 7 (by decide) 44928 (by decide)]
  rfl
#print axioms shape105
def input106 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash106.message
def value106 : State := JFp_SHADigest.output JGc_TX2_M2.Hash106.result
theorem cast106_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash106.B00.input).map Fin.val=JGc_TX2_M2.Hash106.B00.input := by rfl
#print axioms cast106_0
theorem tail106 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash106.tail).map Fin.val=JGc_TX2_M2.Hash106.tail := by rfl
#print axioms tail106
theorem numeric106 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash106.message).map Fin.val=JGc_TX2_M2.Hash106.message := by
  simp only [JGc_TX2_M2.Hash106.message,JGc_TX2_M2.Hash106.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast106_0,tail106]
#print axioms numeric106
theorem hash106 : JFp_SHADigest.digest input106=value106 := by
  unfold input106 JFp_SHADigest.digest
  rw [numeric106,JGc_TX2_M2.Hash106.checked]
  rfl
#print axioms hash106
theorem address106 : BinMerkle32Path.nodeInput (children value094 (JGc_TX2_HashBytes.state [28,199,112,185,124,21,12,200,73,81,243,251,45,9,76,88,249,49,148,21,81,57,238,4,78,6,76,133,161,191,178,242]))=input106 := by rfl
#print axioms address106
def tree106 : Tree := .branch tree094 (.supplied (JGc_TX2_HashBytes.state [28,199,112,185,124,21,12,200,73,81,243,251,45,9,76,88,249,49,148,21,81,57,238,4,78,6,76,133,161,191,178,242]))
theorem root106 : root JFp_SHADigest.digest tree106=value106 := by
  rw [tree106,root,root094]
  exact (congrArg JFp_SHADigest.digest address106).trans hash106
#print axioms root106
theorem shape106 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 46336=tree106 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 46336)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape094 f g inputs siblings]
  rw [unoccupied f g 7 46464 (by decide),siblings 7 (by decide) 46464 (by decide)]
  rfl
#print axioms shape106
def input107 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash107.message
def value107 : State := JFp_SHADigest.output JGc_TX2_M2.Hash107.result
theorem cast107_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash107.B00.input).map Fin.val=JGc_TX2_M2.Hash107.B00.input := by rfl
#print axioms cast107_0
theorem tail107 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash107.tail).map Fin.val=JGc_TX2_M2.Hash107.tail := by rfl
#print axioms tail107
theorem numeric107 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash107.message).map Fin.val=JGc_TX2_M2.Hash107.message := by
  simp only [JGc_TX2_M2.Hash107.message,JGc_TX2_M2.Hash107.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast107_0,tail107]
#print axioms numeric107
theorem hash107 : JFp_SHADigest.digest input107=value107 := by
  unfold input107 JFp_SHADigest.digest
  rw [numeric107,JGc_TX2_M2.Hash107.checked]
  rfl
#print axioms hash107
theorem address107 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [60,35,71,152,98,250,57,95,190,164,242,171,150,136,250,13,115,103,187,32,110,48,103,160,127,120,86,39,251,167,45,94]) value095)=input107 := by rfl
#print axioms address107
def tree107 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [60,35,71,152,98,250,57,95,190,164,242,171,150,136,250,13,115,103,187,32,110,48,103,160,127,120,86,39,251,167,45,94])) tree095
theorem root107 : root JFp_SHADigest.digest tree107=value107 := by
  rw [tree107,root,root095]
  exact (congrArg JFp_SHADigest.digest address107).trans hash107
#print axioms root107
theorem shape107 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 54272=tree107 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 54272)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 7 54272 (by decide),siblings 7 (by decide) 54272 (by decide)]
  rw [shape095 f g inputs siblings]
  rfl
#print axioms shape107
end AspisR1.JGc_TX2_M2Roots
end
