import NDO_JGh_TX2_M1Level06
import NDO_JGh_TX2_M1W025
import NDO_JGh_TX2_M1W026
import NDO_JGh_TX2_M1W027
import NDO_JGh_TX2_M1W028
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input096 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash096.message
def value096 : State := JFp_SHADigest.output JGh_TX2_M1.Hash096.result
theorem cast096_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash096.B00.input).map Fin.val=JGh_TX2_M1.Hash096.B00.input := by rfl
#print axioms cast096_0
theorem tail096 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash096.tail).map Fin.val=JGh_TX2_M1.Hash096.tail := by rfl
#print axioms tail096
theorem numeric096 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash096.message).map Fin.val=JGh_TX2_M1.Hash096.message := by
  simp only [JGh_TX2_M1.Hash096.message,JGh_TX2_M1.Hash096.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast096_0,tail096]
#print axioms numeric096
theorem hash096 : JFp_SHADigest.digest input096=value096 := by
  unfold input096 JFp_SHADigest.digest
  rw [numeric096,JGh_TX2_M1.Hash096.checked]
  rfl
#print axioms hash096
theorem address096 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [203,9,133,227,15,195,21,115,223,53,152,174,124,199,4,94,229,118,63,214,217,122,22,128,174,253,10,14,171,97,252,197]) value084)=input096 := by rfl
#print axioms address096
def tree096 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [203,9,133,227,15,195,21,115,223,53,152,174,124,199,4,94,229,118,63,214,217,122,22,128,174,253,10,14,171,97,252,197])) tree084
theorem root096 : root JFp_SHADigest.digest tree096=value096 := by
  rw [tree096,root,root084]
  exact (congrArg JFp_SHADigest.digest address096).trans hash096
#print axioms root096
theorem shape096 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 14080=tree096 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 14080)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 7 14080 (by decide),siblings 7 (by decide) 14080 (by decide)]
  rw [shape084 f g inputs siblings]
  rfl
#print axioms shape096
def input097 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash097.message
def value097 : State := JFp_SHADigest.output JGh_TX2_M1.Hash097.result
theorem cast097_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash097.B00.input).map Fin.val=JGh_TX2_M1.Hash097.B00.input := by rfl
#print axioms cast097_0
theorem tail097 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash097.tail).map Fin.val=JGh_TX2_M1.Hash097.tail := by rfl
#print axioms tail097
theorem numeric097 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash097.message).map Fin.val=JGh_TX2_M1.Hash097.message := by
  simp only [JGh_TX2_M1.Hash097.message,JGh_TX2_M1.Hash097.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast097_0,tail097]
#print axioms numeric097
theorem hash097 : JFp_SHADigest.digest input097=value097 := by
  unfold input097 JFp_SHADigest.digest
  rw [numeric097,JGh_TX2_M1.Hash097.checked]
  rfl
#print axioms hash097
theorem address097 : BinMerkle32Path.nodeInput (children value085 (JGc_TX2_HashBytes.state [4,111,221,72,213,154,98,139,231,197,10,227,180,103,86,61,114,160,110,73,66,39,22,40,71,225,154,223,55,58,205,108]))=input097 := by rfl
#print axioms address097
def tree097 : Tree := .branch tree085 (.supplied (JGc_TX2_HashBytes.state [4,111,221,72,213,154,98,139,231,197,10,227,180,103,86,61,114,160,110,73,66,39,22,40,71,225,154,223,55,58,205,108]))
theorem root097 : root JFp_SHADigest.digest tree097=value097 := by
  rw [tree097,root,root085]
  exact (congrArg JFp_SHADigest.digest address097).trans hash097
#print axioms root097
theorem shape097 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 21248=tree097 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 21248)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape085 f g inputs siblings]
  rw [unoccupied f g 7 21376 (by decide),siblings 7 (by decide) 21376 (by decide)]
  rfl
#print axioms shape097
def input098 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash098.message
def value098 : State := JFp_SHADigest.output JGh_TX2_M1.Hash098.result
theorem cast098_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash098.B00.input).map Fin.val=JGh_TX2_M1.Hash098.B00.input := by rfl
#print axioms cast098_0
theorem tail098 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash098.tail).map Fin.val=JGh_TX2_M1.Hash098.tail := by rfl
#print axioms tail098
theorem numeric098 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash098.message).map Fin.val=JGh_TX2_M1.Hash098.message := by
  simp only [JGh_TX2_M1.Hash098.message,JGh_TX2_M1.Hash098.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast098_0,tail098]
#print axioms numeric098
theorem hash098 : JFp_SHADigest.digest input098=value098 := by
  unfold input098 JFp_SHADigest.digest
  rw [numeric098,JGh_TX2_M1.Hash098.checked]
  rfl
#print axioms hash098
theorem address098 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [73,249,200,133,96,173,28,175,204,110,144,41,6,64,159,174,225,179,179,207,101,205,137,114,231,100,35,81,143,125,160,80]) value086)=input098 := by rfl
#print axioms address098
def tree098 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [73,249,200,133,96,173,28,175,204,110,144,41,6,64,159,174,225,179,179,207,101,205,137,114,231,100,35,81,143,125,160,80])) tree086
theorem root098 : root JFp_SHADigest.digest tree098=value098 := by
  rw [tree098,root,root086]
  exact (congrArg JFp_SHADigest.digest address098).trans hash098
#print axioms root098
theorem shape098 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 41984=tree098 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 41984)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 7 41984 (by decide),siblings 7 (by decide) 41984 (by decide)]
  rw [shape086 f g inputs siblings]
  rfl
#print axioms shape098
def input099 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash099.message
def value099 : State := JFp_SHADigest.output JGh_TX2_M1.Hash099.result
theorem cast099_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash099.B00.input).map Fin.val=JGh_TX2_M1.Hash099.B00.input := by rfl
#print axioms cast099_0
theorem tail099 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash099.tail).map Fin.val=JGh_TX2_M1.Hash099.tail := by rfl
#print axioms tail099
theorem numeric099 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash099.message).map Fin.val=JGh_TX2_M1.Hash099.message := by
  simp only [JGh_TX2_M1.Hash099.message,JGh_TX2_M1.Hash099.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast099_0,tail099]
#print axioms numeric099
theorem hash099 : JFp_SHADigest.digest input099=value099 := by
  unfold input099 JFp_SHADigest.digest
  rw [numeric099,JGh_TX2_M1.Hash099.checked]
  rfl
#print axioms hash099
theorem address099 : BinMerkle32Path.nodeInput (children value087 (JGc_TX2_HashBytes.state [40,152,225,228,234,20,139,186,209,211,179,52,223,219,213,227,61,184,135,134,121,131,254,163,17,154,210,129,147,10,15,237]))=input099 := by rfl
#print axioms address099
def tree099 : Tree := .branch tree087 (.supplied (JGc_TX2_HashBytes.state [40,152,225,228,234,20,139,186,209,211,179,52,223,219,213,227,61,184,135,134,121,131,254,163,17,154,210,129,147,10,15,237]))
theorem root099 : root JFp_SHADigest.digest tree099=value099 := by
  rw [tree099,root,root087]
  exact (congrArg JFp_SHADigest.digest address099).trans hash099
#print axioms root099
theorem shape099 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 55296=tree099 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 55296)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape087 f g inputs siblings]
  rw [unoccupied f g 7 55424 (by decide),siblings 7 (by decide) 55424 (by decide)]
  rfl
#print axioms shape099
def input100 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash100.message
def value100 : State := JFp_SHADigest.output JGh_TX2_M1.Hash100.result
theorem cast100_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash100.B00.input).map Fin.val=JGh_TX2_M1.Hash100.B00.input := by rfl
#print axioms cast100_0
theorem tail100 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash100.tail).map Fin.val=JGh_TX2_M1.Hash100.tail := by rfl
#print axioms tail100
theorem numeric100 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash100.message).map Fin.val=JGh_TX2_M1.Hash100.message := by
  simp only [JGh_TX2_M1.Hash100.message,JGh_TX2_M1.Hash100.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast100_0,tail100]
#print axioms numeric100
theorem hash100 : JFp_SHADigest.digest input100=value100 := by
  unfold input100 JFp_SHADigest.digest
  rw [numeric100,JGh_TX2_M1.Hash100.checked]
  rfl
#print axioms hash100
theorem address100 : BinMerkle32Path.nodeInput (children value088 (JGc_TX2_HashBytes.state [240,142,169,184,183,101,200,198,128,106,126,146,216,97,129,238,198,129,196,235,159,83,117,254,163,93,137,7,144,104,234,135]))=input100 := by rfl
#print axioms address100
def tree100 : Tree := .branch tree088 (.supplied (JGc_TX2_HashBytes.state [240,142,169,184,183,101,200,198,128,106,126,146,216,97,129,238,198,129,196,235,159,83,117,254,163,93,137,7,144,104,234,135]))
theorem root100 : root JFp_SHADigest.digest tree100=value100 := by
  rw [tree100,root,root088]
  exact (congrArg JFp_SHADigest.digest address100).trans hash100
#print axioms root100
theorem shape100 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 63744=tree100 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 63744)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape088 f g inputs siblings]
  rw [unoccupied f g 7 63872 (by decide),siblings 7 (by decide) 63872 (by decide)]
  rfl
#print axioms shape100
def input101 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash101.message
def value101 : State := JFp_SHADigest.output JGh_TX2_M1.Hash101.result
theorem cast101_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash101.B00.input).map Fin.val=JGh_TX2_M1.Hash101.B00.input := by rfl
#print axioms cast101_0
theorem tail101 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash101.tail).map Fin.val=JGh_TX2_M1.Hash101.tail := by rfl
#print axioms tail101
theorem numeric101 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash101.message).map Fin.val=JGh_TX2_M1.Hash101.message := by
  simp only [JGh_TX2_M1.Hash101.message,JGh_TX2_M1.Hash101.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast101_0,tail101]
#print axioms numeric101
theorem hash101 : JFp_SHADigest.digest input101=value101 := by
  unfold input101 JFp_SHADigest.digest
  rw [numeric101,JGh_TX2_M1.Hash101.checked]
  rfl
#print axioms hash101
theorem address101 : BinMerkle32Path.nodeInput (children value089 (JGc_TX2_HashBytes.state [194,210,7,150,249,28,210,137,57,196,112,39,213,114,31,103,65,61,98,96,111,4,214,212,17,250,158,230,132,1,25,147]))=input101 := by rfl
#print axioms address101
def tree101 : Tree := .branch tree089 (.supplied (JGc_TX2_HashBytes.state [194,210,7,150,249,28,210,137,57,196,112,39,213,114,31,103,65,61,98,96,111,4,214,212,17,250,158,230,132,1,25,147]))
theorem root101 : root JFp_SHADigest.digest tree101=value101 := by
  rw [tree101,root,root089]
  exact (congrArg JFp_SHADigest.digest address101).trans hash101
#print axioms root101
theorem shape101 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 132352=tree101 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 132352)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape089 f g inputs siblings]
  rw [unoccupied f g 7 132480 (by decide),siblings 7 (by decide) 132480 (by decide)]
  rfl
#print axioms shape101
def input102 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash102.message
def value102 : State := JFp_SHADigest.output JGh_TX2_M1.Hash102.result
theorem cast102_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash102.B00.input).map Fin.val=JGh_TX2_M1.Hash102.B00.input := by rfl
#print axioms cast102_0
theorem tail102 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash102.tail).map Fin.val=JGh_TX2_M1.Hash102.tail := by rfl
#print axioms tail102
theorem numeric102 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash102.message).map Fin.val=JGh_TX2_M1.Hash102.message := by
  simp only [JGh_TX2_M1.Hash102.message,JGh_TX2_M1.Hash102.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast102_0,tail102]
#print axioms numeric102
theorem hash102 : JFp_SHADigest.digest input102=value102 := by
  unfold input102 JFp_SHADigest.digest
  rw [numeric102,JGh_TX2_M1.Hash102.checked]
  rfl
#print axioms hash102
theorem address102 : BinMerkle32Path.nodeInput (children value090 (JGc_TX2_HashBytes.state [239,30,19,252,85,32,149,121,101,222,131,47,177,239,199,64,148,207,250,56,169,32,232,115,191,143,189,147,209,21,196,209]))=input102 := by rfl
#print axioms address102
def tree102 : Tree := .branch tree090 (.supplied (JGc_TX2_HashBytes.state [239,30,19,252,85,32,149,121,101,222,131,47,177,239,199,64,148,207,250,56,169,32,232,115,191,143,189,147,209,21,196,209]))
theorem root102 : root JFp_SHADigest.digest tree102=value102 := by
  rw [tree102,root,root090]
  exact (congrArg JFp_SHADigest.digest address102).trans hash102
#print axioms root102
theorem shape102 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 149504=tree102 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 149504)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape090 f g inputs siblings]
  rw [unoccupied f g 7 149632 (by decide),siblings 7 (by decide) 149632 (by decide)]
  rfl
#print axioms shape102
def input103 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash103.message
def value103 : State := JFp_SHADigest.output JGh_TX2_M1.Hash103.result
theorem cast103_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash103.B00.input).map Fin.val=JGh_TX2_M1.Hash103.B00.input := by rfl
#print axioms cast103_0
theorem tail103 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash103.tail).map Fin.val=JGh_TX2_M1.Hash103.tail := by rfl
#print axioms tail103
theorem numeric103 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash103.message).map Fin.val=JGh_TX2_M1.Hash103.message := by
  simp only [JGh_TX2_M1.Hash103.message,JGh_TX2_M1.Hash103.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast103_0,tail103]
#print axioms numeric103
theorem hash103 : JFp_SHADigest.digest input103=value103 := by
  unfold input103 JFp_SHADigest.digest
  rw [numeric103,JGh_TX2_M1.Hash103.checked]
  rfl
#print axioms hash103
theorem address103 : BinMerkle32Path.nodeInput (children value091 (JGc_TX2_HashBytes.state [143,95,171,144,248,1,113,242,91,50,229,44,34,64,188,191,101,120,169,118,86,155,27,164,177,185,137,226,233,96,216,49]))=input103 := by rfl
#print axioms address103
def tree103 : Tree := .branch tree091 (.supplied (JGc_TX2_HashBytes.state [143,95,171,144,248,1,113,242,91,50,229,44,34,64,188,191,101,120,169,118,86,155,27,164,177,185,137,226,233,96,216,49]))
theorem root103 : root JFp_SHADigest.digest tree103=value103 := by
  rw [tree103,root,root091]
  exact (congrArg JFp_SHADigest.digest address103).trans hash103
#print axioms root103
theorem shape103 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 166144=tree103 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 166144)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape091 f g inputs siblings]
  rw [unoccupied f g 7 166272 (by decide),siblings 7 (by decide) 166272 (by decide)]
  rfl
#print axioms shape103
def input104 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash104.message
def value104 : State := JFp_SHADigest.output JGh_TX2_M1.Hash104.result
theorem cast104_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash104.B00.input).map Fin.val=JGh_TX2_M1.Hash104.B00.input := by rfl
#print axioms cast104_0
theorem tail104 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash104.tail).map Fin.val=JGh_TX2_M1.Hash104.tail := by rfl
#print axioms tail104
theorem numeric104 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash104.message).map Fin.val=JGh_TX2_M1.Hash104.message := by
  simp only [JGh_TX2_M1.Hash104.message,JGh_TX2_M1.Hash104.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast104_0,tail104]
#print axioms numeric104
theorem hash104 : JFp_SHADigest.digest input104=value104 := by
  unfold input104 JFp_SHADigest.digest
  rw [numeric104,JGh_TX2_M1.Hash104.checked]
  rfl
#print axioms hash104
theorem address104 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [120,184,180,182,8,74,113,147,122,226,22,124,100,32,230,17,155,26,169,107,143,50,96,36,14,170,84,170,213,28,126,106]) value092)=input104 := by rfl
#print axioms address104
def tree104 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [120,184,180,182,8,74,113,147,122,226,22,124,100,32,230,17,155,26,169,107,143,50,96,36,14,170,84,170,213,28,126,106])) tree092
theorem root104 : root JFp_SHADigest.digest tree104=value104 := by
  rw [tree104,root,root092]
  exact (congrArg JFp_SHADigest.digest address104).trans hash104
#print axioms root104
theorem shape104 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 177920=tree104 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 177920)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 7 177920 (by decide),siblings 7 (by decide) 177920 (by decide)]
  rw [shape092 f g inputs siblings]
  rfl
#print axioms shape104
def input105 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash105.message
def value105 : State := JFp_SHADigest.output JGh_TX2_M1.Hash105.result
theorem cast105_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash105.B00.input).map Fin.val=JGh_TX2_M1.Hash105.B00.input := by rfl
#print axioms cast105_0
theorem tail105 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash105.tail).map Fin.val=JGh_TX2_M1.Hash105.tail := by rfl
#print axioms tail105
theorem numeric105 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash105.message).map Fin.val=JGh_TX2_M1.Hash105.message := by
  simp only [JGh_TX2_M1.Hash105.message,JGh_TX2_M1.Hash105.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast105_0,tail105]
#print axioms numeric105
theorem hash105 : JFp_SHADigest.digest input105=value105 := by
  unfold input105 JFp_SHADigest.digest
  rw [numeric105,JGh_TX2_M1.Hash105.checked]
  rfl
#print axioms hash105
theorem address105 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [217,0,49,133,129,84,241,85,163,17,81,91,191,20,0,243,27,242,234,67,185,82,199,214,175,143,194,28,186,243,133,44]) value093)=input105 := by rfl
#print axioms address105
def tree105 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [217,0,49,133,129,84,241,85,163,17,81,91,191,20,0,243,27,242,234,67,185,82,199,214,175,143,194,28,186,243,133,44])) tree093
theorem root105 : root JFp_SHADigest.digest tree105=value105 := by
  rw [tree105,root,root093]
  exact (congrArg JFp_SHADigest.digest address105).trans hash105
#print axioms root105
theorem shape105 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 179456=tree105 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 179456)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 7 179456 (by decide),siblings 7 (by decide) 179456 (by decide)]
  rw [shape093 f g inputs siblings]
  rfl
#print axioms shape105
def input106 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash106.message
def value106 : State := JFp_SHADigest.output JGh_TX2_M1.Hash106.result
theorem cast106_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash106.B00.input).map Fin.val=JGh_TX2_M1.Hash106.B00.input := by rfl
#print axioms cast106_0
theorem tail106 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash106.tail).map Fin.val=JGh_TX2_M1.Hash106.tail := by rfl
#print axioms tail106
theorem numeric106 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash106.message).map Fin.val=JGh_TX2_M1.Hash106.message := by
  simp only [JGh_TX2_M1.Hash106.message,JGh_TX2_M1.Hash106.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast106_0,tail106]
#print axioms numeric106
theorem hash106 : JFp_SHADigest.digest input106=value106 := by
  unfold input106 JFp_SHADigest.digest
  rw [numeric106,JGh_TX2_M1.Hash106.checked]
  rfl
#print axioms hash106
theorem address106 : BinMerkle32Path.nodeInput (children value094 (JGc_TX2_HashBytes.state [174,76,24,53,14,201,201,53,29,168,105,97,99,242,26,158,165,206,196,172,222,174,132,172,223,235,1,115,185,246,112,40]))=input106 := by rfl
#print axioms address106
def tree106 : Tree := .branch tree094 (.supplied (JGc_TX2_HashBytes.state [174,76,24,53,14,201,201,53,29,168,105,97,99,242,26,158,165,206,196,172,222,174,132,172,223,235,1,115,185,246,112,40]))
theorem root106 : root JFp_SHADigest.digest tree106=value106 := by
  rw [tree106,root,root094]
  exact (congrArg JFp_SHADigest.digest address106).trans hash106
#print axioms root106
theorem shape106 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 185600=tree106 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 185600)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape094 f g inputs siblings]
  rw [unoccupied f g 7 185728 (by decide),siblings 7 (by decide) 185728 (by decide)]
  rfl
#print axioms shape106
def input107 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash107.message
def value107 : State := JFp_SHADigest.output JGh_TX2_M1.Hash107.result
theorem cast107_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash107.B00.input).map Fin.val=JGh_TX2_M1.Hash107.B00.input := by rfl
#print axioms cast107_0
theorem tail107 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash107.tail).map Fin.val=JGh_TX2_M1.Hash107.tail := by rfl
#print axioms tail107
theorem numeric107 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash107.message).map Fin.val=JGh_TX2_M1.Hash107.message := by
  simp only [JGh_TX2_M1.Hash107.message,JGh_TX2_M1.Hash107.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast107_0,tail107]
#print axioms numeric107
theorem hash107 : JFp_SHADigest.digest input107=value107 := by
  unfold input107 JFp_SHADigest.digest
  rw [numeric107,JGh_TX2_M1.Hash107.checked]
  rfl
#print axioms hash107
theorem address107 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [254,149,11,180,204,235,24,36,233,34,55,139,83,230,33,23,28,105,193,218,39,103,170,119,89,206,184,198,95,29,57,222]) value095)=input107 := by rfl
#print axioms address107
def tree107 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [254,149,11,180,204,235,24,36,233,34,55,139,83,230,33,23,28,105,193,218,39,103,170,119,89,206,184,198,95,29,57,222])) tree095
theorem root107 : root JFp_SHADigest.digest tree107=value107 := by
  rw [tree107,root,root095]
  exact (congrArg JFp_SHADigest.digest address107).trans hash107
#print axioms root107
theorem shape107 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 217856=tree107 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 217856)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 7 217856 (by decide),siblings 7 (by decide) 217856 (by decide)]
  rw [shape095 f g inputs siblings]
  rfl
#print axioms shape107
end AspisR1.JGh_TX2_M1Roots
end
