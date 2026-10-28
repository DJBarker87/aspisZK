import NDO_JGf_TX2_M0Level06
import NDO_JGf_TX2_M0W034
import NDO_JGf_TX2_M0W035
import NDO_JGf_TX2_M0W036
import NDO_JGf_TX2_M0W037
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGf_TX2_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input096 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash096.message
def value096 : State := JFp_SHADigest.output JGf_TX2_M0.Hash096.result
theorem cast096_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash096.B00.input).map Fin.val=JGf_TX2_M0.Hash096.B00.input := by rfl
#print axioms cast096_0
theorem tail096 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash096.tail).map Fin.val=JGf_TX2_M0.Hash096.tail := by rfl
#print axioms tail096
theorem numeric096 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash096.message).map Fin.val=JGf_TX2_M0.Hash096.message := by
  simp only [JGf_TX2_M0.Hash096.message,JGf_TX2_M0.Hash096.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast096_0,tail096]
#print axioms numeric096
theorem hash096 : JFp_SHADigest.digest input096=value096 := by
  unfold input096 JFp_SHADigest.digest
  rw [numeric096,JGf_TX2_M0.Hash096.checked]
  rfl
#print axioms hash096
theorem address096 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [154,196,158,83,225,138,155,204,15,188,194,141,98,24,5,89,230,125,90,227,1,139,195,233,25,8,7,62,166,144,120,111]) value084)=input096 := by rfl
#print axioms address096
def tree096 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [154,196,158,83,225,138,155,204,15,188,194,141,98,24,5,89,230,125,90,227,1,139,195,233,25,8,7,62,166,144,120,111])) tree084
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
def input097 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash097.message
def value097 : State := JFp_SHADigest.output JGf_TX2_M0.Hash097.result
theorem cast097_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash097.B00.input).map Fin.val=JGf_TX2_M0.Hash097.B00.input := by rfl
#print axioms cast097_0
theorem tail097 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash097.tail).map Fin.val=JGf_TX2_M0.Hash097.tail := by rfl
#print axioms tail097
theorem numeric097 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash097.message).map Fin.val=JGf_TX2_M0.Hash097.message := by
  simp only [JGf_TX2_M0.Hash097.message,JGf_TX2_M0.Hash097.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast097_0,tail097]
#print axioms numeric097
theorem hash097 : JFp_SHADigest.digest input097=value097 := by
  unfold input097 JFp_SHADigest.digest
  rw [numeric097,JGf_TX2_M0.Hash097.checked]
  rfl
#print axioms hash097
theorem address097 : BinMerkle32Path.nodeInput (children value085 (JGc_TX2_HashBytes.state [62,190,183,90,214,113,62,8,127,162,61,211,66,179,174,193,183,158,239,50,249,229,102,43,115,127,111,181,114,124,52,181]))=input097 := by rfl
#print axioms address097
def tree097 : Tree := .branch tree085 (.supplied (JGc_TX2_HashBytes.state [62,190,183,90,214,113,62,8,127,162,61,211,66,179,174,193,183,158,239,50,249,229,102,43,115,127,111,181,114,124,52,181]))
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
def input098 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash098.message
def value098 : State := JFp_SHADigest.output JGf_TX2_M0.Hash098.result
theorem cast098_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash098.B00.input).map Fin.val=JGf_TX2_M0.Hash098.B00.input := by rfl
#print axioms cast098_0
theorem tail098 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash098.tail).map Fin.val=JGf_TX2_M0.Hash098.tail := by rfl
#print axioms tail098
theorem numeric098 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash098.message).map Fin.val=JGf_TX2_M0.Hash098.message := by
  simp only [JGf_TX2_M0.Hash098.message,JGf_TX2_M0.Hash098.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast098_0,tail098]
#print axioms numeric098
theorem hash098 : JFp_SHADigest.digest input098=value098 := by
  unfold input098 JFp_SHADigest.digest
  rw [numeric098,JGf_TX2_M0.Hash098.checked]
  rfl
#print axioms hash098
theorem address098 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [155,218,187,48,251,227,199,80,81,155,135,194,194,128,51,189,239,124,160,95,208,171,201,132,123,222,44,247,69,84,116,159]) value086)=input098 := by rfl
#print axioms address098
def tree098 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [155,218,187,48,251,227,199,80,81,155,135,194,194,128,51,189,239,124,160,95,208,171,201,132,123,222,44,247,69,84,116,159])) tree086
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
def input099 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash099.message
def value099 : State := JFp_SHADigest.output JGf_TX2_M0.Hash099.result
theorem cast099_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash099.B00.input).map Fin.val=JGf_TX2_M0.Hash099.B00.input := by rfl
#print axioms cast099_0
theorem tail099 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash099.tail).map Fin.val=JGf_TX2_M0.Hash099.tail := by rfl
#print axioms tail099
theorem numeric099 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash099.message).map Fin.val=JGf_TX2_M0.Hash099.message := by
  simp only [JGf_TX2_M0.Hash099.message,JGf_TX2_M0.Hash099.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast099_0,tail099]
#print axioms numeric099
theorem hash099 : JFp_SHADigest.digest input099=value099 := by
  unfold input099 JFp_SHADigest.digest
  rw [numeric099,JGf_TX2_M0.Hash099.checked]
  rfl
#print axioms hash099
theorem address099 : BinMerkle32Path.nodeInput (children value087 (JGc_TX2_HashBytes.state [83,82,25,190,253,83,86,106,36,200,123,74,223,69,140,96,11,218,240,121,218,147,236,101,198,142,197,124,220,161,42,170]))=input099 := by rfl
#print axioms address099
def tree099 : Tree := .branch tree087 (.supplied (JGc_TX2_HashBytes.state [83,82,25,190,253,83,86,106,36,200,123,74,223,69,140,96,11,218,240,121,218,147,236,101,198,142,197,124,220,161,42,170]))
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
def input100 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash100.message
def value100 : State := JFp_SHADigest.output JGf_TX2_M0.Hash100.result
theorem cast100_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash100.B00.input).map Fin.val=JGf_TX2_M0.Hash100.B00.input := by rfl
#print axioms cast100_0
theorem tail100 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash100.tail).map Fin.val=JGf_TX2_M0.Hash100.tail := by rfl
#print axioms tail100
theorem numeric100 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash100.message).map Fin.val=JGf_TX2_M0.Hash100.message := by
  simp only [JGf_TX2_M0.Hash100.message,JGf_TX2_M0.Hash100.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast100_0,tail100]
#print axioms numeric100
theorem hash100 : JFp_SHADigest.digest input100=value100 := by
  unfold input100 JFp_SHADigest.digest
  rw [numeric100,JGf_TX2_M0.Hash100.checked]
  rfl
#print axioms hash100
theorem address100 : BinMerkle32Path.nodeInput (children value088 (JGc_TX2_HashBytes.state [76,118,195,201,179,196,33,57,102,90,164,60,89,12,229,183,221,74,52,152,87,93,170,126,158,163,228,138,193,131,149,195]))=input100 := by rfl
#print axioms address100
def tree100 : Tree := .branch tree088 (.supplied (JGc_TX2_HashBytes.state [76,118,195,201,179,196,33,57,102,90,164,60,89,12,229,183,221,74,52,152,87,93,170,126,158,163,228,138,193,131,149,195]))
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
def input101 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash101.message
def value101 : State := JFp_SHADigest.output JGf_TX2_M0.Hash101.result
theorem cast101_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash101.B00.input).map Fin.val=JGf_TX2_M0.Hash101.B00.input := by rfl
#print axioms cast101_0
theorem tail101 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash101.tail).map Fin.val=JGf_TX2_M0.Hash101.tail := by rfl
#print axioms tail101
theorem numeric101 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash101.message).map Fin.val=JGf_TX2_M0.Hash101.message := by
  simp only [JGf_TX2_M0.Hash101.message,JGf_TX2_M0.Hash101.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast101_0,tail101]
#print axioms numeric101
theorem hash101 : JFp_SHADigest.digest input101=value101 := by
  unfold input101 JFp_SHADigest.digest
  rw [numeric101,JGf_TX2_M0.Hash101.checked]
  rfl
#print axioms hash101
theorem address101 : BinMerkle32Path.nodeInput (children value089 (JGc_TX2_HashBytes.state [229,248,176,60,192,231,190,241,164,8,162,113,239,200,72,227,57,150,131,123,201,16,107,182,204,183,188,61,71,142,112,66]))=input101 := by rfl
#print axioms address101
def tree101 : Tree := .branch tree089 (.supplied (JGc_TX2_HashBytes.state [229,248,176,60,192,231,190,241,164,8,162,113,239,200,72,227,57,150,131,123,201,16,107,182,204,183,188,61,71,142,112,66]))
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
def input102 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash102.message
def value102 : State := JFp_SHADigest.output JGf_TX2_M0.Hash102.result
theorem cast102_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash102.B00.input).map Fin.val=JGf_TX2_M0.Hash102.B00.input := by rfl
#print axioms cast102_0
theorem tail102 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash102.tail).map Fin.val=JGf_TX2_M0.Hash102.tail := by rfl
#print axioms tail102
theorem numeric102 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash102.message).map Fin.val=JGf_TX2_M0.Hash102.message := by
  simp only [JGf_TX2_M0.Hash102.message,JGf_TX2_M0.Hash102.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast102_0,tail102]
#print axioms numeric102
theorem hash102 : JFp_SHADigest.digest input102=value102 := by
  unfold input102 JFp_SHADigest.digest
  rw [numeric102,JGf_TX2_M0.Hash102.checked]
  rfl
#print axioms hash102
theorem address102 : BinMerkle32Path.nodeInput (children value090 (JGc_TX2_HashBytes.state [169,130,242,107,221,151,67,37,2,35,179,227,197,44,54,153,109,251,14,185,80,61,202,8,29,105,78,26,100,101,48,80]))=input102 := by rfl
#print axioms address102
def tree102 : Tree := .branch tree090 (.supplied (JGc_TX2_HashBytes.state [169,130,242,107,221,151,67,37,2,35,179,227,197,44,54,153,109,251,14,185,80,61,202,8,29,105,78,26,100,101,48,80]))
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
def input103 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash103.message
def value103 : State := JFp_SHADigest.output JGf_TX2_M0.Hash103.result
theorem cast103_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash103.B00.input).map Fin.val=JGf_TX2_M0.Hash103.B00.input := by rfl
#print axioms cast103_0
theorem tail103 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash103.tail).map Fin.val=JGf_TX2_M0.Hash103.tail := by rfl
#print axioms tail103
theorem numeric103 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash103.message).map Fin.val=JGf_TX2_M0.Hash103.message := by
  simp only [JGf_TX2_M0.Hash103.message,JGf_TX2_M0.Hash103.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast103_0,tail103]
#print axioms numeric103
theorem hash103 : JFp_SHADigest.digest input103=value103 := by
  unfold input103 JFp_SHADigest.digest
  rw [numeric103,JGf_TX2_M0.Hash103.checked]
  rfl
#print axioms hash103
theorem address103 : BinMerkle32Path.nodeInput (children value091 (JGc_TX2_HashBytes.state [137,56,169,36,13,178,12,117,171,154,53,189,85,159,249,253,6,70,115,30,52,53,157,48,186,253,102,178,56,69,255,86]))=input103 := by rfl
#print axioms address103
def tree103 : Tree := .branch tree091 (.supplied (JGc_TX2_HashBytes.state [137,56,169,36,13,178,12,117,171,154,53,189,85,159,249,253,6,70,115,30,52,53,157,48,186,253,102,178,56,69,255,86]))
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
def input104 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash104.message
def value104 : State := JFp_SHADigest.output JGf_TX2_M0.Hash104.result
theorem cast104_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash104.B00.input).map Fin.val=JGf_TX2_M0.Hash104.B00.input := by rfl
#print axioms cast104_0
theorem tail104 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash104.tail).map Fin.val=JGf_TX2_M0.Hash104.tail := by rfl
#print axioms tail104
theorem numeric104 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash104.message).map Fin.val=JGf_TX2_M0.Hash104.message := by
  simp only [JGf_TX2_M0.Hash104.message,JGf_TX2_M0.Hash104.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast104_0,tail104]
#print axioms numeric104
theorem hash104 : JFp_SHADigest.digest input104=value104 := by
  unfold input104 JFp_SHADigest.digest
  rw [numeric104,JGf_TX2_M0.Hash104.checked]
  rfl
#print axioms hash104
theorem address104 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [61,193,117,88,169,255,60,9,25,95,251,153,70,101,229,206,193,109,171,45,58,133,46,94,72,84,104,22,201,216,143,208]) value092)=input104 := by rfl
#print axioms address104
def tree104 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [61,193,117,88,169,255,60,9,25,95,251,153,70,101,229,206,193,109,171,45,58,133,46,94,72,84,104,22,201,216,143,208])) tree092
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
def input105 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash105.message
def value105 : State := JFp_SHADigest.output JGf_TX2_M0.Hash105.result
theorem cast105_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash105.B00.input).map Fin.val=JGf_TX2_M0.Hash105.B00.input := by rfl
#print axioms cast105_0
theorem tail105 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash105.tail).map Fin.val=JGf_TX2_M0.Hash105.tail := by rfl
#print axioms tail105
theorem numeric105 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash105.message).map Fin.val=JGf_TX2_M0.Hash105.message := by
  simp only [JGf_TX2_M0.Hash105.message,JGf_TX2_M0.Hash105.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast105_0,tail105]
#print axioms numeric105
theorem hash105 : JFp_SHADigest.digest input105=value105 := by
  unfold input105 JFp_SHADigest.digest
  rw [numeric105,JGf_TX2_M0.Hash105.checked]
  rfl
#print axioms hash105
theorem address105 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [176,79,24,145,242,117,36,99,56,240,100,57,53,68,191,247,12,42,203,102,113,28,199,218,233,227,189,240,0,255,130,238]) value093)=input105 := by rfl
#print axioms address105
def tree105 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [176,79,24,145,242,117,36,99,56,240,100,57,53,68,191,247,12,42,203,102,113,28,199,218,233,227,189,240,0,255,130,238])) tree093
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
def input106 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash106.message
def value106 : State := JFp_SHADigest.output JGf_TX2_M0.Hash106.result
theorem cast106_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash106.B00.input).map Fin.val=JGf_TX2_M0.Hash106.B00.input := by rfl
#print axioms cast106_0
theorem tail106 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash106.tail).map Fin.val=JGf_TX2_M0.Hash106.tail := by rfl
#print axioms tail106
theorem numeric106 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash106.message).map Fin.val=JGf_TX2_M0.Hash106.message := by
  simp only [JGf_TX2_M0.Hash106.message,JGf_TX2_M0.Hash106.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast106_0,tail106]
#print axioms numeric106
theorem hash106 : JFp_SHADigest.digest input106=value106 := by
  unfold input106 JFp_SHADigest.digest
  rw [numeric106,JGf_TX2_M0.Hash106.checked]
  rfl
#print axioms hash106
theorem address106 : BinMerkle32Path.nodeInput (children value094 (JGc_TX2_HashBytes.state [62,233,74,174,145,136,176,68,228,195,155,226,225,182,30,103,202,248,136,209,123,22,12,84,133,124,59,28,249,153,231,21]))=input106 := by rfl
#print axioms address106
def tree106 : Tree := .branch tree094 (.supplied (JGc_TX2_HashBytes.state [62,233,74,174,145,136,176,68,228,195,155,226,225,182,30,103,202,248,136,209,123,22,12,84,133,124,59,28,249,153,231,21]))
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
def input107 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash107.message
def value107 : State := JFp_SHADigest.output JGf_TX2_M0.Hash107.result
theorem cast107_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash107.B00.input).map Fin.val=JGf_TX2_M0.Hash107.B00.input := by rfl
#print axioms cast107_0
theorem tail107 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash107.tail).map Fin.val=JGf_TX2_M0.Hash107.tail := by rfl
#print axioms tail107
theorem numeric107 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash107.message).map Fin.val=JGf_TX2_M0.Hash107.message := by
  simp only [JGf_TX2_M0.Hash107.message,JGf_TX2_M0.Hash107.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast107_0,tail107]
#print axioms numeric107
theorem hash107 : JFp_SHADigest.digest input107=value107 := by
  unfold input107 JFp_SHADigest.digest
  rw [numeric107,JGf_TX2_M0.Hash107.checked]
  rfl
#print axioms hash107
theorem address107 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [61,111,116,199,153,166,58,159,0,157,208,82,129,127,168,1,177,186,172,227,106,253,192,48,119,202,157,19,65,143,252,100]) value095)=input107 := by rfl
#print axioms address107
def tree107 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [61,111,116,199,153,166,58,159,0,157,208,82,129,127,168,1,177,186,172,227,106,253,192,48,119,202,157,19,65,143,252,100])) tree095
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
end AspisR1.JGf_TX2_M0Roots
end
