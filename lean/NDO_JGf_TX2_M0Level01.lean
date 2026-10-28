import NDO_JGf_TX2_M0Level00
import NDO_JGf_TX2_M0W016
import NDO_JGf_TX2_M0W017
import NDO_JGf_TX2_M0W018
import NDO_JGf_TX2_M0W019
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGf_TX2_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input024 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash024.message
def value024 : State := JFp_SHADigest.output JGf_TX2_M0.Hash024.result
theorem cast024_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash024.B00.input).map Fin.val=JGf_TX2_M0.Hash024.B00.input := by rfl
#print axioms cast024_0
theorem tail024 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash024.tail).map Fin.val=JGf_TX2_M0.Hash024.tail := by rfl
#print axioms tail024
theorem numeric024 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash024.message).map Fin.val=JGf_TX2_M0.Hash024.message := by
  simp only [JGf_TX2_M0.Hash024.message,JGf_TX2_M0.Hash024.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast024_0,tail024]
#print axioms numeric024
theorem hash024 : JFp_SHADigest.digest input024=value024 := by
  unfold input024 JFp_SHADigest.digest
  rw [numeric024,JGf_TX2_M0.Hash024.checked]
  rfl
#print axioms hash024
theorem address024 : BinMerkle32Path.nodeInput (children value012 (JGc_TX2_HashBytes.state [179,27,252,171,11,166,183,248,37,189,110,185,10,137,245,83,180,133,37,25,31,172,162,92,252,83,154,245,120,135,141,34]))=input024 := by rfl
#print axioms address024
def tree024 : Tree := .branch tree012 (.supplied (JGc_TX2_HashBytes.state [179,27,252,171,11,166,183,248,37,189,110,185,10,137,245,83,180,133,37,25,31,172,162,92,252,83,154,245,120,135,141,34]))
theorem root024 : root JFp_SHADigest.digest tree024=value024 := by
  rw [tree024,root,root012]
  exact (congrArg JFp_SHADigest.digest address024).trans hash024
#print axioms root024
theorem shape024 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 14296=tree024 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 14296)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape012 f g inputs siblings]
  rw [unoccupied f g 1 14298 (by decide),siblings 1 (by decide) 14298 (by decide)]
  rfl
#print axioms shape024
def input025 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash025.message
def value025 : State := JFp_SHADigest.output JGf_TX2_M0.Hash025.result
theorem cast025_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash025.B00.input).map Fin.val=JGf_TX2_M0.Hash025.B00.input := by rfl
#print axioms cast025_0
theorem tail025 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash025.tail).map Fin.val=JGf_TX2_M0.Hash025.tail := by rfl
#print axioms tail025
theorem numeric025 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash025.message).map Fin.val=JGf_TX2_M0.Hash025.message := by
  simp only [JGf_TX2_M0.Hash025.message,JGf_TX2_M0.Hash025.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast025_0,tail025]
#print axioms numeric025
theorem hash025 : JFp_SHADigest.digest input025=value025 := by
  unfold input025 JFp_SHADigest.digest
  rw [numeric025,JGf_TX2_M0.Hash025.checked]
  rfl
#print axioms hash025
theorem address025 : BinMerkle32Path.nodeInput (children value013 (JGc_TX2_HashBytes.state [104,206,110,127,150,245,78,189,227,51,247,160,112,1,161,175,17,228,5,139,241,207,127,29,117,131,201,48,48,99,128,232]))=input025 := by rfl
#print axioms address025
def tree025 : Tree := .branch tree013 (.supplied (JGc_TX2_HashBytes.state [104,206,110,127,150,245,78,189,227,51,247,160,112,1,161,175,17,228,5,139,241,207,127,29,117,131,201,48,48,99,128,232]))
theorem root025 : root JFp_SHADigest.digest tree025=value025 := by
  rw [tree025,root,root013]
  exact (congrArg JFp_SHADigest.digest address025).trans hash025
#print axioms root025
theorem shape025 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 21248=tree025 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 21248)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape013 f g inputs siblings]
  rw [unoccupied f g 1 21250 (by decide),siblings 1 (by decide) 21250 (by decide)]
  rfl
#print axioms shape025
def input026 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash026.message
def value026 : State := JFp_SHADigest.output JGf_TX2_M0.Hash026.result
theorem cast026_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash026.B00.input).map Fin.val=JGf_TX2_M0.Hash026.B00.input := by rfl
#print axioms cast026_0
theorem tail026 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash026.tail).map Fin.val=JGf_TX2_M0.Hash026.tail := by rfl
#print axioms tail026
theorem numeric026 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash026.message).map Fin.val=JGf_TX2_M0.Hash026.message := by
  simp only [JGf_TX2_M0.Hash026.message,JGf_TX2_M0.Hash026.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast026_0,tail026]
#print axioms numeric026
theorem hash026 : JFp_SHADigest.digest input026=value026 := by
  unfold input026 JFp_SHADigest.digest
  rw [numeric026,JGf_TX2_M0.Hash026.checked]
  rfl
#print axioms hash026
theorem address026 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [195,203,174,12,64,241,197,103,133,148,198,8,162,200,252,46,244,216,134,149,204,46,189,22,136,8,11,12,229,251,132,70]) value014)=input026 := by rfl
#print axioms address026
def tree026 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [195,203,174,12,64,241,197,103,133,148,198,8,162,200,252,46,244,216,134,149,204,46,189,22,136,8,11,12,229,251,132,70])) tree014
theorem root026 : root JFp_SHADigest.digest tree026=value026 := by
  rw [tree026,root,root014]
  exact (congrArg JFp_SHADigest.digest address026).trans hash026
#print axioms root026
theorem shape026 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 42156=tree026 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 42156)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 42156 (by decide),siblings 1 (by decide) 42156 (by decide)]
  rw [shape014 f g inputs siblings]
  rfl
#print axioms shape026
def input027 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash027.message
def value027 : State := JFp_SHADigest.output JGf_TX2_M0.Hash027.result
theorem cast027_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash027.B00.input).map Fin.val=JGf_TX2_M0.Hash027.B00.input := by rfl
#print axioms cast027_0
theorem tail027 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash027.tail).map Fin.val=JGf_TX2_M0.Hash027.tail := by rfl
#print axioms tail027
theorem numeric027 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash027.message).map Fin.val=JGf_TX2_M0.Hash027.message := by
  simp only [JGf_TX2_M0.Hash027.message,JGf_TX2_M0.Hash027.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast027_0,tail027]
#print axioms numeric027
theorem hash027 : JFp_SHADigest.digest input027=value027 := by
  unfold input027 JFp_SHADigest.digest
  rw [numeric027,JGf_TX2_M0.Hash027.checked]
  rfl
#print axioms hash027
theorem address027 : BinMerkle32Path.nodeInput (children value015 (JGc_TX2_HashBytes.state [141,192,4,80,242,25,110,251,105,93,220,133,123,246,154,67,163,105,104,177,156,222,239,0,96,249,215,228,126,144,22,241]))=input027 := by rfl
#print axioms address027
def tree027 : Tree := .branch tree015 (.supplied (JGc_TX2_HashBytes.state [141,192,4,80,242,25,110,251,105,93,220,133,123,246,154,67,163,105,104,177,156,222,239,0,96,249,215,228,126,144,22,241]))
theorem root027 : root JFp_SHADigest.digest tree027=value027 := by
  rw [tree027,root,root015]
  exact (congrArg JFp_SHADigest.digest address027).trans hash027
#print axioms root027
theorem shape027 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 55376=tree027 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 55376)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape015 f g inputs siblings]
  rw [unoccupied f g 1 55378 (by decide),siblings 1 (by decide) 55378 (by decide)]
  rfl
#print axioms shape027
def input028 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash028.message
def value028 : State := JFp_SHADigest.output JGf_TX2_M0.Hash028.result
theorem cast028_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash028.B00.input).map Fin.val=JGf_TX2_M0.Hash028.B00.input := by rfl
#print axioms cast028_0
theorem tail028 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash028.tail).map Fin.val=JGf_TX2_M0.Hash028.tail := by rfl
#print axioms tail028
theorem numeric028 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash028.message).map Fin.val=JGf_TX2_M0.Hash028.message := by
  simp only [JGf_TX2_M0.Hash028.message,JGf_TX2_M0.Hash028.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast028_0,tail028]
#print axioms numeric028
theorem hash028 : JFp_SHADigest.digest input028=value028 := by
  unfold input028 JFp_SHADigest.digest
  rw [numeric028,JGf_TX2_M0.Hash028.checked]
  rfl
#print axioms hash028
theorem address028 : BinMerkle32Path.nodeInput (children value016 (JGc_TX2_HashBytes.state [134,141,131,210,190,5,147,113,45,178,5,235,175,101,144,118,172,89,45,245,9,180,106,8,155,37,172,253,128,48,12,83]))=input028 := by rfl
#print axioms address028
def tree028 : Tree := .branch tree016 (.supplied (JGc_TX2_HashBytes.state [134,141,131,210,190,5,147,113,45,178,5,235,175,101,144,118,172,89,45,245,9,180,106,8,155,37,172,253,128,48,12,83]))
theorem root028 : root JFp_SHADigest.digest tree028=value028 := by
  rw [tree028,root,root016]
  exact (congrArg JFp_SHADigest.digest address028).trans hash028
#print axioms root028
theorem shape028 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 63860=tree028 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 63860)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape016 f g inputs siblings]
  rw [unoccupied f g 1 63862 (by decide),siblings 1 (by decide) 63862 (by decide)]
  rfl
#print axioms shape028
def input029 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash029.message
def value029 : State := JFp_SHADigest.output JGf_TX2_M0.Hash029.result
theorem cast029_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash029.B00.input).map Fin.val=JGf_TX2_M0.Hash029.B00.input := by rfl
#print axioms cast029_0
theorem tail029 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash029.tail).map Fin.val=JGf_TX2_M0.Hash029.tail := by rfl
#print axioms tail029
theorem numeric029 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash029.message).map Fin.val=JGf_TX2_M0.Hash029.message := by
  simp only [JGf_TX2_M0.Hash029.message,JGf_TX2_M0.Hash029.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast029_0,tail029]
#print axioms numeric029
theorem hash029 : JFp_SHADigest.digest input029=value029 := by
  unfold input029 JFp_SHADigest.digest
  rw [numeric029,JGf_TX2_M0.Hash029.checked]
  rfl
#print axioms hash029
theorem address029 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [56,110,188,136,90,151,201,246,165,173,217,244,96,247,207,116,182,10,37,45,192,246,192,56,136,225,252,97,146,229,88,128]) value017)=input029 := by rfl
#print axioms address029
def tree029 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [56,110,188,136,90,151,201,246,165,173,217,244,96,247,207,116,182,10,37,45,192,246,192,56,136,225,252,97,146,229,88,128])) tree017
theorem root029 : root JFp_SHADigest.digest tree029=value029 := by
  rw [tree029,root,root017]
  exact (congrArg JFp_SHADigest.digest address029).trans hash029
#print axioms root029
theorem shape029 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 132352=tree029 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 132352)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 132352 (by decide),siblings 1 (by decide) 132352 (by decide)]
  rw [shape017 f g inputs siblings]
  rfl
#print axioms shape029
def input030 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash030.message
def value030 : State := JFp_SHADigest.output JGf_TX2_M0.Hash030.result
theorem cast030_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash030.B00.input).map Fin.val=JGf_TX2_M0.Hash030.B00.input := by rfl
#print axioms cast030_0
theorem tail030 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash030.tail).map Fin.val=JGf_TX2_M0.Hash030.tail := by rfl
#print axioms tail030
theorem numeric030 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash030.message).map Fin.val=JGf_TX2_M0.Hash030.message := by
  simp only [JGf_TX2_M0.Hash030.message,JGf_TX2_M0.Hash030.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast030_0,tail030]
#print axioms numeric030
theorem hash030 : JFp_SHADigest.digest input030=value030 := by
  unfold input030 JFp_SHADigest.digest
  rw [numeric030,JGf_TX2_M0.Hash030.checked]
  rfl
#print axioms hash030
theorem address030 : BinMerkle32Path.nodeInput (children value018 (JGc_TX2_HashBytes.state [131,187,242,154,115,45,153,67,208,61,186,81,223,48,114,191,33,115,205,184,182,249,26,32,156,199,99,225,160,234,26,128]))=input030 := by rfl
#print axioms address030
def tree030 : Tree := .branch tree018 (.supplied (JGc_TX2_HashBytes.state [131,187,242,154,115,45,153,67,208,61,186,81,223,48,114,191,33,115,205,184,182,249,26,32,156,199,99,225,160,234,26,128]))
theorem root030 : root JFp_SHADigest.digest tree030=value030 := by
  rw [tree030,root,root018]
  exact (congrArg JFp_SHADigest.digest address030).trans hash030
#print axioms root030
theorem shape030 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 149624=tree030 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 149624)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape018 f g inputs siblings]
  rw [unoccupied f g 1 149626 (by decide),siblings 1 (by decide) 149626 (by decide)]
  rfl
#print axioms shape030
def input031 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash031.message
def value031 : State := JFp_SHADigest.output JGf_TX2_M0.Hash031.result
theorem cast031_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash031.B00.input).map Fin.val=JGf_TX2_M0.Hash031.B00.input := by rfl
#print axioms cast031_0
theorem tail031 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash031.tail).map Fin.val=JGf_TX2_M0.Hash031.tail := by rfl
#print axioms tail031
theorem numeric031 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash031.message).map Fin.val=JGf_TX2_M0.Hash031.message := by
  simp only [JGf_TX2_M0.Hash031.message,JGf_TX2_M0.Hash031.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast031_0,tail031]
#print axioms numeric031
theorem hash031 : JFp_SHADigest.digest input031=value031 := by
  unfold input031 JFp_SHADigest.digest
  rw [numeric031,JGf_TX2_M0.Hash031.checked]
  rfl
#print axioms hash031
theorem address031 : BinMerkle32Path.nodeInput (children value019 (JGc_TX2_HashBytes.state [57,5,106,8,216,101,250,171,148,139,150,111,118,189,150,152,153,254,246,65,37,70,172,181,98,205,196,230,130,233,32,161]))=input031 := by rfl
#print axioms address031
def tree031 : Tree := .branch tree019 (.supplied (JGc_TX2_HashBytes.state [57,5,106,8,216,101,250,171,148,139,150,111,118,189,150,152,153,254,246,65,37,70,172,181,98,205,196,230,130,233,32,161]))
theorem root031 : root JFp_SHADigest.digest tree031=value031 := by
  rw [tree031,root,root019]
  exact (congrArg JFp_SHADigest.digest address031).trans hash031
#print axioms root031
theorem shape031 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 166164=tree031 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 166164)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape019 f g inputs siblings]
  rw [unoccupied f g 1 166166 (by decide),siblings 1 (by decide) 166166 (by decide)]
  rfl
#print axioms shape031
def input032 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash032.message
def value032 : State := JFp_SHADigest.output JGf_TX2_M0.Hash032.result
theorem cast032_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash032.B00.input).map Fin.val=JGf_TX2_M0.Hash032.B00.input := by rfl
#print axioms cast032_0
theorem tail032 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash032.tail).map Fin.val=JGf_TX2_M0.Hash032.tail := by rfl
#print axioms tail032
theorem numeric032 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash032.message).map Fin.val=JGf_TX2_M0.Hash032.message := by
  simp only [JGf_TX2_M0.Hash032.message,JGf_TX2_M0.Hash032.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast032_0,tail032]
#print axioms numeric032
theorem hash032 : JFp_SHADigest.digest input032=value032 := by
  unfold input032 JFp_SHADigest.digest
  rw [numeric032,JGf_TX2_M0.Hash032.checked]
  rfl
#print axioms hash032
theorem address032 : BinMerkle32Path.nodeInput (children value020 (JGc_TX2_HashBytes.state [27,194,72,184,29,77,142,193,158,249,7,229,77,164,44,254,52,194,135,151,150,186,181,54,122,219,166,195,116,111,239,146]))=input032 := by rfl
#print axioms address032
def tree032 : Tree := .branch tree020 (.supplied (JGc_TX2_HashBytes.state [27,194,72,184,29,77,142,193,158,249,7,229,77,164,44,254,52,194,135,151,150,186,181,54,122,219,166,195,116,111,239,146]))
theorem root032 : root JFp_SHADigest.digest tree032=value032 := by
  rw [tree032,root,root020]
  exact (congrArg JFp_SHADigest.digest address032).trans hash032
#print axioms root032
theorem shape032 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 178080=tree032 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 178080)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape020 f g inputs siblings]
  rw [unoccupied f g 1 178082 (by decide),siblings 1 (by decide) 178082 (by decide)]
  rfl
#print axioms shape032
def input033 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash033.message
def value033 : State := JFp_SHADigest.output JGf_TX2_M0.Hash033.result
theorem cast033_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash033.B00.input).map Fin.val=JGf_TX2_M0.Hash033.B00.input := by rfl
#print axioms cast033_0
theorem tail033 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash033.tail).map Fin.val=JGf_TX2_M0.Hash033.tail := by rfl
#print axioms tail033
theorem numeric033 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash033.message).map Fin.val=JGf_TX2_M0.Hash033.message := by
  simp only [JGf_TX2_M0.Hash033.message,JGf_TX2_M0.Hash033.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast033_0,tail033]
#print axioms numeric033
theorem hash033 : JFp_SHADigest.digest input033=value033 := by
  unfold input033 JFp_SHADigest.digest
  rw [numeric033,JGf_TX2_M0.Hash033.checked]
  rfl
#print axioms hash033
theorem address033 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [10,138,97,167,83,116,192,234,146,44,6,5,111,85,6,205,75,22,120,61,158,109,241,142,231,223,127,164,99,85,154,113]) value021)=input033 := by rfl
#print axioms address033
def tree033 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [10,138,97,167,83,116,192,234,146,44,6,5,111,85,6,205,75,22,120,61,158,109,241,142,231,223,127,164,99,85,154,113])) tree021
theorem root033 : root JFp_SHADigest.digest tree033=value033 := by
  rw [tree033,root,root021]
  exact (congrArg JFp_SHADigest.digest address033).trans hash033
#print axioms root033
theorem shape033 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 179620=tree033 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 179620)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 179620 (by decide),siblings 1 (by decide) 179620 (by decide)]
  rw [shape021 f g inputs siblings]
  rfl
#print axioms shape033
def input034 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash034.message
def value034 : State := JFp_SHADigest.output JGf_TX2_M0.Hash034.result
theorem cast034_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash034.B00.input).map Fin.val=JGf_TX2_M0.Hash034.B00.input := by rfl
#print axioms cast034_0
theorem tail034 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash034.tail).map Fin.val=JGf_TX2_M0.Hash034.tail := by rfl
#print axioms tail034
theorem numeric034 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash034.message).map Fin.val=JGf_TX2_M0.Hash034.message := by
  simp only [JGf_TX2_M0.Hash034.message,JGf_TX2_M0.Hash034.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast034_0,tail034]
#print axioms numeric034
theorem hash034 : JFp_SHADigest.digest input034=value034 := by
  unfold input034 JFp_SHADigest.digest
  rw [numeric034,JGf_TX2_M0.Hash034.checked]
  rfl
#print axioms hash034
theorem address034 : BinMerkle32Path.nodeInput (children value022 (JGc_TX2_HashBytes.state [211,136,217,93,243,43,26,207,45,65,20,239,189,52,171,23,64,45,177,122,99,241,214,160,94,224,15,69,1,138,38,206]))=input034 := by rfl
#print axioms address034
def tree034 : Tree := .branch tree022 (.supplied (JGc_TX2_HashBytes.state [211,136,217,93,243,43,26,207,45,65,20,239,189,52,171,23,64,45,177,122,99,241,214,160,94,224,15,69,1,138,38,206]))
theorem root034 : root JFp_SHADigest.digest tree034=value034 := by
  rw [tree034,root,root022]
  exact (congrArg JFp_SHADigest.digest address034).trans hash034
#print axioms root034
theorem shape034 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 185636=tree034 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 185636)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape022 f g inputs siblings]
  rw [unoccupied f g 1 185638 (by decide),siblings 1 (by decide) 185638 (by decide)]
  rfl
#print axioms shape034
def input035 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash035.message
def value035 : State := JFp_SHADigest.output JGf_TX2_M0.Hash035.result
theorem cast035_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash035.B00.input).map Fin.val=JGf_TX2_M0.Hash035.B00.input := by rfl
#print axioms cast035_0
theorem tail035 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash035.tail).map Fin.val=JGf_TX2_M0.Hash035.tail := by rfl
#print axioms tail035
theorem numeric035 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash035.message).map Fin.val=JGf_TX2_M0.Hash035.message := by
  simp only [JGf_TX2_M0.Hash035.message,JGf_TX2_M0.Hash035.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast035_0,tail035]
#print axioms numeric035
theorem hash035 : JFp_SHADigest.digest input035=value035 := by
  unfold input035 JFp_SHADigest.digest
  rw [numeric035,JGf_TX2_M0.Hash035.checked]
  rfl
#print axioms hash035
theorem address035 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [20,91,19,186,51,102,128,96,202,101,240,53,190,132,106,215,19,60,128,150,173,68,205,12,89,93,217,146,161,93,166,98]) value023)=input035 := by rfl
#print axioms address035
def tree035 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [20,91,19,186,51,102,128,96,202,101,240,53,190,132,106,215,19,60,128,150,173,68,205,12,89,93,217,146,161,93,166,98])) tree023
theorem root035 : root JFp_SHADigest.digest tree035=value035 := by
  rw [tree035,root,root023]
  exact (congrArg JFp_SHADigest.digest address035).trans hash035
#print axioms root035
theorem shape035 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 218092=tree035 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 218092)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 218092 (by decide),siblings 1 (by decide) 218092 (by decide)]
  rw [shape023 f g inputs siblings]
  rfl
#print axioms shape035
end AspisR1.JGf_TX2_M0Roots
end
