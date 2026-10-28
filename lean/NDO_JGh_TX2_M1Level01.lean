import NDO_JGh_TX2_M1Level00
import NDO_JGf_TX2_M1W007
import NDO_JGf_TX2_M1W008
import NDO_JGf_TX2_M1W009
import NDO_JGf_TX2_M1W010
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input024 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash024.message
def value024 : State := JFp_SHADigest.output JGf_TX2_M1.Hash024.result
theorem cast024_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash024.B00.input).map Fin.val=JGf_TX2_M1.Hash024.B00.input := by rfl
#print axioms cast024_0
theorem tail024 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash024.tail).map Fin.val=JGf_TX2_M1.Hash024.tail := by rfl
#print axioms tail024
theorem numeric024 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash024.message).map Fin.val=JGf_TX2_M1.Hash024.message := by
  simp only [JGf_TX2_M1.Hash024.message,JGf_TX2_M1.Hash024.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast024_0,tail024]
#print axioms numeric024
theorem hash024 : JFp_SHADigest.digest input024=value024 := by
  unfold input024 JFp_SHADigest.digest
  rw [numeric024,JGf_TX2_M1.Hash024.checked]
  rfl
#print axioms hash024
theorem address024 : BinMerkle32Path.nodeInput (children value012 (JGc_TX2_HashBytes.state [216,223,213,101,41,128,149,129,58,91,232,73,41,20,253,211,20,159,220,40,176,238,92,137,1,118,222,122,224,78,31,82]))=input024 := by rfl
#print axioms address024
def tree024 : Tree := .branch tree012 (.supplied (JGc_TX2_HashBytes.state [216,223,213,101,41,128,149,129,58,91,232,73,41,20,253,211,20,159,220,40,176,238,92,137,1,118,222,122,224,78,31,82]))
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
def input025 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash025.message
def value025 : State := JFp_SHADigest.output JGf_TX2_M1.Hash025.result
theorem cast025_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash025.B00.input).map Fin.val=JGf_TX2_M1.Hash025.B00.input := by rfl
#print axioms cast025_0
theorem tail025 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash025.tail).map Fin.val=JGf_TX2_M1.Hash025.tail := by rfl
#print axioms tail025
theorem numeric025 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash025.message).map Fin.val=JGf_TX2_M1.Hash025.message := by
  simp only [JGf_TX2_M1.Hash025.message,JGf_TX2_M1.Hash025.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast025_0,tail025]
#print axioms numeric025
theorem hash025 : JFp_SHADigest.digest input025=value025 := by
  unfold input025 JFp_SHADigest.digest
  rw [numeric025,JGf_TX2_M1.Hash025.checked]
  rfl
#print axioms hash025
theorem address025 : BinMerkle32Path.nodeInput (children value013 (JGc_TX2_HashBytes.state [30,118,171,2,169,209,190,232,106,71,105,13,157,61,242,12,6,119,20,1,187,189,73,131,74,38,48,76,86,130,142,48]))=input025 := by rfl
#print axioms address025
def tree025 : Tree := .branch tree013 (.supplied (JGc_TX2_HashBytes.state [30,118,171,2,169,209,190,232,106,71,105,13,157,61,242,12,6,119,20,1,187,189,73,131,74,38,48,76,86,130,142,48]))
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
def input026 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash026.message
def value026 : State := JFp_SHADigest.output JGf_TX2_M1.Hash026.result
theorem cast026_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash026.B00.input).map Fin.val=JGf_TX2_M1.Hash026.B00.input := by rfl
#print axioms cast026_0
theorem tail026 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash026.tail).map Fin.val=JGf_TX2_M1.Hash026.tail := by rfl
#print axioms tail026
theorem numeric026 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash026.message).map Fin.val=JGf_TX2_M1.Hash026.message := by
  simp only [JGf_TX2_M1.Hash026.message,JGf_TX2_M1.Hash026.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast026_0,tail026]
#print axioms numeric026
theorem hash026 : JFp_SHADigest.digest input026=value026 := by
  unfold input026 JFp_SHADigest.digest
  rw [numeric026,JGf_TX2_M1.Hash026.checked]
  rfl
#print axioms hash026
theorem address026 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [12,5,225,176,113,187,78,221,176,5,230,197,156,131,58,137,184,183,10,83,226,77,148,18,254,39,159,75,153,96,252,255]) value014)=input026 := by rfl
#print axioms address026
def tree026 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [12,5,225,176,113,187,78,221,176,5,230,197,156,131,58,137,184,183,10,83,226,77,148,18,254,39,159,75,153,96,252,255])) tree014
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
def input027 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash027.message
def value027 : State := JFp_SHADigest.output JGf_TX2_M1.Hash027.result
theorem cast027_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash027.B00.input).map Fin.val=JGf_TX2_M1.Hash027.B00.input := by rfl
#print axioms cast027_0
theorem tail027 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash027.tail).map Fin.val=JGf_TX2_M1.Hash027.tail := by rfl
#print axioms tail027
theorem numeric027 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash027.message).map Fin.val=JGf_TX2_M1.Hash027.message := by
  simp only [JGf_TX2_M1.Hash027.message,JGf_TX2_M1.Hash027.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast027_0,tail027]
#print axioms numeric027
theorem hash027 : JFp_SHADigest.digest input027=value027 := by
  unfold input027 JFp_SHADigest.digest
  rw [numeric027,JGf_TX2_M1.Hash027.checked]
  rfl
#print axioms hash027
theorem address027 : BinMerkle32Path.nodeInput (children value015 (JGc_TX2_HashBytes.state [125,194,82,0,44,37,60,138,181,78,216,238,8,79,227,54,31,16,252,89,102,117,160,255,76,41,106,131,16,142,89,145]))=input027 := by rfl
#print axioms address027
def tree027 : Tree := .branch tree015 (.supplied (JGc_TX2_HashBytes.state [125,194,82,0,44,37,60,138,181,78,216,238,8,79,227,54,31,16,252,89,102,117,160,255,76,41,106,131,16,142,89,145]))
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
def input028 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash028.message
def value028 : State := JFp_SHADigest.output JGf_TX2_M1.Hash028.result
theorem cast028_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash028.B00.input).map Fin.val=JGf_TX2_M1.Hash028.B00.input := by rfl
#print axioms cast028_0
theorem tail028 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash028.tail).map Fin.val=JGf_TX2_M1.Hash028.tail := by rfl
#print axioms tail028
theorem numeric028 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash028.message).map Fin.val=JGf_TX2_M1.Hash028.message := by
  simp only [JGf_TX2_M1.Hash028.message,JGf_TX2_M1.Hash028.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast028_0,tail028]
#print axioms numeric028
theorem hash028 : JFp_SHADigest.digest input028=value028 := by
  unfold input028 JFp_SHADigest.digest
  rw [numeric028,JGf_TX2_M1.Hash028.checked]
  rfl
#print axioms hash028
theorem address028 : BinMerkle32Path.nodeInput (children value016 (JGc_TX2_HashBytes.state [90,46,188,85,119,50,38,141,233,157,160,95,207,12,226,71,132,251,171,24,102,158,154,72,139,68,47,222,106,14,112,7]))=input028 := by rfl
#print axioms address028
def tree028 : Tree := .branch tree016 (.supplied (JGc_TX2_HashBytes.state [90,46,188,85,119,50,38,141,233,157,160,95,207,12,226,71,132,251,171,24,102,158,154,72,139,68,47,222,106,14,112,7]))
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
def input029 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash029.message
def value029 : State := JFp_SHADigest.output JGf_TX2_M1.Hash029.result
theorem cast029_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash029.B00.input).map Fin.val=JGf_TX2_M1.Hash029.B00.input := by rfl
#print axioms cast029_0
theorem tail029 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash029.tail).map Fin.val=JGf_TX2_M1.Hash029.tail := by rfl
#print axioms tail029
theorem numeric029 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash029.message).map Fin.val=JGf_TX2_M1.Hash029.message := by
  simp only [JGf_TX2_M1.Hash029.message,JGf_TX2_M1.Hash029.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast029_0,tail029]
#print axioms numeric029
theorem hash029 : JFp_SHADigest.digest input029=value029 := by
  unfold input029 JFp_SHADigest.digest
  rw [numeric029,JGf_TX2_M1.Hash029.checked]
  rfl
#print axioms hash029
theorem address029 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [247,176,102,31,121,87,30,85,180,105,91,242,68,89,43,86,205,119,23,8,139,200,166,179,220,55,195,26,10,13,100,20]) value017)=input029 := by rfl
#print axioms address029
def tree029 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [247,176,102,31,121,87,30,85,180,105,91,242,68,89,43,86,205,119,23,8,139,200,166,179,220,55,195,26,10,13,100,20])) tree017
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
def input030 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash030.message
def value030 : State := JFp_SHADigest.output JGf_TX2_M1.Hash030.result
theorem cast030_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash030.B00.input).map Fin.val=JGf_TX2_M1.Hash030.B00.input := by rfl
#print axioms cast030_0
theorem tail030 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash030.tail).map Fin.val=JGf_TX2_M1.Hash030.tail := by rfl
#print axioms tail030
theorem numeric030 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash030.message).map Fin.val=JGf_TX2_M1.Hash030.message := by
  simp only [JGf_TX2_M1.Hash030.message,JGf_TX2_M1.Hash030.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast030_0,tail030]
#print axioms numeric030
theorem hash030 : JFp_SHADigest.digest input030=value030 := by
  unfold input030 JFp_SHADigest.digest
  rw [numeric030,JGf_TX2_M1.Hash030.checked]
  rfl
#print axioms hash030
theorem address030 : BinMerkle32Path.nodeInput (children value018 (JGc_TX2_HashBytes.state [8,160,154,154,187,132,120,70,130,82,38,199,175,175,143,35,172,123,146,204,85,230,25,147,162,216,160,132,38,248,175,157]))=input030 := by rfl
#print axioms address030
def tree030 : Tree := .branch tree018 (.supplied (JGc_TX2_HashBytes.state [8,160,154,154,187,132,120,70,130,82,38,199,175,175,143,35,172,123,146,204,85,230,25,147,162,216,160,132,38,248,175,157]))
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
def input031 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash031.message
def value031 : State := JFp_SHADigest.output JGf_TX2_M1.Hash031.result
theorem cast031_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash031.B00.input).map Fin.val=JGf_TX2_M1.Hash031.B00.input := by rfl
#print axioms cast031_0
theorem tail031 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash031.tail).map Fin.val=JGf_TX2_M1.Hash031.tail := by rfl
#print axioms tail031
theorem numeric031 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash031.message).map Fin.val=JGf_TX2_M1.Hash031.message := by
  simp only [JGf_TX2_M1.Hash031.message,JGf_TX2_M1.Hash031.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast031_0,tail031]
#print axioms numeric031
theorem hash031 : JFp_SHADigest.digest input031=value031 := by
  unfold input031 JFp_SHADigest.digest
  rw [numeric031,JGf_TX2_M1.Hash031.checked]
  rfl
#print axioms hash031
theorem address031 : BinMerkle32Path.nodeInput (children value019 (JGc_TX2_HashBytes.state [251,119,242,89,73,15,47,154,214,157,191,152,156,55,108,140,82,114,194,108,62,5,33,70,101,112,53,45,43,85,20,98]))=input031 := by rfl
#print axioms address031
def tree031 : Tree := .branch tree019 (.supplied (JGc_TX2_HashBytes.state [251,119,242,89,73,15,47,154,214,157,191,152,156,55,108,140,82,114,194,108,62,5,33,70,101,112,53,45,43,85,20,98]))
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
def input032 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash032.message
def value032 : State := JFp_SHADigest.output JGf_TX2_M1.Hash032.result
theorem cast032_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash032.B00.input).map Fin.val=JGf_TX2_M1.Hash032.B00.input := by rfl
#print axioms cast032_0
theorem tail032 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash032.tail).map Fin.val=JGf_TX2_M1.Hash032.tail := by rfl
#print axioms tail032
theorem numeric032 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash032.message).map Fin.val=JGf_TX2_M1.Hash032.message := by
  simp only [JGf_TX2_M1.Hash032.message,JGf_TX2_M1.Hash032.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast032_0,tail032]
#print axioms numeric032
theorem hash032 : JFp_SHADigest.digest input032=value032 := by
  unfold input032 JFp_SHADigest.digest
  rw [numeric032,JGf_TX2_M1.Hash032.checked]
  rfl
#print axioms hash032
theorem address032 : BinMerkle32Path.nodeInput (children value020 (JGc_TX2_HashBytes.state [137,71,172,178,23,128,157,180,5,133,200,165,110,19,231,141,181,138,183,89,18,86,34,54,101,88,0,102,121,151,46,42]))=input032 := by rfl
#print axioms address032
def tree032 : Tree := .branch tree020 (.supplied (JGc_TX2_HashBytes.state [137,71,172,178,23,128,157,180,5,133,200,165,110,19,231,141,181,138,183,89,18,86,34,54,101,88,0,102,121,151,46,42]))
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
def input033 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash033.message
def value033 : State := JFp_SHADigest.output JGf_TX2_M1.Hash033.result
theorem cast033_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash033.B00.input).map Fin.val=JGf_TX2_M1.Hash033.B00.input := by rfl
#print axioms cast033_0
theorem tail033 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash033.tail).map Fin.val=JGf_TX2_M1.Hash033.tail := by rfl
#print axioms tail033
theorem numeric033 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash033.message).map Fin.val=JGf_TX2_M1.Hash033.message := by
  simp only [JGf_TX2_M1.Hash033.message,JGf_TX2_M1.Hash033.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast033_0,tail033]
#print axioms numeric033
theorem hash033 : JFp_SHADigest.digest input033=value033 := by
  unfold input033 JFp_SHADigest.digest
  rw [numeric033,JGf_TX2_M1.Hash033.checked]
  rfl
#print axioms hash033
theorem address033 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [70,248,22,218,176,78,97,134,73,12,54,143,44,31,207,93,211,126,173,160,98,64,79,248,10,14,144,232,237,195,66,160]) value021)=input033 := by rfl
#print axioms address033
def tree033 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [70,248,22,218,176,78,97,134,73,12,54,143,44,31,207,93,211,126,173,160,98,64,79,248,10,14,144,232,237,195,66,160])) tree021
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
def input034 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash034.message
def value034 : State := JFp_SHADigest.output JGf_TX2_M1.Hash034.result
theorem cast034_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash034.B00.input).map Fin.val=JGf_TX2_M1.Hash034.B00.input := by rfl
#print axioms cast034_0
theorem tail034 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash034.tail).map Fin.val=JGf_TX2_M1.Hash034.tail := by rfl
#print axioms tail034
theorem numeric034 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash034.message).map Fin.val=JGf_TX2_M1.Hash034.message := by
  simp only [JGf_TX2_M1.Hash034.message,JGf_TX2_M1.Hash034.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast034_0,tail034]
#print axioms numeric034
theorem hash034 : JFp_SHADigest.digest input034=value034 := by
  unfold input034 JFp_SHADigest.digest
  rw [numeric034,JGf_TX2_M1.Hash034.checked]
  rfl
#print axioms hash034
theorem address034 : BinMerkle32Path.nodeInput (children value022 (JGc_TX2_HashBytes.state [157,182,95,193,147,24,224,22,66,49,54,207,109,148,137,107,200,187,255,178,41,193,168,207,99,244,50,201,59,64,77,26]))=input034 := by rfl
#print axioms address034
def tree034 : Tree := .branch tree022 (.supplied (JGc_TX2_HashBytes.state [157,182,95,193,147,24,224,22,66,49,54,207,109,148,137,107,200,187,255,178,41,193,168,207,99,244,50,201,59,64,77,26]))
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
def input035 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash035.message
def value035 : State := JFp_SHADigest.output JGf_TX2_M1.Hash035.result
theorem cast035_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash035.B00.input).map Fin.val=JGf_TX2_M1.Hash035.B00.input := by rfl
#print axioms cast035_0
theorem tail035 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash035.tail).map Fin.val=JGf_TX2_M1.Hash035.tail := by rfl
#print axioms tail035
theorem numeric035 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash035.message).map Fin.val=JGf_TX2_M1.Hash035.message := by
  simp only [JGf_TX2_M1.Hash035.message,JGf_TX2_M1.Hash035.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast035_0,tail035]
#print axioms numeric035
theorem hash035 : JFp_SHADigest.digest input035=value035 := by
  unfold input035 JFp_SHADigest.digest
  rw [numeric035,JGf_TX2_M1.Hash035.checked]
  rfl
#print axioms hash035
theorem address035 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [52,136,53,57,243,212,114,169,248,218,155,197,72,240,65,68,127,80,247,180,209,12,50,220,99,110,46,16,25,101,33,118]) value023)=input035 := by rfl
#print axioms address035
def tree035 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [52,136,53,57,243,212,114,169,248,218,155,197,72,240,65,68,127,80,247,180,209,12,50,220,99,110,46,16,25,101,33,118])) tree023
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
end AspisR1.JGh_TX2_M1Roots
end
