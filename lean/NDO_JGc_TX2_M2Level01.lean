import NDO_JGc_TX2_M2Level00
import NDO_JGc_TX2_M2H024
import NDO_JGc_TX2_M2H028
import NDO_JGc_TX2_M2H032
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input024 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash024.message
def value024 : State := JFp_SHADigest.output JGc_TX2_M2.Hash024.result
theorem cast024_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash024.B00.input).map Fin.val=JGc_TX2_M2.Hash024.B00.input := by rfl
#print axioms cast024_0
theorem tail024 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash024.tail).map Fin.val=JGc_TX2_M2.Hash024.tail := by rfl
#print axioms tail024
theorem numeric024 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash024.message).map Fin.val=JGc_TX2_M2.Hash024.message := by
  simp only [JGc_TX2_M2.Hash024.message,JGc_TX2_M2.Hash024.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast024_0,tail024]
#print axioms numeric024
theorem hash024 : JFp_SHADigest.digest input024=value024 := by
  unfold input024 JFp_SHADigest.digest
  rw [numeric024,JGc_TX2_M2.Hash024.checked]
  rfl
#print axioms hash024
theorem address024 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [105,35,33,25,119,208,99,122,241,83,137,249,1,36,19,102,132,128,84,40,134,172,5,189,221,115,114,23,3,37,54,158]) value012)=input024 := by rfl
#print axioms address024
def tree024 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [105,35,33,25,119,208,99,122,241,83,137,249,1,36,19,102,132,128,84,40,134,172,5,189,221,115,114,23,3,37,54,158])) tree012
theorem root024 : root JFp_SHADigest.digest tree024=value024 := by
  rw [tree024,root,root012]
  exact (congrArg JFp_SHADigest.digest address024).trans hash024
#print axioms root024
theorem shape024 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 3572=tree024 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 3572)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 3572 (by decide),siblings 1 (by decide) 3572 (by decide)]
  rw [shape012 f g inputs siblings]
  rfl
#print axioms shape024
def input025 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash025.message
def value025 : State := JFp_SHADigest.output JGc_TX2_M2.Hash025.result
theorem cast025_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash025.B00.input).map Fin.val=JGc_TX2_M2.Hash025.B00.input := by rfl
#print axioms cast025_0
theorem tail025 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash025.tail).map Fin.val=JGc_TX2_M2.Hash025.tail := by rfl
#print axioms tail025
theorem numeric025 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash025.message).map Fin.val=JGc_TX2_M2.Hash025.message := by
  simp only [JGc_TX2_M2.Hash025.message,JGc_TX2_M2.Hash025.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast025_0,tail025]
#print axioms numeric025
theorem hash025 : JFp_SHADigest.digest input025=value025 := by
  unfold input025 JFp_SHADigest.digest
  rw [numeric025,JGc_TX2_M2.Hash025.checked]
  rfl
#print axioms hash025
theorem address025 : BinMerkle32Path.nodeInput (children value013 (JGc_TX2_HashBytes.state [218,176,44,113,131,180,132,20,212,56,12,158,193,73,217,66,162,155,35,24,129,247,189,168,103,224,224,11,223,60,137,215]))=input025 := by rfl
#print axioms address025
def tree025 : Tree := .branch tree013 (.supplied (JGc_TX2_HashBytes.state [218,176,44,113,131,180,132,20,212,56,12,158,193,73,217,66,162,155,35,24,129,247,189,168,103,224,224,11,223,60,137,215]))
theorem root025 : root JFp_SHADigest.digest tree025=value025 := by
  rw [tree025,root,root013]
  exact (congrArg JFp_SHADigest.digest address025).trans hash025
#print axioms root025
theorem shape025 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 5312=tree025 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 5312)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape013 f g inputs siblings]
  rw [unoccupied f g 1 5314 (by decide),siblings 1 (by decide) 5314 (by decide)]
  rfl
#print axioms shape025
def input026 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash026.message
def value026 : State := JFp_SHADigest.output JGc_TX2_M2.Hash026.result
theorem cast026_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash026.B00.input).map Fin.val=JGc_TX2_M2.Hash026.B00.input := by rfl
#print axioms cast026_0
theorem tail026 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash026.tail).map Fin.val=JGc_TX2_M2.Hash026.tail := by rfl
#print axioms tail026
theorem numeric026 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash026.message).map Fin.val=JGc_TX2_M2.Hash026.message := by
  simp only [JGc_TX2_M2.Hash026.message,JGc_TX2_M2.Hash026.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast026_0,tail026]
#print axioms numeric026
theorem hash026 : JFp_SHADigest.digest input026=value026 := by
  unfold input026 JFp_SHADigest.digest
  rw [numeric026,JGc_TX2_M2.Hash026.checked]
  rfl
#print axioms hash026
theorem address026 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [132,255,46,148,119,0,171,127,165,204,158,201,240,96,58,157,230,188,33,239,24,211,136,255,49,109,40,245,11,18,140,22]) value014)=input026 := by rfl
#print axioms address026
def tree026 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [132,255,46,148,119,0,171,127,165,204,158,201,240,96,58,157,230,188,33,239,24,211,136,255,49,109,40,245,11,18,140,22])) tree014
theorem root026 : root JFp_SHADigest.digest tree026=value026 := by
  rw [tree026,root,root014]
  exact (congrArg JFp_SHADigest.digest address026).trans hash026
#print axioms root026
theorem shape026 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 10536=tree026 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 10536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 10536 (by decide),siblings 1 (by decide) 10536 (by decide)]
  rw [shape014 f g inputs siblings]
  rfl
#print axioms shape026
def input027 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash027.message
def value027 : State := JFp_SHADigest.output JGc_TX2_M2.Hash027.result
theorem cast027_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash027.B00.input).map Fin.val=JGc_TX2_M2.Hash027.B00.input := by rfl
#print axioms cast027_0
theorem tail027 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash027.tail).map Fin.val=JGc_TX2_M2.Hash027.tail := by rfl
#print axioms tail027
theorem numeric027 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash027.message).map Fin.val=JGc_TX2_M2.Hash027.message := by
  simp only [JGc_TX2_M2.Hash027.message,JGc_TX2_M2.Hash027.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast027_0,tail027]
#print axioms numeric027
theorem hash027 : JFp_SHADigest.digest input027=value027 := by
  unfold input027 JFp_SHADigest.digest
  rw [numeric027,JGc_TX2_M2.Hash027.checked]
  rfl
#print axioms hash027
theorem address027 : BinMerkle32Path.nodeInput (children value015 (JGc_TX2_HashBytes.state [85,215,10,4,191,215,234,187,84,233,203,164,88,121,188,115,84,133,133,163,100,71,185,145,61,125,215,5,244,103,15,220]))=input027 := by rfl
#print axioms address027
def tree027 : Tree := .branch tree015 (.supplied (JGc_TX2_HashBytes.state [85,215,10,4,191,215,234,187,84,233,203,164,88,121,188,115,84,133,133,163,100,71,185,145,61,125,215,5,244,103,15,220]))
theorem root027 : root JFp_SHADigest.digest tree027=value027 := by
  rw [tree027,root,root015]
  exact (congrArg JFp_SHADigest.digest address027).trans hash027
#print axioms root027
theorem shape027 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 13844=tree027 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 13844)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape015 f g inputs siblings]
  rw [unoccupied f g 1 13846 (by decide),siblings 1 (by decide) 13846 (by decide)]
  rfl
#print axioms shape027
def input028 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash028.message
def value028 : State := JFp_SHADigest.output JGc_TX2_M2.Hash028.result
theorem cast028_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash028.B00.input).map Fin.val=JGc_TX2_M2.Hash028.B00.input := by rfl
#print axioms cast028_0
theorem tail028 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash028.tail).map Fin.val=JGc_TX2_M2.Hash028.tail := by rfl
#print axioms tail028
theorem numeric028 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash028.message).map Fin.val=JGc_TX2_M2.Hash028.message := by
  simp only [JGc_TX2_M2.Hash028.message,JGc_TX2_M2.Hash028.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast028_0,tail028]
#print axioms numeric028
theorem hash028 : JFp_SHADigest.digest input028=value028 := by
  unfold input028 JFp_SHADigest.digest
  rw [numeric028,JGc_TX2_M2.Hash028.checked]
  rfl
#print axioms hash028
theorem address028 : BinMerkle32Path.nodeInput (children value016 (JGc_TX2_HashBytes.state [233,12,76,182,55,86,131,28,134,104,64,245,5,248,85,26,112,218,240,222,87,201,63,197,143,161,1,205,152,1,87,146]))=input028 := by rfl
#print axioms address028
def tree028 : Tree := .branch tree016 (.supplied (JGc_TX2_HashBytes.state [233,12,76,182,55,86,131,28,134,104,64,245,5,248,85,26,112,218,240,222,87,201,63,197,143,161,1,205,152,1,87,146]))
theorem root028 : root JFp_SHADigest.digest tree028=value028 := by
  rw [tree028,root,root016]
  exact (congrArg JFp_SHADigest.digest address028).trans hash028
#print axioms root028
theorem shape028 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 15964=tree028 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 15964)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape016 f g inputs siblings]
  rw [unoccupied f g 1 15966 (by decide),siblings 1 (by decide) 15966 (by decide)]
  rfl
#print axioms shape028
def input029 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash029.message
def value029 : State := JFp_SHADigest.output JGc_TX2_M2.Hash029.result
theorem cast029_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash029.B00.input).map Fin.val=JGc_TX2_M2.Hash029.B00.input := by rfl
#print axioms cast029_0
theorem tail029 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash029.tail).map Fin.val=JGc_TX2_M2.Hash029.tail := by rfl
#print axioms tail029
theorem numeric029 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash029.message).map Fin.val=JGc_TX2_M2.Hash029.message := by
  simp only [JGc_TX2_M2.Hash029.message,JGc_TX2_M2.Hash029.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast029_0,tail029]
#print axioms numeric029
theorem hash029 : JFp_SHADigest.digest input029=value029 := by
  unfold input029 JFp_SHADigest.digest
  rw [numeric029,JGc_TX2_M2.Hash029.checked]
  rfl
#print axioms hash029
theorem address029 : BinMerkle32Path.nodeInput (children value017 (JGc_TX2_HashBytes.state [41,123,146,98,74,41,194,48,129,190,154,231,228,83,190,152,113,0,84,3,82,78,64,108,73,103,48,204,39,90,128,180]))=input029 := by rfl
#print axioms address029
def tree029 : Tree := .branch tree017 (.supplied (JGc_TX2_HashBytes.state [41,123,146,98,74,41,194,48,129,190,154,231,228,83,190,152,113,0,84,3,82,78,64,108,73,103,48,204,39,90,128,180]))
theorem root029 : root JFp_SHADigest.digest tree029=value029 := by
  rw [tree029,root,root017]
  exact (congrArg JFp_SHADigest.digest address029).trans hash029
#print axioms root029
theorem shape029 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 33088=tree029 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 33088)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape017 f g inputs siblings]
  rw [unoccupied f g 1 33090 (by decide),siblings 1 (by decide) 33090 (by decide)]
  rfl
#print axioms shape029
def input030 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash030.message
def value030 : State := JFp_SHADigest.output JGc_TX2_M2.Hash030.result
theorem cast030_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash030.B00.input).map Fin.val=JGc_TX2_M2.Hash030.B00.input := by rfl
#print axioms cast030_0
theorem tail030 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash030.tail).map Fin.val=JGc_TX2_M2.Hash030.tail := by rfl
#print axioms tail030
theorem numeric030 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash030.message).map Fin.val=JGc_TX2_M2.Hash030.message := by
  simp only [JGc_TX2_M2.Hash030.message,JGc_TX2_M2.Hash030.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast030_0,tail030]
#print axioms numeric030
theorem hash030 : JFp_SHADigest.digest input030=value030 := by
  unfold input030 JFp_SHADigest.digest
  rw [numeric030,JGc_TX2_M2.Hash030.checked]
  rfl
#print axioms hash030
theorem address030 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [197,218,140,229,49,134,37,57,194,185,240,206,239,92,48,217,156,44,145,139,116,206,138,85,253,224,195,206,148,79,137,249]) value018)=input030 := by rfl
#print axioms address030
def tree030 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [197,218,140,229,49,134,37,57,194,185,240,206,239,92,48,217,156,44,145,139,116,206,138,85,253,224,195,206,148,79,137,249])) tree018
theorem root030 : root JFp_SHADigest.digest tree030=value030 := by
  rw [tree030,root,root018]
  exact (congrArg JFp_SHADigest.digest address030).trans hash030
#print axioms root030
theorem shape030 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 37404=tree030 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 37404)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 37404 (by decide),siblings 1 (by decide) 37404 (by decide)]
  rw [shape018 f g inputs siblings]
  rfl
#print axioms shape030
def input031 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash031.message
def value031 : State := JFp_SHADigest.output JGc_TX2_M2.Hash031.result
theorem cast031_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash031.B00.input).map Fin.val=JGc_TX2_M2.Hash031.B00.input := by rfl
#print axioms cast031_0
theorem tail031 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash031.tail).map Fin.val=JGc_TX2_M2.Hash031.tail := by rfl
#print axioms tail031
theorem numeric031 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash031.message).map Fin.val=JGc_TX2_M2.Hash031.message := by
  simp only [JGc_TX2_M2.Hash031.message,JGc_TX2_M2.Hash031.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast031_0,tail031]
#print axioms numeric031
theorem hash031 : JFp_SHADigest.digest input031=value031 := by
  unfold input031 JFp_SHADigest.digest
  rw [numeric031,JGc_TX2_M2.Hash031.checked]
  rfl
#print axioms hash031
theorem address031 : BinMerkle32Path.nodeInput (children value019 (JGc_TX2_HashBytes.state [178,0,87,176,242,109,72,47,236,219,104,45,218,234,49,125,20,64,147,191,238,235,142,180,71,229,234,13,235,62,31,222]))=input031 := by rfl
#print axioms address031
def tree031 : Tree := .branch tree019 (.supplied (JGc_TX2_HashBytes.state [178,0,87,176,242,109,72,47,236,219,104,45,218,234,49,125,20,64,147,191,238,235,142,180,71,229,234,13,235,62,31,222]))
theorem root031 : root JFp_SHADigest.digest tree031=value031 := by
  rw [tree031,root,root019]
  exact (congrArg JFp_SHADigest.digest address031).trans hash031
#print axioms root031
theorem shape031 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 41540=tree031 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 41540)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape019 f g inputs siblings]
  rw [unoccupied f g 1 41542 (by decide),siblings 1 (by decide) 41542 (by decide)]
  rfl
#print axioms shape031
def input032 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash032.message
def value032 : State := JFp_SHADigest.output JGc_TX2_M2.Hash032.result
theorem cast032_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash032.B00.input).map Fin.val=JGc_TX2_M2.Hash032.B00.input := by rfl
#print axioms cast032_0
theorem tail032 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash032.tail).map Fin.val=JGc_TX2_M2.Hash032.tail := by rfl
#print axioms tail032
theorem numeric032 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash032.message).map Fin.val=JGc_TX2_M2.Hash032.message := by
  simp only [JGc_TX2_M2.Hash032.message,JGc_TX2_M2.Hash032.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast032_0,tail032]
#print axioms numeric032
theorem hash032 : JFp_SHADigest.digest input032=value032 := by
  unfold input032 JFp_SHADigest.digest
  rw [numeric032,JGc_TX2_M2.Hash032.checked]
  rfl
#print axioms hash032
theorem address032 : BinMerkle32Path.nodeInput (children value020 (JGc_TX2_HashBytes.state [83,160,147,101,157,27,33,159,100,90,115,0,45,96,6,225,224,46,153,6,49,103,54,140,125,129,85,191,42,2,132,189]))=input032 := by rfl
#print axioms address032
def tree032 : Tree := .branch tree020 (.supplied (JGc_TX2_HashBytes.state [83,160,147,101,157,27,33,159,100,90,115,0,45,96,6,225,224,46,153,6,49,103,54,140,125,129,85,191,42,2,132,189]))
theorem root032 : root JFp_SHADigest.digest tree032=value032 := by
  rw [tree032,root,root020]
  exact (congrArg JFp_SHADigest.digest address032).trans hash032
#print axioms root032
theorem shape032 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 44520=tree032 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 44520)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape020 f g inputs siblings]
  rw [unoccupied f g 1 44522 (by decide),siblings 1 (by decide) 44522 (by decide)]
  rfl
#print axioms shape032
def input033 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash033.message
def value033 : State := JFp_SHADigest.output JGc_TX2_M2.Hash033.result
theorem cast033_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash033.B00.input).map Fin.val=JGc_TX2_M2.Hash033.B00.input := by rfl
#print axioms cast033_0
theorem tail033 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash033.tail).map Fin.val=JGc_TX2_M2.Hash033.tail := by rfl
#print axioms tail033
theorem numeric033 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash033.message).map Fin.val=JGc_TX2_M2.Hash033.message := by
  simp only [JGc_TX2_M2.Hash033.message,JGc_TX2_M2.Hash033.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast033_0,tail033]
#print axioms numeric033
theorem hash033 : JFp_SHADigest.digest input033=value033 := by
  unfold input033 JFp_SHADigest.digest
  rw [numeric033,JGc_TX2_M2.Hash033.checked]
  rfl
#print axioms hash033
theorem address033 : BinMerkle32Path.nodeInput (children value021 (JGc_TX2_HashBytes.state [153,19,7,14,39,146,75,143,167,19,170,143,26,60,63,207,209,103,140,223,4,181,82,97,131,224,162,105,220,45,101,229]))=input033 := by rfl
#print axioms address033
def tree033 : Tree := .branch tree021 (.supplied (JGc_TX2_HashBytes.state [153,19,7,14,39,146,75,143,167,19,170,143,26,60,63,207,209,103,140,223,4,181,82,97,131,224,162,105,220,45,101,229]))
theorem root033 : root JFp_SHADigest.digest tree033=value033 := by
  rw [tree033,root,root021]
  exact (congrArg JFp_SHADigest.digest address033).trans hash033
#print axioms root033
theorem shape033 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 44904=tree033 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 44904)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape021 f g inputs siblings]
  rw [unoccupied f g 1 44906 (by decide),siblings 1 (by decide) 44906 (by decide)]
  rfl
#print axioms shape033
def input034 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash034.message
def value034 : State := JFp_SHADigest.output JGc_TX2_M2.Hash034.result
theorem cast034_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash034.B00.input).map Fin.val=JGc_TX2_M2.Hash034.B00.input := by rfl
#print axioms cast034_0
theorem tail034 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash034.tail).map Fin.val=JGc_TX2_M2.Hash034.tail := by rfl
#print axioms tail034
theorem numeric034 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash034.message).map Fin.val=JGc_TX2_M2.Hash034.message := by
  simp only [JGc_TX2_M2.Hash034.message,JGc_TX2_M2.Hash034.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast034_0,tail034]
#print axioms numeric034
theorem hash034 : JFp_SHADigest.digest input034=value034 := by
  unfold input034 JFp_SHADigest.digest
  rw [numeric034,JGc_TX2_M2.Hash034.checked]
  rfl
#print axioms hash034
theorem address034 : BinMerkle32Path.nodeInput (children value022 (JGc_TX2_HashBytes.state [149,146,136,206,135,184,54,243,49,151,144,138,183,57,96,167,205,119,38,18,59,15,214,146,121,90,119,232,157,129,235,177]))=input034 := by rfl
#print axioms address034
def tree034 : Tree := .branch tree022 (.supplied (JGc_TX2_HashBytes.state [149,146,136,206,135,184,54,243,49,151,144,138,183,57,96,167,205,119,38,18,59,15,214,146,121,90,119,232,157,129,235,177]))
theorem root034 : root JFp_SHADigest.digest tree034=value034 := by
  rw [tree034,root,root022]
  exact (congrArg JFp_SHADigest.digest address034).trans hash034
#print axioms root034
theorem shape034 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 46408=tree034 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 46408)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape022 f g inputs siblings]
  rw [unoccupied f g 1 46410 (by decide),siblings 1 (by decide) 46410 (by decide)]
  rfl
#print axioms shape034
def input035 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash035.message
def value035 : State := JFp_SHADigest.output JGc_TX2_M2.Hash035.result
theorem cast035_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash035.B00.input).map Fin.val=JGc_TX2_M2.Hash035.B00.input := by rfl
#print axioms cast035_0
theorem tail035 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash035.tail).map Fin.val=JGc_TX2_M2.Hash035.tail := by rfl
#print axioms tail035
theorem numeric035 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash035.message).map Fin.val=JGc_TX2_M2.Hash035.message := by
  simp only [JGc_TX2_M2.Hash035.message,JGc_TX2_M2.Hash035.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast035_0,tail035]
#print axioms numeric035
theorem hash035 : JFp_SHADigest.digest input035=value035 := by
  unfold input035 JFp_SHADigest.digest
  rw [numeric035,JGc_TX2_M2.Hash035.checked]
  rfl
#print axioms hash035
theorem address035 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [10,30,26,104,25,237,52,75,60,229,159,181,23,252,33,103,235,23,37,234,195,95,102,113,140,111,81,254,244,220,95,33]) value023)=input035 := by rfl
#print axioms address035
def tree035 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [10,30,26,104,25,237,52,75,60,229,159,181,23,252,33,103,235,23,37,234,195,95,102,113,140,111,81,254,244,220,95,33])) tree023
theorem root035 : root JFp_SHADigest.digest tree035=value035 := by
  rw [tree035,root,root023]
  exact (congrArg JFp_SHADigest.digest address035).trans hash035
#print axioms root035
theorem shape035 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 54520=tree035 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 54520)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 54520 (by decide),siblings 1 (by decide) 54520 (by decide)]
  rw [shape023 f g inputs siblings]
  rfl
#print axioms shape035
end AspisR1.JGc_TX2_M2Roots
end
