import NDO_JGf_TX2_M0Level04
import NDO_JGf_TX2_M0W028
import NDO_JGf_TX2_M0W029
import NDO_JGf_TX2_M0W030
import NDO_JGf_TX2_M0W031
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGf_TX2_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input072 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash072.message
def value072 : State := JFp_SHADigest.output JGf_TX2_M0.Hash072.result
theorem cast072_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash072.B00.input).map Fin.val=JGf_TX2_M0.Hash072.B00.input := by rfl
#print axioms cast072_0
theorem tail072 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash072.tail).map Fin.val=JGf_TX2_M0.Hash072.tail := by rfl
#print axioms tail072
theorem numeric072 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash072.message).map Fin.val=JGf_TX2_M0.Hash072.message := by
  simp only [JGf_TX2_M0.Hash072.message,JGf_TX2_M0.Hash072.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast072_0,tail072]
#print axioms numeric072
theorem hash072 : JFp_SHADigest.digest input072=value072 := by
  unfold input072 JFp_SHADigest.digest
  rw [numeric072,JGf_TX2_M0.Hash072.checked]
  rfl
#print axioms hash072
theorem address072 : BinMerkle32Path.nodeInput (children value060 (JGc_TX2_HashBytes.state [231,229,212,57,61,52,13,131,98,196,105,18,170,125,180,159,155,88,136,210,120,50,162,252,183,109,92,145,239,186,61,138]))=input072 := by rfl
#print axioms address072
def tree072 : Tree := .branch tree060 (.supplied (JGc_TX2_HashBytes.state [231,229,212,57,61,52,13,131,98,196,105,18,170,125,180,159,155,88,136,210,120,50,162,252,183,109,92,145,239,186,61,138]))
theorem root072 : root JFp_SHADigest.digest tree072=value072 := by
  rw [tree072,root,root060]
  exact (congrArg JFp_SHADigest.digest address072).trans hash072
#print axioms root072
theorem shape072 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 14272=tree072 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 14272)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape060 f g inputs siblings]
  rw [unoccupied f g 5 14304 (by decide),siblings 5 (by decide) 14304 (by decide)]
  rfl
#print axioms shape072
def input073 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash073.message
def value073 : State := JFp_SHADigest.output JGf_TX2_M0.Hash073.result
theorem cast073_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash073.B00.input).map Fin.val=JGf_TX2_M0.Hash073.B00.input := by rfl
#print axioms cast073_0
theorem tail073 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash073.tail).map Fin.val=JGf_TX2_M0.Hash073.tail := by rfl
#print axioms tail073
theorem numeric073 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash073.message).map Fin.val=JGf_TX2_M0.Hash073.message := by
  simp only [JGf_TX2_M0.Hash073.message,JGf_TX2_M0.Hash073.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast073_0,tail073]
#print axioms numeric073
theorem hash073 : JFp_SHADigest.digest input073=value073 := by
  unfold input073 JFp_SHADigest.digest
  rw [numeric073,JGf_TX2_M0.Hash073.checked]
  rfl
#print axioms hash073
theorem address073 : BinMerkle32Path.nodeInput (children value061 (JGc_TX2_HashBytes.state [208,106,137,156,88,252,163,167,103,236,35,6,239,195,55,37,126,226,113,63,72,148,131,98,39,186,94,170,101,28,78,97]))=input073 := by rfl
#print axioms address073
def tree073 : Tree := .branch tree061 (.supplied (JGc_TX2_HashBytes.state [208,106,137,156,88,252,163,167,103,236,35,6,239,195,55,37,126,226,113,63,72,148,131,98,39,186,94,170,101,28,78,97]))
theorem root073 : root JFp_SHADigest.digest tree073=value073 := by
  rw [tree073,root,root061]
  exact (congrArg JFp_SHADigest.digest address073).trans hash073
#print axioms root073
theorem shape073 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 21248=tree073 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 21248)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape061 f g inputs siblings]
  rw [unoccupied f g 5 21280 (by decide),siblings 5 (by decide) 21280 (by decide)]
  rfl
#print axioms shape073
def input074 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash074.message
def value074 : State := JFp_SHADigest.output JGf_TX2_M0.Hash074.result
theorem cast074_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash074.B00.input).map Fin.val=JGf_TX2_M0.Hash074.B00.input := by rfl
#print axioms cast074_0
theorem tail074 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash074.tail).map Fin.val=JGf_TX2_M0.Hash074.tail := by rfl
#print axioms tail074
theorem numeric074 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash074.message).map Fin.val=JGf_TX2_M0.Hash074.message := by
  simp only [JGf_TX2_M0.Hash074.message,JGf_TX2_M0.Hash074.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast074_0,tail074]
#print axioms numeric074
theorem hash074 : JFp_SHADigest.digest input074=value074 := by
  unfold input074 JFp_SHADigest.digest
  rw [numeric074,JGf_TX2_M0.Hash074.checked]
  rfl
#print axioms hash074
theorem address074 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [96,86,165,214,60,58,153,79,245,118,213,70,119,212,97,94,73,218,75,178,144,237,239,5,152,168,50,70,114,194,196,190]) value062)=input074 := by rfl
#print axioms address074
def tree074 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [96,86,165,214,60,58,153,79,245,118,213,70,119,212,97,94,73,218,75,178,144,237,239,5,152,168,50,70,114,194,196,190])) tree062
theorem root074 : root JFp_SHADigest.digest tree074=value074 := by
  rw [tree074,root,root062]
  exact (congrArg JFp_SHADigest.digest address074).trans hash074
#print axioms root074
theorem shape074 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 42112=tree074 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 42112)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 42112 (by decide),siblings 5 (by decide) 42112 (by decide)]
  rw [shape062 f g inputs siblings]
  rfl
#print axioms shape074
def input075 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash075.message
def value075 : State := JFp_SHADigest.output JGf_TX2_M0.Hash075.result
theorem cast075_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash075.B00.input).map Fin.val=JGf_TX2_M0.Hash075.B00.input := by rfl
#print axioms cast075_0
theorem tail075 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash075.tail).map Fin.val=JGf_TX2_M0.Hash075.tail := by rfl
#print axioms tail075
theorem numeric075 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash075.message).map Fin.val=JGf_TX2_M0.Hash075.message := by
  simp only [JGf_TX2_M0.Hash075.message,JGf_TX2_M0.Hash075.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast075_0,tail075]
#print axioms numeric075
theorem hash075 : JFp_SHADigest.digest input075=value075 := by
  unfold input075 JFp_SHADigest.digest
  rw [numeric075,JGf_TX2_M0.Hash075.checked]
  rfl
#print axioms hash075
theorem address075 : BinMerkle32Path.nodeInput (children value063 (JGc_TX2_HashBytes.state [67,56,172,155,250,179,222,134,219,90,202,255,153,121,98,56,144,27,144,127,45,183,122,190,111,165,244,250,51,94,26,214]))=input075 := by rfl
#print axioms address075
def tree075 : Tree := .branch tree063 (.supplied (JGc_TX2_HashBytes.state [67,56,172,155,250,179,222,134,219,90,202,255,153,121,98,56,144,27,144,127,45,183,122,190,111,165,244,250,51,94,26,214]))
theorem root075 : root JFp_SHADigest.digest tree075=value075 := by
  rw [tree075,root,root063]
  exact (congrArg JFp_SHADigest.digest address075).trans hash075
#print axioms root075
theorem shape075 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 55360=tree075 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 55360)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape063 f g inputs siblings]
  rw [unoccupied f g 5 55392 (by decide),siblings 5 (by decide) 55392 (by decide)]
  rfl
#print axioms shape075
def input076 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash076.message
def value076 : State := JFp_SHADigest.output JGf_TX2_M0.Hash076.result
theorem cast076_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash076.B00.input).map Fin.val=JGf_TX2_M0.Hash076.B00.input := by rfl
#print axioms cast076_0
theorem tail076 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash076.tail).map Fin.val=JGf_TX2_M0.Hash076.tail := by rfl
#print axioms tail076
theorem numeric076 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash076.message).map Fin.val=JGf_TX2_M0.Hash076.message := by
  simp only [JGf_TX2_M0.Hash076.message,JGf_TX2_M0.Hash076.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast076_0,tail076]
#print axioms numeric076
theorem hash076 : JFp_SHADigest.digest input076=value076 := by
  unfold input076 JFp_SHADigest.digest
  rw [numeric076,JGf_TX2_M0.Hash076.checked]
  rfl
#print axioms hash076
theorem address076 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [137,230,227,165,233,42,125,178,96,86,175,162,161,211,230,12,211,67,26,123,39,21,192,98,16,164,106,28,9,61,16,102]) value064)=input076 := by rfl
#print axioms address076
def tree076 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [137,230,227,165,233,42,125,178,96,86,175,162,161,211,230,12,211,67,26,123,39,21,192,98,16,164,106,28,9,61,16,102])) tree064
theorem root076 : root JFp_SHADigest.digest tree076=value076 := by
  rw [tree076,root,root064]
  exact (congrArg JFp_SHADigest.digest address076).trans hash076
#print axioms root076
theorem shape076 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 63808=tree076 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 63808)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 63808 (by decide),siblings 5 (by decide) 63808 (by decide)]
  rw [shape064 f g inputs siblings]
  rfl
#print axioms shape076
def input077 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash077.message
def value077 : State := JFp_SHADigest.output JGf_TX2_M0.Hash077.result
theorem cast077_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash077.B00.input).map Fin.val=JGf_TX2_M0.Hash077.B00.input := by rfl
#print axioms cast077_0
theorem tail077 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash077.tail).map Fin.val=JGf_TX2_M0.Hash077.tail := by rfl
#print axioms tail077
theorem numeric077 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash077.message).map Fin.val=JGf_TX2_M0.Hash077.message := by
  simp only [JGf_TX2_M0.Hash077.message,JGf_TX2_M0.Hash077.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast077_0,tail077]
#print axioms numeric077
theorem hash077 : JFp_SHADigest.digest input077=value077 := by
  unfold input077 JFp_SHADigest.digest
  rw [numeric077,JGf_TX2_M0.Hash077.checked]
  rfl
#print axioms hash077
theorem address077 : BinMerkle32Path.nodeInput (children value065 (JGc_TX2_HashBytes.state [63,8,57,60,116,219,77,27,90,202,240,19,201,3,4,1,44,37,168,199,67,205,148,46,190,34,185,150,152,219,190,185]))=input077 := by rfl
#print axioms address077
def tree077 : Tree := .branch tree065 (.supplied (JGc_TX2_HashBytes.state [63,8,57,60,116,219,77,27,90,202,240,19,201,3,4,1,44,37,168,199,67,205,148,46,190,34,185,150,152,219,190,185]))
theorem root077 : root JFp_SHADigest.digest tree077=value077 := by
  rw [tree077,root,root065]
  exact (congrArg JFp_SHADigest.digest address077).trans hash077
#print axioms root077
theorem shape077 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 132352=tree077 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 132352)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape065 f g inputs siblings]
  rw [unoccupied f g 5 132384 (by decide),siblings 5 (by decide) 132384 (by decide)]
  rfl
#print axioms shape077
def input078 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash078.message
def value078 : State := JFp_SHADigest.output JGf_TX2_M0.Hash078.result
theorem cast078_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash078.B00.input).map Fin.val=JGf_TX2_M0.Hash078.B00.input := by rfl
#print axioms cast078_0
theorem tail078 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash078.tail).map Fin.val=JGf_TX2_M0.Hash078.tail := by rfl
#print axioms tail078
theorem numeric078 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash078.message).map Fin.val=JGf_TX2_M0.Hash078.message := by
  simp only [JGf_TX2_M0.Hash078.message,JGf_TX2_M0.Hash078.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast078_0,tail078]
#print axioms numeric078
theorem hash078 : JFp_SHADigest.digest input078=value078 := by
  unfold input078 JFp_SHADigest.digest
  rw [numeric078,JGf_TX2_M0.Hash078.checked]
  rfl
#print axioms hash078
theorem address078 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [40,148,151,234,47,81,210,205,168,84,182,75,116,195,24,72,138,16,180,55,51,82,30,80,248,67,3,180,153,50,12,9]) value066)=input078 := by rfl
#print axioms address078
def tree078 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [40,148,151,234,47,81,210,205,168,84,182,75,116,195,24,72,138,16,180,55,51,82,30,80,248,67,3,180,153,50,12,9])) tree066
theorem root078 : root JFp_SHADigest.digest tree078=value078 := by
  rw [tree078,root,root066]
  exact (congrArg JFp_SHADigest.digest address078).trans hash078
#print axioms root078
theorem shape078 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 149568=tree078 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 149568)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 149568 (by decide),siblings 5 (by decide) 149568 (by decide)]
  rw [shape066 f g inputs siblings]
  rfl
#print axioms shape078
def input079 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash079.message
def value079 : State := JFp_SHADigest.output JGf_TX2_M0.Hash079.result
theorem cast079_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash079.B00.input).map Fin.val=JGf_TX2_M0.Hash079.B00.input := by rfl
#print axioms cast079_0
theorem tail079 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash079.tail).map Fin.val=JGf_TX2_M0.Hash079.tail := by rfl
#print axioms tail079
theorem numeric079 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash079.message).map Fin.val=JGf_TX2_M0.Hash079.message := by
  simp only [JGf_TX2_M0.Hash079.message,JGf_TX2_M0.Hash079.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast079_0,tail079]
#print axioms numeric079
theorem hash079 : JFp_SHADigest.digest input079=value079 := by
  unfold input079 JFp_SHADigest.digest
  rw [numeric079,JGf_TX2_M0.Hash079.checked]
  rfl
#print axioms hash079
theorem address079 : BinMerkle32Path.nodeInput (children value067 (JGc_TX2_HashBytes.state [226,33,86,10,93,130,74,210,30,96,38,232,163,178,202,190,106,193,115,33,153,59,158,30,27,85,135,153,164,154,213,23]))=input079 := by rfl
#print axioms address079
def tree079 : Tree := .branch tree067 (.supplied (JGc_TX2_HashBytes.state [226,33,86,10,93,130,74,210,30,96,38,232,163,178,202,190,106,193,115,33,153,59,158,30,27,85,135,153,164,154,213,23]))
theorem root079 : root JFp_SHADigest.digest tree079=value079 := by
  rw [tree079,root,root067]
  exact (congrArg JFp_SHADigest.digest address079).trans hash079
#print axioms root079
theorem shape079 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 166144=tree079 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 166144)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape067 f g inputs siblings]
  rw [unoccupied f g 5 166176 (by decide),siblings 5 (by decide) 166176 (by decide)]
  rfl
#print axioms shape079
def input080 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash080.message
def value080 : State := JFp_SHADigest.output JGf_TX2_M0.Hash080.result
theorem cast080_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash080.B00.input).map Fin.val=JGf_TX2_M0.Hash080.B00.input := by rfl
#print axioms cast080_0
theorem tail080 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash080.tail).map Fin.val=JGf_TX2_M0.Hash080.tail := by rfl
#print axioms tail080
theorem numeric080 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash080.message).map Fin.val=JGf_TX2_M0.Hash080.message := by
  simp only [JGf_TX2_M0.Hash080.message,JGf_TX2_M0.Hash080.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast080_0,tail080]
#print axioms numeric080
theorem hash080 : JFp_SHADigest.digest input080=value080 := by
  unfold input080 JFp_SHADigest.digest
  rw [numeric080,JGf_TX2_M0.Hash080.checked]
  rfl
#print axioms hash080
theorem address080 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [129,93,233,4,10,237,255,49,97,128,241,124,80,41,207,190,126,211,126,91,31,193,143,89,254,222,118,216,114,175,42,17]) value068)=input080 := by rfl
#print axioms address080
def tree080 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [129,93,233,4,10,237,255,49,97,128,241,124,80,41,207,190,126,211,126,91,31,193,143,89,254,222,118,216,114,175,42,17])) tree068
theorem root080 : root JFp_SHADigest.digest tree080=value080 := by
  rw [tree080,root,root068]
  exact (congrArg JFp_SHADigest.digest address080).trans hash080
#print axioms root080
theorem shape080 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 178048=tree080 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 178048)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 178048 (by decide),siblings 5 (by decide) 178048 (by decide)]
  rw [shape068 f g inputs siblings]
  rfl
#print axioms shape080
def input081 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash081.message
def value081 : State := JFp_SHADigest.output JGf_TX2_M0.Hash081.result
theorem cast081_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash081.B00.input).map Fin.val=JGf_TX2_M0.Hash081.B00.input := by rfl
#print axioms cast081_0
theorem tail081 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash081.tail).map Fin.val=JGf_TX2_M0.Hash081.tail := by rfl
#print axioms tail081
theorem numeric081 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash081.message).map Fin.val=JGf_TX2_M0.Hash081.message := by
  simp only [JGf_TX2_M0.Hash081.message,JGf_TX2_M0.Hash081.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast081_0,tail081]
#print axioms numeric081
theorem hash081 : JFp_SHADigest.digest input081=value081 := by
  unfold input081 JFp_SHADigest.digest
  rw [numeric081,JGf_TX2_M0.Hash081.checked]
  rfl
#print axioms hash081
theorem address081 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [22,71,7,19,51,149,73,150,190,170,30,203,179,236,91,204,95,54,245,160,239,72,74,49,49,87,24,43,131,42,87,52]) value069)=input081 := by rfl
#print axioms address081
def tree081 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [22,71,7,19,51,149,73,150,190,170,30,203,179,236,91,204,95,54,245,160,239,72,74,49,49,87,24,43,131,42,87,52])) tree069
theorem root081 : root JFp_SHADigest.digest tree081=value081 := by
  rw [tree081,root,root069]
  exact (congrArg JFp_SHADigest.digest address081).trans hash081
#print axioms root081
theorem shape081 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 179584=tree081 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 179584)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 179584 (by decide),siblings 5 (by decide) 179584 (by decide)]
  rw [shape069 f g inputs siblings]
  rfl
#print axioms shape081
def input082 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash082.message
def value082 : State := JFp_SHADigest.output JGf_TX2_M0.Hash082.result
theorem cast082_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash082.B00.input).map Fin.val=JGf_TX2_M0.Hash082.B00.input := by rfl
#print axioms cast082_0
theorem tail082 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash082.tail).map Fin.val=JGf_TX2_M0.Hash082.tail := by rfl
#print axioms tail082
theorem numeric082 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash082.message).map Fin.val=JGf_TX2_M0.Hash082.message := by
  simp only [JGf_TX2_M0.Hash082.message,JGf_TX2_M0.Hash082.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast082_0,tail082]
#print axioms numeric082
theorem hash082 : JFp_SHADigest.digest input082=value082 := by
  unfold input082 JFp_SHADigest.digest
  rw [numeric082,JGf_TX2_M0.Hash082.checked]
  rfl
#print axioms hash082
theorem address082 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [199,10,148,235,137,56,26,21,42,164,55,2,116,225,94,53,71,47,166,136,132,254,119,246,161,220,161,87,230,45,113,199]) value070)=input082 := by rfl
#print axioms address082
def tree082 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [199,10,148,235,137,56,26,21,42,164,55,2,116,225,94,53,71,47,166,136,132,254,119,246,161,220,161,87,230,45,113,199])) tree070
theorem root082 : root JFp_SHADigest.digest tree082=value082 := by
  rw [tree082,root,root070]
  exact (congrArg JFp_SHADigest.digest address082).trans hash082
#print axioms root082
theorem shape082 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 185600=tree082 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 185600)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 185600 (by decide),siblings 5 (by decide) 185600 (by decide)]
  rw [shape070 f g inputs siblings]
  rfl
#print axioms shape082
def input083 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash083.message
def value083 : State := JFp_SHADigest.output JGf_TX2_M0.Hash083.result
theorem cast083_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash083.B00.input).map Fin.val=JGf_TX2_M0.Hash083.B00.input := by rfl
#print axioms cast083_0
theorem tail083 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash083.tail).map Fin.val=JGf_TX2_M0.Hash083.tail := by rfl
#print axioms tail083
theorem numeric083 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash083.message).map Fin.val=JGf_TX2_M0.Hash083.message := by
  simp only [JGf_TX2_M0.Hash083.message,JGf_TX2_M0.Hash083.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast083_0,tail083]
#print axioms numeric083
theorem hash083 : JFp_SHADigest.digest input083=value083 := by
  unfold input083 JFp_SHADigest.digest
  rw [numeric083,JGf_TX2_M0.Hash083.checked]
  rfl
#print axioms hash083
theorem address083 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [72,241,117,171,183,245,182,47,99,0,248,6,146,198,34,85,212,4,80,93,238,61,89,145,106,182,22,198,155,40,28,141]) value071)=input083 := by rfl
#print axioms address083
def tree083 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [72,241,117,171,183,245,182,47,99,0,248,6,146,198,34,85,212,4,80,93,238,61,89,145,106,182,22,198,155,40,28,141])) tree071
theorem root083 : root JFp_SHADigest.digest tree083=value083 := by
  rw [tree083,root,root071]
  exact (congrArg JFp_SHADigest.digest address083).trans hash083
#print axioms root083
theorem shape083 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 218048=tree083 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 218048)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 218048 (by decide),siblings 5 (by decide) 218048 (by decide)]
  rw [shape071 f g inputs siblings]
  rfl
#print axioms shape083
end AspisR1.JGf_TX2_M0Roots
end
