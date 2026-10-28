import NDO_JGc_TX2_M2Level04
import NDO_JGc_TX2_M2H072
import NDO_JGc_TX2_M2H076
import NDO_JGc_TX2_M2H080
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input072 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash072.message
def value072 : State := JFp_SHADigest.output JGc_TX2_M2.Hash072.result
theorem cast072_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash072.B00.input).map Fin.val=JGc_TX2_M2.Hash072.B00.input := by rfl
#print axioms cast072_0
theorem tail072 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash072.tail).map Fin.val=JGc_TX2_M2.Hash072.tail := by rfl
#print axioms tail072
theorem numeric072 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash072.message).map Fin.val=JGc_TX2_M2.Hash072.message := by
  simp only [JGc_TX2_M2.Hash072.message,JGc_TX2_M2.Hash072.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast072_0,tail072]
#print axioms numeric072
theorem hash072 : JFp_SHADigest.digest input072=value072 := by
  unfold input072 JFp_SHADigest.digest
  rw [numeric072,JGc_TX2_M2.Hash072.checked]
  rfl
#print axioms hash072
theorem address072 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [1,237,18,196,233,39,178,178,35,79,53,190,211,240,20,96,230,205,40,85,182,76,58,95,169,70,172,81,91,109,154,181]) value060)=input072 := by rfl
#print axioms address072
def tree072 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [1,237,18,196,233,39,178,178,35,79,53,190,211,240,20,96,230,205,40,85,182,76,58,95,169,70,172,81,91,109,154,181])) tree060
theorem root072 : root JFp_SHADigest.digest tree072=value072 := by
  rw [tree072,root,root060]
  exact (congrArg JFp_SHADigest.digest address072).trans hash072
#print axioms root072
theorem shape072 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 3520=tree072 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 3520)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 3520 (by decide),siblings 5 (by decide) 3520 (by decide)]
  rw [shape060 f g inputs siblings]
  rfl
#print axioms shape072
def input073 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash073.message
def value073 : State := JFp_SHADigest.output JGc_TX2_M2.Hash073.result
theorem cast073_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash073.B00.input).map Fin.val=JGc_TX2_M2.Hash073.B00.input := by rfl
#print axioms cast073_0
theorem tail073 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash073.tail).map Fin.val=JGc_TX2_M2.Hash073.tail := by rfl
#print axioms tail073
theorem numeric073 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash073.message).map Fin.val=JGc_TX2_M2.Hash073.message := by
  simp only [JGc_TX2_M2.Hash073.message,JGc_TX2_M2.Hash073.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast073_0,tail073]
#print axioms numeric073
theorem hash073 : JFp_SHADigest.digest input073=value073 := by
  unfold input073 JFp_SHADigest.digest
  rw [numeric073,JGc_TX2_M2.Hash073.checked]
  rfl
#print axioms hash073
theorem address073 : BinMerkle32Path.nodeInput (children value061 (JGc_TX2_HashBytes.state [17,110,165,89,88,97,204,188,157,141,239,241,82,170,13,164,58,245,11,101,142,71,56,55,72,84,189,184,122,166,208,77]))=input073 := by rfl
#print axioms address073
def tree073 : Tree := .branch tree061 (.supplied (JGc_TX2_HashBytes.state [17,110,165,89,88,97,204,188,157,141,239,241,82,170,13,164,58,245,11,101,142,71,56,55,72,84,189,184,122,166,208,77]))
theorem root073 : root JFp_SHADigest.digest tree073=value073 := by
  rw [tree073,root,root061]
  exact (congrArg JFp_SHADigest.digest address073).trans hash073
#print axioms root073
theorem shape073 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 5312=tree073 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 5312)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape061 f g inputs siblings]
  rw [unoccupied f g 5 5344 (by decide),siblings 5 (by decide) 5344 (by decide)]
  rfl
#print axioms shape073
def input074 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash074.message
def value074 : State := JFp_SHADigest.output JGc_TX2_M2.Hash074.result
theorem cast074_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash074.B00.input).map Fin.val=JGc_TX2_M2.Hash074.B00.input := by rfl
#print axioms cast074_0
theorem tail074 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash074.tail).map Fin.val=JGc_TX2_M2.Hash074.tail := by rfl
#print axioms tail074
theorem numeric074 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash074.message).map Fin.val=JGc_TX2_M2.Hash074.message := by
  simp only [JGc_TX2_M2.Hash074.message,JGc_TX2_M2.Hash074.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast074_0,tail074]
#print axioms numeric074
theorem hash074 : JFp_SHADigest.digest input074=value074 := by
  unfold input074 JFp_SHADigest.digest
  rw [numeric074,JGc_TX2_M2.Hash074.checked]
  rfl
#print axioms hash074
theorem address074 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [246,104,63,223,79,203,181,70,53,144,44,89,118,225,29,149,201,76,85,31,185,128,109,46,33,13,209,195,9,122,247,44]) value062)=input074 := by rfl
#print axioms address074
def tree074 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [246,104,63,223,79,203,181,70,53,144,44,89,118,225,29,149,201,76,85,31,185,128,109,46,33,13,209,195,9,122,247,44])) tree062
theorem root074 : root JFp_SHADigest.digest tree074=value074 := by
  rw [tree074,root,root062]
  exact (congrArg JFp_SHADigest.digest address074).trans hash074
#print axioms root074
theorem shape074 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 10496=tree074 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 10496)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 10496 (by decide),siblings 5 (by decide) 10496 (by decide)]
  rw [shape062 f g inputs siblings]
  rfl
#print axioms shape074
def input075 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash075.message
def value075 : State := JFp_SHADigest.output JGc_TX2_M2.Hash075.result
theorem cast075_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash075.B00.input).map Fin.val=JGc_TX2_M2.Hash075.B00.input := by rfl
#print axioms cast075_0
theorem tail075 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash075.tail).map Fin.val=JGc_TX2_M2.Hash075.tail := by rfl
#print axioms tail075
theorem numeric075 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash075.message).map Fin.val=JGc_TX2_M2.Hash075.message := by
  simp only [JGc_TX2_M2.Hash075.message,JGc_TX2_M2.Hash075.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast075_0,tail075]
#print axioms numeric075
theorem hash075 : JFp_SHADigest.digest input075=value075 := by
  unfold input075 JFp_SHADigest.digest
  rw [numeric075,JGc_TX2_M2.Hash075.checked]
  rfl
#print axioms hash075
theorem address075 : BinMerkle32Path.nodeInput (children value063 (JGc_TX2_HashBytes.state [1,116,42,43,182,84,192,200,101,253,7,63,138,245,88,234,36,26,217,235,97,4,151,224,83,147,6,191,142,125,170,23]))=input075 := by rfl
#print axioms address075
def tree075 : Tree := .branch tree063 (.supplied (JGc_TX2_HashBytes.state [1,116,42,43,182,84,192,200,101,253,7,63,138,245,88,234,36,26,217,235,97,4,151,224,83,147,6,191,142,125,170,23]))
theorem root075 : root JFp_SHADigest.digest tree075=value075 := by
  rw [tree075,root,root063]
  exact (congrArg JFp_SHADigest.digest address075).trans hash075
#print axioms root075
theorem shape075 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 13824=tree075 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 13824)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape063 f g inputs siblings]
  rw [unoccupied f g 5 13856 (by decide),siblings 5 (by decide) 13856 (by decide)]
  rfl
#print axioms shape075
def input076 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash076.message
def value076 : State := JFp_SHADigest.output JGc_TX2_M2.Hash076.result
theorem cast076_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash076.B00.input).map Fin.val=JGc_TX2_M2.Hash076.B00.input := by rfl
#print axioms cast076_0
theorem tail076 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash076.tail).map Fin.val=JGc_TX2_M2.Hash076.tail := by rfl
#print axioms tail076
theorem numeric076 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash076.message).map Fin.val=JGc_TX2_M2.Hash076.message := by
  simp only [JGc_TX2_M2.Hash076.message,JGc_TX2_M2.Hash076.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast076_0,tail076]
#print axioms numeric076
theorem hash076 : JFp_SHADigest.digest input076=value076 := by
  unfold input076 JFp_SHADigest.digest
  rw [numeric076,JGc_TX2_M2.Hash076.checked]
  rfl
#print axioms hash076
theorem address076 : BinMerkle32Path.nodeInput (children value064 (JGc_TX2_HashBytes.state [7,196,171,243,14,126,26,212,69,228,46,121,239,212,235,111,190,18,86,44,45,11,68,56,140,174,80,33,135,177,110,33]))=input076 := by rfl
#print axioms address076
def tree076 : Tree := .branch tree064 (.supplied (JGc_TX2_HashBytes.state [7,196,171,243,14,126,26,212,69,228,46,121,239,212,235,111,190,18,86,44,45,11,68,56,140,174,80,33,135,177,110,33]))
theorem root076 : root JFp_SHADigest.digest tree076=value076 := by
  rw [tree076,root,root064]
  exact (congrArg JFp_SHADigest.digest address076).trans hash076
#print axioms root076
theorem shape076 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 15936=tree076 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 15936)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape064 f g inputs siblings]
  rw [unoccupied f g 5 15968 (by decide),siblings 5 (by decide) 15968 (by decide)]
  rfl
#print axioms shape076
def input077 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash077.message
def value077 : State := JFp_SHADigest.output JGc_TX2_M2.Hash077.result
theorem cast077_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash077.B00.input).map Fin.val=JGc_TX2_M2.Hash077.B00.input := by rfl
#print axioms cast077_0
theorem tail077 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash077.tail).map Fin.val=JGc_TX2_M2.Hash077.tail := by rfl
#print axioms tail077
theorem numeric077 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash077.message).map Fin.val=JGc_TX2_M2.Hash077.message := by
  simp only [JGc_TX2_M2.Hash077.message,JGc_TX2_M2.Hash077.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast077_0,tail077]
#print axioms numeric077
theorem hash077 : JFp_SHADigest.digest input077=value077 := by
  unfold input077 JFp_SHADigest.digest
  rw [numeric077,JGc_TX2_M2.Hash077.checked]
  rfl
#print axioms hash077
theorem address077 : BinMerkle32Path.nodeInput (children value065 (JGc_TX2_HashBytes.state [111,175,90,42,65,26,233,28,53,239,157,159,251,176,155,75,50,212,185,156,215,209,132,169,50,45,67,159,9,15,241,110]))=input077 := by rfl
#print axioms address077
def tree077 : Tree := .branch tree065 (.supplied (JGc_TX2_HashBytes.state [111,175,90,42,65,26,233,28,53,239,157,159,251,176,155,75,50,212,185,156,215,209,132,169,50,45,67,159,9,15,241,110]))
theorem root077 : root JFp_SHADigest.digest tree077=value077 := by
  rw [tree077,root,root065]
  exact (congrArg JFp_SHADigest.digest address077).trans hash077
#print axioms root077
theorem shape077 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 33088=tree077 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 33088)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape065 f g inputs siblings]
  rw [unoccupied f g 5 33120 (by decide),siblings 5 (by decide) 33120 (by decide)]
  rfl
#print axioms shape077
def input078 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash078.message
def value078 : State := JFp_SHADigest.output JGc_TX2_M2.Hash078.result
theorem cast078_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash078.B00.input).map Fin.val=JGc_TX2_M2.Hash078.B00.input := by rfl
#print axioms cast078_0
theorem tail078 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash078.tail).map Fin.val=JGc_TX2_M2.Hash078.tail := by rfl
#print axioms tail078
theorem numeric078 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash078.message).map Fin.val=JGc_TX2_M2.Hash078.message := by
  simp only [JGc_TX2_M2.Hash078.message,JGc_TX2_M2.Hash078.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast078_0,tail078]
#print axioms numeric078
theorem hash078 : JFp_SHADigest.digest input078=value078 := by
  unfold input078 JFp_SHADigest.digest
  rw [numeric078,JGc_TX2_M2.Hash078.checked]
  rfl
#print axioms hash078
theorem address078 : BinMerkle32Path.nodeInput (children value066 (JGc_TX2_HashBytes.state [85,21,32,249,224,176,168,172,119,102,236,89,29,42,238,30,194,98,172,247,142,11,173,110,64,226,99,23,154,152,22,64]))=input078 := by rfl
#print axioms address078
def tree078 : Tree := .branch tree066 (.supplied (JGc_TX2_HashBytes.state [85,21,32,249,224,176,168,172,119,102,236,89,29,42,238,30,194,98,172,247,142,11,173,110,64,226,99,23,154,152,22,64]))
theorem root078 : root JFp_SHADigest.digest tree078=value078 := by
  rw [tree078,root,root066]
  exact (congrArg JFp_SHADigest.digest address078).trans hash078
#print axioms root078
theorem shape078 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 37376=tree078 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 37376)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape066 f g inputs siblings]
  rw [unoccupied f g 5 37408 (by decide),siblings 5 (by decide) 37408 (by decide)]
  rfl
#print axioms shape078
def input079 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash079.message
def value079 : State := JFp_SHADigest.output JGc_TX2_M2.Hash079.result
theorem cast079_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash079.B00.input).map Fin.val=JGc_TX2_M2.Hash079.B00.input := by rfl
#print axioms cast079_0
theorem tail079 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash079.tail).map Fin.val=JGc_TX2_M2.Hash079.tail := by rfl
#print axioms tail079
theorem numeric079 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash079.message).map Fin.val=JGc_TX2_M2.Hash079.message := by
  simp only [JGc_TX2_M2.Hash079.message,JGc_TX2_M2.Hash079.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast079_0,tail079]
#print axioms numeric079
theorem hash079 : JFp_SHADigest.digest input079=value079 := by
  unfold input079 JFp_SHADigest.digest
  rw [numeric079,JGc_TX2_M2.Hash079.checked]
  rfl
#print axioms hash079
theorem address079 : BinMerkle32Path.nodeInput (children value067 (JGc_TX2_HashBytes.state [198,122,239,139,202,85,228,34,247,38,228,144,73,228,184,236,63,242,121,77,143,25,210,71,24,47,70,226,141,125,211,152]))=input079 := by rfl
#print axioms address079
def tree079 : Tree := .branch tree067 (.supplied (JGc_TX2_HashBytes.state [198,122,239,139,202,85,228,34,247,38,228,144,73,228,184,236,63,242,121,77,143,25,210,71,24,47,70,226,141,125,211,152]))
theorem root079 : root JFp_SHADigest.digest tree079=value079 := by
  rw [tree079,root,root067]
  exact (congrArg JFp_SHADigest.digest address079).trans hash079
#print axioms root079
theorem shape079 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 41536=tree079 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 41536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape067 f g inputs siblings]
  rw [unoccupied f g 5 41568 (by decide),siblings 5 (by decide) 41568 (by decide)]
  rfl
#print axioms shape079
def input080 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash080.message
def value080 : State := JFp_SHADigest.output JGc_TX2_M2.Hash080.result
theorem cast080_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash080.B00.input).map Fin.val=JGc_TX2_M2.Hash080.B00.input := by rfl
#print axioms cast080_0
theorem tail080 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash080.tail).map Fin.val=JGc_TX2_M2.Hash080.tail := by rfl
#print axioms tail080
theorem numeric080 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash080.message).map Fin.val=JGc_TX2_M2.Hash080.message := by
  simp only [JGc_TX2_M2.Hash080.message,JGc_TX2_M2.Hash080.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast080_0,tail080]
#print axioms numeric080
theorem hash080 : JFp_SHADigest.digest input080=value080 := by
  unfold input080 JFp_SHADigest.digest
  rw [numeric080,JGc_TX2_M2.Hash080.checked]
  rfl
#print axioms hash080
theorem address080 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [140,227,29,105,106,55,63,242,192,126,99,62,84,5,235,217,55,45,24,103,164,246,172,215,109,36,253,146,12,209,202,171]) value068)=input080 := by rfl
#print axioms address080
def tree080 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [140,227,29,105,106,55,63,242,192,126,99,62,84,5,235,217,55,45,24,103,164,246,172,215,109,36,253,146,12,209,202,171])) tree068
theorem root080 : root JFp_SHADigest.digest tree080=value080 := by
  rw [tree080,root,root068]
  exact (congrArg JFp_SHADigest.digest address080).trans hash080
#print axioms root080
theorem shape080 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 44480=tree080 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 44480)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 44480 (by decide),siblings 5 (by decide) 44480 (by decide)]
  rw [shape068 f g inputs siblings]
  rfl
#print axioms shape080
def input081 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash081.message
def value081 : State := JFp_SHADigest.output JGc_TX2_M2.Hash081.result
theorem cast081_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash081.B00.input).map Fin.val=JGc_TX2_M2.Hash081.B00.input := by rfl
#print axioms cast081_0
theorem tail081 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash081.tail).map Fin.val=JGc_TX2_M2.Hash081.tail := by rfl
#print axioms tail081
theorem numeric081 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash081.message).map Fin.val=JGc_TX2_M2.Hash081.message := by
  simp only [JGc_TX2_M2.Hash081.message,JGc_TX2_M2.Hash081.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast081_0,tail081]
#print axioms numeric081
theorem hash081 : JFp_SHADigest.digest input081=value081 := by
  unfold input081 JFp_SHADigest.digest
  rw [numeric081,JGc_TX2_M2.Hash081.checked]
  rfl
#print axioms hash081
theorem address081 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [11,101,205,179,141,3,233,199,62,225,0,7,254,175,205,162,175,152,62,124,12,72,127,66,155,175,208,76,69,60,37,211]) value069)=input081 := by rfl
#print axioms address081
def tree081 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [11,101,205,179,141,3,233,199,62,225,0,7,254,175,205,162,175,152,62,124,12,72,127,66,155,175,208,76,69,60,37,211])) tree069
theorem root081 : root JFp_SHADigest.digest tree081=value081 := by
  rw [tree081,root,root069]
  exact (congrArg JFp_SHADigest.digest address081).trans hash081
#print axioms root081
theorem shape081 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 44864=tree081 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 44864)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 44864 (by decide),siblings 5 (by decide) 44864 (by decide)]
  rw [shape069 f g inputs siblings]
  rfl
#print axioms shape081
def input082 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash082.message
def value082 : State := JFp_SHADigest.output JGc_TX2_M2.Hash082.result
theorem cast082_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash082.B00.input).map Fin.val=JGc_TX2_M2.Hash082.B00.input := by rfl
#print axioms cast082_0
theorem tail082 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash082.tail).map Fin.val=JGc_TX2_M2.Hash082.tail := by rfl
#print axioms tail082
theorem numeric082 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash082.message).map Fin.val=JGc_TX2_M2.Hash082.message := by
  simp only [JGc_TX2_M2.Hash082.message,JGc_TX2_M2.Hash082.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast082_0,tail082]
#print axioms numeric082
theorem hash082 : JFp_SHADigest.digest input082=value082 := by
  unfold input082 JFp_SHADigest.digest
  rw [numeric082,JGc_TX2_M2.Hash082.checked]
  rfl
#print axioms hash082
theorem address082 : BinMerkle32Path.nodeInput (children value070 (JGc_TX2_HashBytes.state [228,243,146,146,115,1,11,211,23,234,114,128,161,58,90,191,60,47,246,50,229,123,228,139,231,20,48,252,93,44,173,67]))=input082 := by rfl
#print axioms address082
def tree082 : Tree := .branch tree070 (.supplied (JGc_TX2_HashBytes.state [228,243,146,146,115,1,11,211,23,234,114,128,161,58,90,191,60,47,246,50,229,123,228,139,231,20,48,252,93,44,173,67]))
theorem root082 : root JFp_SHADigest.digest tree082=value082 := by
  rw [tree082,root,root070]
  exact (congrArg JFp_SHADigest.digest address082).trans hash082
#print axioms root082
theorem shape082 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 46400=tree082 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 46400)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape070 f g inputs siblings]
  rw [unoccupied f g 5 46432 (by decide),siblings 5 (by decide) 46432 (by decide)]
  rfl
#print axioms shape082
def input083 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash083.message
def value083 : State := JFp_SHADigest.output JGc_TX2_M2.Hash083.result
theorem cast083_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash083.B00.input).map Fin.val=JGc_TX2_M2.Hash083.B00.input := by rfl
#print axioms cast083_0
theorem tail083 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash083.tail).map Fin.val=JGc_TX2_M2.Hash083.tail := by rfl
#print axioms tail083
theorem numeric083 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash083.message).map Fin.val=JGc_TX2_M2.Hash083.message := by
  simp only [JGc_TX2_M2.Hash083.message,JGc_TX2_M2.Hash083.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast083_0,tail083]
#print axioms numeric083
theorem hash083 : JFp_SHADigest.digest input083=value083 := by
  unfold input083 JFp_SHADigest.digest
  rw [numeric083,JGc_TX2_M2.Hash083.checked]
  rfl
#print axioms hash083
theorem address083 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [38,141,219,157,52,107,217,96,207,231,61,149,2,114,140,112,36,95,207,84,115,187,206,102,196,31,43,157,174,210,54,133]) value071)=input083 := by rfl
#print axioms address083
def tree083 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [38,141,219,157,52,107,217,96,207,231,61,149,2,114,140,112,36,95,207,84,115,187,206,102,196,31,43,157,174,210,54,133])) tree071
theorem root083 : root JFp_SHADigest.digest tree083=value083 := by
  rw [tree083,root,root071]
  exact (congrArg JFp_SHADigest.digest address083).trans hash083
#print axioms root083
theorem shape083 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 54464=tree083 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 54464)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 54464 (by decide),siblings 5 (by decide) 54464 (by decide)]
  rw [shape071 f g inputs siblings]
  rfl
#print axioms shape083
end AspisR1.JGc_TX2_M2Roots
end
