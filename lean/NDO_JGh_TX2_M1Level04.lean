import NDO_JGh_TX2_M1Level03
import NDO_JGh_TX2_M1W016
import NDO_JGh_TX2_M1W017
import NDO_JGh_TX2_M1W018
import NDO_JGh_TX2_M1W019
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input060 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash060.message
def value060 : State := JFp_SHADigest.output JGh_TX2_M1.Hash060.result
theorem cast060_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash060.B00.input).map Fin.val=JGh_TX2_M1.Hash060.B00.input := by rfl
#print axioms cast060_0
theorem tail060 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash060.tail).map Fin.val=JGh_TX2_M1.Hash060.tail := by rfl
#print axioms tail060
theorem numeric060 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash060.message).map Fin.val=JGh_TX2_M1.Hash060.message := by
  simp only [JGh_TX2_M1.Hash060.message,JGh_TX2_M1.Hash060.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast060_0,tail060]
#print axioms numeric060
theorem hash060 : JFp_SHADigest.digest input060=value060 := by
  unfold input060 JFp_SHADigest.digest
  rw [numeric060,JGh_TX2_M1.Hash060.checked]
  rfl
#print axioms hash060
theorem address060 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [91,145,122,197,62,9,154,119,198,228,207,125,51,231,239,131,45,185,107,138,118,76,50,80,150,224,70,82,116,167,73,251]) value048)=input060 := by rfl
#print axioms address060
def tree060 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [91,145,122,197,62,9,154,119,198,228,207,125,51,231,239,131,45,185,107,138,118,76,50,80,150,224,70,82,116,167,73,251])) tree048
theorem root060 : root JFp_SHADigest.digest tree060=value060 := by
  rw [tree060,root,root048]
  exact (congrArg JFp_SHADigest.digest address060).trans hash060
#print axioms root060
theorem shape060 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 14272=tree060 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 14272)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 14272 (by decide),siblings 4 (by decide) 14272 (by decide)]
  rw [shape048 f g inputs siblings]
  rfl
#print axioms shape060
def input061 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash061.message
def value061 : State := JFp_SHADigest.output JGh_TX2_M1.Hash061.result
theorem cast061_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash061.B00.input).map Fin.val=JGh_TX2_M1.Hash061.B00.input := by rfl
#print axioms cast061_0
theorem tail061 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash061.tail).map Fin.val=JGh_TX2_M1.Hash061.tail := by rfl
#print axioms tail061
theorem numeric061 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash061.message).map Fin.val=JGh_TX2_M1.Hash061.message := by
  simp only [JGh_TX2_M1.Hash061.message,JGh_TX2_M1.Hash061.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast061_0,tail061]
#print axioms numeric061
theorem hash061 : JFp_SHADigest.digest input061=value061 := by
  unfold input061 JFp_SHADigest.digest
  rw [numeric061,JGh_TX2_M1.Hash061.checked]
  rfl
#print axioms hash061
theorem address061 : BinMerkle32Path.nodeInput (children value049 (JGc_TX2_HashBytes.state [90,140,213,237,59,84,110,8,10,122,97,222,95,2,126,163,159,44,250,139,169,14,158,92,31,86,13,238,246,127,219,227]))=input061 := by rfl
#print axioms address061
def tree061 : Tree := .branch tree049 (.supplied (JGc_TX2_HashBytes.state [90,140,213,237,59,84,110,8,10,122,97,222,95,2,126,163,159,44,250,139,169,14,158,92,31,86,13,238,246,127,219,227]))
theorem root061 : root JFp_SHADigest.digest tree061=value061 := by
  rw [tree061,root,root049]
  exact (congrArg JFp_SHADigest.digest address061).trans hash061
#print axioms root061
theorem shape061 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 21248=tree061 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 21248)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape049 f g inputs siblings]
  rw [unoccupied f g 4 21264 (by decide),siblings 4 (by decide) 21264 (by decide)]
  rfl
#print axioms shape061
def input062 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash062.message
def value062 : State := JFp_SHADigest.output JGh_TX2_M1.Hash062.result
theorem cast062_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash062.B00.input).map Fin.val=JGh_TX2_M1.Hash062.B00.input := by rfl
#print axioms cast062_0
theorem tail062 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash062.tail).map Fin.val=JGh_TX2_M1.Hash062.tail := by rfl
#print axioms tail062
theorem numeric062 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash062.message).map Fin.val=JGh_TX2_M1.Hash062.message := by
  simp only [JGh_TX2_M1.Hash062.message,JGh_TX2_M1.Hash062.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast062_0,tail062]
#print axioms numeric062
theorem hash062 : JFp_SHADigest.digest input062=value062 := by
  unfold input062 JFp_SHADigest.digest
  rw [numeric062,JGh_TX2_M1.Hash062.checked]
  rfl
#print axioms hash062
theorem address062 : BinMerkle32Path.nodeInput (children value050 (JGc_TX2_HashBytes.state [137,141,84,108,125,109,191,204,48,143,71,88,73,187,152,220,129,207,202,11,5,41,190,123,105,166,56,164,25,14,111,64]))=input062 := by rfl
#print axioms address062
def tree062 : Tree := .branch tree050 (.supplied (JGc_TX2_HashBytes.state [137,141,84,108,125,109,191,204,48,143,71,88,73,187,152,220,129,207,202,11,5,41,190,123,105,166,56,164,25,14,111,64]))
theorem root062 : root JFp_SHADigest.digest tree062=value062 := by
  rw [tree062,root,root050]
  exact (congrArg JFp_SHADigest.digest address062).trans hash062
#print axioms root062
theorem shape062 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 42144=tree062 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 42144)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape050 f g inputs siblings]
  rw [unoccupied f g 4 42160 (by decide),siblings 4 (by decide) 42160 (by decide)]
  rfl
#print axioms shape062
def input063 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash063.message
def value063 : State := JFp_SHADigest.output JGh_TX2_M1.Hash063.result
theorem cast063_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash063.B00.input).map Fin.val=JGh_TX2_M1.Hash063.B00.input := by rfl
#print axioms cast063_0
theorem tail063 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash063.tail).map Fin.val=JGh_TX2_M1.Hash063.tail := by rfl
#print axioms tail063
theorem numeric063 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash063.message).map Fin.val=JGh_TX2_M1.Hash063.message := by
  simp only [JGh_TX2_M1.Hash063.message,JGh_TX2_M1.Hash063.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast063_0,tail063]
#print axioms numeric063
theorem hash063 : JFp_SHADigest.digest input063=value063 := by
  unfold input063 JFp_SHADigest.digest
  rw [numeric063,JGh_TX2_M1.Hash063.checked]
  rfl
#print axioms hash063
theorem address063 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [162,109,78,218,105,211,135,69,9,239,254,91,237,250,215,233,43,236,40,70,170,227,33,222,85,125,177,228,237,172,133,212]) value051)=input063 := by rfl
#print axioms address063
def tree063 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [162,109,78,218,105,211,135,69,9,239,254,91,237,250,215,233,43,236,40,70,170,227,33,222,85,125,177,228,237,172,133,212])) tree051
theorem root063 : root JFp_SHADigest.digest tree063=value063 := by
  rw [tree063,root,root051]
  exact (congrArg JFp_SHADigest.digest address063).trans hash063
#print axioms root063
theorem shape063 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 55360=tree063 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 55360)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 55360 (by decide),siblings 4 (by decide) 55360 (by decide)]
  rw [shape051 f g inputs siblings]
  rfl
#print axioms shape063
def input064 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash064.message
def value064 : State := JFp_SHADigest.output JGh_TX2_M1.Hash064.result
theorem cast064_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash064.B00.input).map Fin.val=JGh_TX2_M1.Hash064.B00.input := by rfl
#print axioms cast064_0
theorem tail064 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash064.tail).map Fin.val=JGh_TX2_M1.Hash064.tail := by rfl
#print axioms tail064
theorem numeric064 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash064.message).map Fin.val=JGh_TX2_M1.Hash064.message := by
  simp only [JGh_TX2_M1.Hash064.message,JGh_TX2_M1.Hash064.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast064_0,tail064]
#print axioms numeric064
theorem hash064 : JFp_SHADigest.digest input064=value064 := by
  unfold input064 JFp_SHADigest.digest
  rw [numeric064,JGh_TX2_M1.Hash064.checked]
  rfl
#print axioms hash064
theorem address064 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [3,177,75,35,72,150,141,238,11,48,28,245,55,173,235,70,132,215,65,116,153,151,30,3,133,217,158,241,55,198,165,163]) value052)=input064 := by rfl
#print axioms address064
def tree064 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [3,177,75,35,72,150,141,238,11,48,28,245,55,173,235,70,132,215,65,116,153,151,30,3,133,217,158,241,55,198,165,163])) tree052
theorem root064 : root JFp_SHADigest.digest tree064=value064 := by
  rw [tree064,root,root052]
  exact (congrArg JFp_SHADigest.digest address064).trans hash064
#print axioms root064
theorem shape064 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 63840=tree064 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 63840)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 63840 (by decide),siblings 4 (by decide) 63840 (by decide)]
  rw [shape052 f g inputs siblings]
  rfl
#print axioms shape064
def input065 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash065.message
def value065 : State := JFp_SHADigest.output JGh_TX2_M1.Hash065.result
theorem cast065_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash065.B00.input).map Fin.val=JGh_TX2_M1.Hash065.B00.input := by rfl
#print axioms cast065_0
theorem tail065 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash065.tail).map Fin.val=JGh_TX2_M1.Hash065.tail := by rfl
#print axioms tail065
theorem numeric065 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash065.message).map Fin.val=JGh_TX2_M1.Hash065.message := by
  simp only [JGh_TX2_M1.Hash065.message,JGh_TX2_M1.Hash065.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast065_0,tail065]
#print axioms numeric065
theorem hash065 : JFp_SHADigest.digest input065=value065 := by
  unfold input065 JFp_SHADigest.digest
  rw [numeric065,JGh_TX2_M1.Hash065.checked]
  rfl
#print axioms hash065
theorem address065 : BinMerkle32Path.nodeInput (children value053 (JGc_TX2_HashBytes.state [7,71,230,53,233,46,37,77,184,75,193,88,35,33,68,235,51,159,237,177,94,144,173,223,233,16,106,87,161,58,177,105]))=input065 := by rfl
#print axioms address065
def tree065 : Tree := .branch tree053 (.supplied (JGc_TX2_HashBytes.state [7,71,230,53,233,46,37,77,184,75,193,88,35,33,68,235,51,159,237,177,94,144,173,223,233,16,106,87,161,58,177,105]))
theorem root065 : root JFp_SHADigest.digest tree065=value065 := by
  rw [tree065,root,root053]
  exact (congrArg JFp_SHADigest.digest address065).trans hash065
#print axioms root065
theorem shape065 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 132352=tree065 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 132352)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape053 f g inputs siblings]
  rw [unoccupied f g 4 132368 (by decide),siblings 4 (by decide) 132368 (by decide)]
  rfl
#print axioms shape065
def input066 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash066.message
def value066 : State := JFp_SHADigest.output JGh_TX2_M1.Hash066.result
theorem cast066_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash066.B00.input).map Fin.val=JGh_TX2_M1.Hash066.B00.input := by rfl
#print axioms cast066_0
theorem tail066 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash066.tail).map Fin.val=JGh_TX2_M1.Hash066.tail := by rfl
#print axioms tail066
theorem numeric066 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash066.message).map Fin.val=JGh_TX2_M1.Hash066.message := by
  simp only [JGh_TX2_M1.Hash066.message,JGh_TX2_M1.Hash066.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast066_0,tail066]
#print axioms numeric066
theorem hash066 : JFp_SHADigest.digest input066=value066 := by
  unfold input066 JFp_SHADigest.digest
  rw [numeric066,JGh_TX2_M1.Hash066.checked]
  rfl
#print axioms hash066
theorem address066 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [100,208,206,178,211,104,93,209,84,229,201,209,70,62,177,3,162,49,77,164,166,198,88,39,148,11,159,214,254,213,150,193]) value054)=input066 := by rfl
#print axioms address066
def tree066 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [100,208,206,178,211,104,93,209,84,229,201,209,70,62,177,3,162,49,77,164,166,198,88,39,148,11,159,214,254,213,150,193])) tree054
theorem root066 : root JFp_SHADigest.digest tree066=value066 := by
  rw [tree066,root,root054]
  exact (congrArg JFp_SHADigest.digest address066).trans hash066
#print axioms root066
theorem shape066 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 149600=tree066 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 149600)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 149600 (by decide),siblings 4 (by decide) 149600 (by decide)]
  rw [shape054 f g inputs siblings]
  rfl
#print axioms shape066
def input067 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash067.message
def value067 : State := JFp_SHADigest.output JGh_TX2_M1.Hash067.result
theorem cast067_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash067.B00.input).map Fin.val=JGh_TX2_M1.Hash067.B00.input := by rfl
#print axioms cast067_0
theorem tail067 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash067.tail).map Fin.val=JGh_TX2_M1.Hash067.tail := by rfl
#print axioms tail067
theorem numeric067 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash067.message).map Fin.val=JGh_TX2_M1.Hash067.message := by
  simp only [JGh_TX2_M1.Hash067.message,JGh_TX2_M1.Hash067.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast067_0,tail067]
#print axioms numeric067
theorem hash067 : JFp_SHADigest.digest input067=value067 := by
  unfold input067 JFp_SHADigest.digest
  rw [numeric067,JGh_TX2_M1.Hash067.checked]
  rfl
#print axioms hash067
theorem address067 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [204,138,128,220,43,110,243,42,112,197,80,64,180,242,245,200,51,70,22,140,85,234,163,241,149,58,99,176,37,185,89,70]) value055)=input067 := by rfl
#print axioms address067
def tree067 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [204,138,128,220,43,110,243,42,112,197,80,64,180,242,245,200,51,70,22,140,85,234,163,241,149,58,99,176,37,185,89,70])) tree055
theorem root067 : root JFp_SHADigest.digest tree067=value067 := by
  rw [tree067,root,root055]
  exact (congrArg JFp_SHADigest.digest address067).trans hash067
#print axioms root067
theorem shape067 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 166144=tree067 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 166144)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 166144 (by decide),siblings 4 (by decide) 166144 (by decide)]
  rw [shape055 f g inputs siblings]
  rfl
#print axioms shape067
def input068 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash068.message
def value068 : State := JFp_SHADigest.output JGh_TX2_M1.Hash068.result
theorem cast068_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash068.B00.input).map Fin.val=JGh_TX2_M1.Hash068.B00.input := by rfl
#print axioms cast068_0
theorem tail068 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash068.tail).map Fin.val=JGh_TX2_M1.Hash068.tail := by rfl
#print axioms tail068
theorem numeric068 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash068.message).map Fin.val=JGh_TX2_M1.Hash068.message := by
  simp only [JGh_TX2_M1.Hash068.message,JGh_TX2_M1.Hash068.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast068_0,tail068]
#print axioms numeric068
theorem hash068 : JFp_SHADigest.digest input068=value068 := by
  unfold input068 JFp_SHADigest.digest
  rw [numeric068,JGh_TX2_M1.Hash068.checked]
  rfl
#print axioms hash068
theorem address068 : BinMerkle32Path.nodeInput (children value056 (JGc_TX2_HashBytes.state [100,75,61,102,95,187,38,76,72,111,199,89,100,106,122,95,239,187,212,134,17,10,153,71,129,234,125,216,197,105,64,123]))=input068 := by rfl
#print axioms address068
def tree068 : Tree := .branch tree056 (.supplied (JGc_TX2_HashBytes.state [100,75,61,102,95,187,38,76,72,111,199,89,100,106,122,95,239,187,212,134,17,10,153,71,129,234,125,216,197,105,64,123]))
theorem root068 : root JFp_SHADigest.digest tree068=value068 := by
  rw [tree068,root,root056]
  exact (congrArg JFp_SHADigest.digest address068).trans hash068
#print axioms root068
theorem shape068 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 178080=tree068 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 178080)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape056 f g inputs siblings]
  rw [unoccupied f g 4 178096 (by decide),siblings 4 (by decide) 178096 (by decide)]
  rfl
#print axioms shape068
def input069 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash069.message
def value069 : State := JFp_SHADigest.output JGh_TX2_M1.Hash069.result
theorem cast069_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash069.B00.input).map Fin.val=JGh_TX2_M1.Hash069.B00.input := by rfl
#print axioms cast069_0
theorem tail069 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash069.tail).map Fin.val=JGh_TX2_M1.Hash069.tail := by rfl
#print axioms tail069
theorem numeric069 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash069.message).map Fin.val=JGh_TX2_M1.Hash069.message := by
  simp only [JGh_TX2_M1.Hash069.message,JGh_TX2_M1.Hash069.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast069_0,tail069]
#print axioms numeric069
theorem hash069 : JFp_SHADigest.digest input069=value069 := by
  unfold input069 JFp_SHADigest.digest
  rw [numeric069,JGh_TX2_M1.Hash069.checked]
  rfl
#print axioms hash069
theorem address069 : BinMerkle32Path.nodeInput (children value057 (JGc_TX2_HashBytes.state [192,203,122,95,19,169,3,216,182,71,243,115,97,181,77,86,174,198,18,233,61,203,165,112,193,236,213,83,40,40,150,3]))=input069 := by rfl
#print axioms address069
def tree069 : Tree := .branch tree057 (.supplied (JGc_TX2_HashBytes.state [192,203,122,95,19,169,3,216,182,71,243,115,97,181,77,86,174,198,18,233,61,203,165,112,193,236,213,83,40,40,150,3]))
theorem root069 : root JFp_SHADigest.digest tree069=value069 := by
  rw [tree069,root,root057]
  exact (congrArg JFp_SHADigest.digest address069).trans hash069
#print axioms root069
theorem shape069 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 179616=tree069 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 179616)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape057 f g inputs siblings]
  rw [unoccupied f g 4 179632 (by decide),siblings 4 (by decide) 179632 (by decide)]
  rfl
#print axioms shape069
def input070 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash070.message
def value070 : State := JFp_SHADigest.output JGh_TX2_M1.Hash070.result
theorem cast070_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash070.B00.input).map Fin.val=JGh_TX2_M1.Hash070.B00.input := by rfl
#print axioms cast070_0
theorem tail070 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash070.tail).map Fin.val=JGh_TX2_M1.Hash070.tail := by rfl
#print axioms tail070
theorem numeric070 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash070.message).map Fin.val=JGh_TX2_M1.Hash070.message := by
  simp only [JGh_TX2_M1.Hash070.message,JGh_TX2_M1.Hash070.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast070_0,tail070]
#print axioms numeric070
theorem hash070 : JFp_SHADigest.digest input070=value070 := by
  unfold input070 JFp_SHADigest.digest
  rw [numeric070,JGh_TX2_M1.Hash070.checked]
  rfl
#print axioms hash070
theorem address070 : BinMerkle32Path.nodeInput (children value058 (JGc_TX2_HashBytes.state [49,2,133,245,85,142,142,39,72,171,94,251,203,163,145,100,127,163,255,58,90,160,38,46,170,45,166,44,55,55,154,112]))=input070 := by rfl
#print axioms address070
def tree070 : Tree := .branch tree058 (.supplied (JGc_TX2_HashBytes.state [49,2,133,245,85,142,142,39,72,171,94,251,203,163,145,100,127,163,255,58,90,160,38,46,170,45,166,44,55,55,154,112]))
theorem root070 : root JFp_SHADigest.digest tree070=value070 := by
  rw [tree070,root,root058]
  exact (congrArg JFp_SHADigest.digest address070).trans hash070
#print axioms root070
theorem shape070 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 185632=tree070 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 185632)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape058 f g inputs siblings]
  rw [unoccupied f g 4 185648 (by decide),siblings 4 (by decide) 185648 (by decide)]
  rfl
#print axioms shape070
def input071 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash071.message
def value071 : State := JFp_SHADigest.output JGh_TX2_M1.Hash071.result
theorem cast071_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash071.B00.input).map Fin.val=JGh_TX2_M1.Hash071.B00.input := by rfl
#print axioms cast071_0
theorem tail071 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash071.tail).map Fin.val=JGh_TX2_M1.Hash071.tail := by rfl
#print axioms tail071
theorem numeric071 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash071.message).map Fin.val=JGh_TX2_M1.Hash071.message := by
  simp only [JGh_TX2_M1.Hash071.message,JGh_TX2_M1.Hash071.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast071_0,tail071]
#print axioms numeric071
theorem hash071 : JFp_SHADigest.digest input071=value071 := by
  unfold input071 JFp_SHADigest.digest
  rw [numeric071,JGh_TX2_M1.Hash071.checked]
  rfl
#print axioms hash071
theorem address071 : BinMerkle32Path.nodeInput (children value059 (JGc_TX2_HashBytes.state [37,136,167,16,131,171,200,73,63,75,48,101,141,75,3,143,138,38,137,9,54,123,113,130,73,175,89,214,32,212,174,7]))=input071 := by rfl
#print axioms address071
def tree071 : Tree := .branch tree059 (.supplied (JGc_TX2_HashBytes.state [37,136,167,16,131,171,200,73,63,75,48,101,141,75,3,143,138,38,137,9,54,123,113,130,73,175,89,214,32,212,174,7]))
theorem root071 : root JFp_SHADigest.digest tree071=value071 := by
  rw [tree071,root,root059]
  exact (congrArg JFp_SHADigest.digest address071).trans hash071
#print axioms root071
theorem shape071 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 218080=tree071 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 218080)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape059 f g inputs siblings]
  rw [unoccupied f g 4 218096 (by decide),siblings 4 (by decide) 218096 (by decide)]
  rfl
#print axioms shape071
end AspisR1.JGh_TX2_M1Roots
end
