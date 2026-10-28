import NDO_JGf_TX2_M0Level03
import NDO_JGf_TX2_M0W025
import NDO_JGf_TX2_M0W026
import NDO_JGf_TX2_M0W027
import NDO_JGf_TX2_M0W028
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGf_TX2_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input060 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash060.message
def value060 : State := JFp_SHADigest.output JGf_TX2_M0.Hash060.result
theorem cast060_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash060.B00.input).map Fin.val=JGf_TX2_M0.Hash060.B00.input := by rfl
#print axioms cast060_0
theorem tail060 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash060.tail).map Fin.val=JGf_TX2_M0.Hash060.tail := by rfl
#print axioms tail060
theorem numeric060 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash060.message).map Fin.val=JGf_TX2_M0.Hash060.message := by
  simp only [JGf_TX2_M0.Hash060.message,JGf_TX2_M0.Hash060.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast060_0,tail060]
#print axioms numeric060
theorem hash060 : JFp_SHADigest.digest input060=value060 := by
  unfold input060 JFp_SHADigest.digest
  rw [numeric060,JGf_TX2_M0.Hash060.checked]
  rfl
#print axioms hash060
theorem address060 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [228,204,254,67,230,118,0,54,190,87,163,106,56,43,42,151,28,188,38,200,193,86,163,127,232,231,123,161,212,175,50,54]) value048)=input060 := by rfl
#print axioms address060
def tree060 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [228,204,254,67,230,118,0,54,190,87,163,106,56,43,42,151,28,188,38,200,193,86,163,127,232,231,123,161,212,175,50,54])) tree048
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
def input061 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash061.message
def value061 : State := JFp_SHADigest.output JGf_TX2_M0.Hash061.result
theorem cast061_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash061.B00.input).map Fin.val=JGf_TX2_M0.Hash061.B00.input := by rfl
#print axioms cast061_0
theorem tail061 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash061.tail).map Fin.val=JGf_TX2_M0.Hash061.tail := by rfl
#print axioms tail061
theorem numeric061 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash061.message).map Fin.val=JGf_TX2_M0.Hash061.message := by
  simp only [JGf_TX2_M0.Hash061.message,JGf_TX2_M0.Hash061.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast061_0,tail061]
#print axioms numeric061
theorem hash061 : JFp_SHADigest.digest input061=value061 := by
  unfold input061 JFp_SHADigest.digest
  rw [numeric061,JGf_TX2_M0.Hash061.checked]
  rfl
#print axioms hash061
theorem address061 : BinMerkle32Path.nodeInput (children value049 (JGc_TX2_HashBytes.state [207,115,167,13,132,41,194,60,160,60,40,206,138,12,35,141,204,211,242,140,203,61,186,254,156,163,164,14,187,87,101,175]))=input061 := by rfl
#print axioms address061
def tree061 : Tree := .branch tree049 (.supplied (JGc_TX2_HashBytes.state [207,115,167,13,132,41,194,60,160,60,40,206,138,12,35,141,204,211,242,140,203,61,186,254,156,163,164,14,187,87,101,175]))
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
def input062 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash062.message
def value062 : State := JFp_SHADigest.output JGf_TX2_M0.Hash062.result
theorem cast062_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash062.B00.input).map Fin.val=JGf_TX2_M0.Hash062.B00.input := by rfl
#print axioms cast062_0
theorem tail062 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash062.tail).map Fin.val=JGf_TX2_M0.Hash062.tail := by rfl
#print axioms tail062
theorem numeric062 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash062.message).map Fin.val=JGf_TX2_M0.Hash062.message := by
  simp only [JGf_TX2_M0.Hash062.message,JGf_TX2_M0.Hash062.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast062_0,tail062]
#print axioms numeric062
theorem hash062 : JFp_SHADigest.digest input062=value062 := by
  unfold input062 JFp_SHADigest.digest
  rw [numeric062,JGf_TX2_M0.Hash062.checked]
  rfl
#print axioms hash062
theorem address062 : BinMerkle32Path.nodeInput (children value050 (JGc_TX2_HashBytes.state [196,21,137,100,218,94,88,186,109,74,242,215,8,210,222,151,27,167,25,152,3,158,186,75,240,243,57,223,228,226,15,192]))=input062 := by rfl
#print axioms address062
def tree062 : Tree := .branch tree050 (.supplied (JGc_TX2_HashBytes.state [196,21,137,100,218,94,88,186,109,74,242,215,8,210,222,151,27,167,25,152,3,158,186,75,240,243,57,223,228,226,15,192]))
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
def input063 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash063.message
def value063 : State := JFp_SHADigest.output JGf_TX2_M0.Hash063.result
theorem cast063_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash063.B00.input).map Fin.val=JGf_TX2_M0.Hash063.B00.input := by rfl
#print axioms cast063_0
theorem tail063 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash063.tail).map Fin.val=JGf_TX2_M0.Hash063.tail := by rfl
#print axioms tail063
theorem numeric063 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash063.message).map Fin.val=JGf_TX2_M0.Hash063.message := by
  simp only [JGf_TX2_M0.Hash063.message,JGf_TX2_M0.Hash063.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast063_0,tail063]
#print axioms numeric063
theorem hash063 : JFp_SHADigest.digest input063=value063 := by
  unfold input063 JFp_SHADigest.digest
  rw [numeric063,JGf_TX2_M0.Hash063.checked]
  rfl
#print axioms hash063
theorem address063 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [42,50,189,174,210,176,188,91,167,159,114,203,100,46,24,109,47,82,193,175,154,48,183,92,151,32,254,53,100,115,136,86]) value051)=input063 := by rfl
#print axioms address063
def tree063 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [42,50,189,174,210,176,188,91,167,159,114,203,100,46,24,109,47,82,193,175,154,48,183,92,151,32,254,53,100,115,136,86])) tree051
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
def input064 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash064.message
def value064 : State := JFp_SHADigest.output JGf_TX2_M0.Hash064.result
theorem cast064_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash064.B00.input).map Fin.val=JGf_TX2_M0.Hash064.B00.input := by rfl
#print axioms cast064_0
theorem tail064 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash064.tail).map Fin.val=JGf_TX2_M0.Hash064.tail := by rfl
#print axioms tail064
theorem numeric064 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash064.message).map Fin.val=JGf_TX2_M0.Hash064.message := by
  simp only [JGf_TX2_M0.Hash064.message,JGf_TX2_M0.Hash064.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast064_0,tail064]
#print axioms numeric064
theorem hash064 : JFp_SHADigest.digest input064=value064 := by
  unfold input064 JFp_SHADigest.digest
  rw [numeric064,JGf_TX2_M0.Hash064.checked]
  rfl
#print axioms hash064
theorem address064 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [232,43,61,202,89,127,239,178,164,252,172,132,69,194,14,219,129,103,155,228,28,22,223,57,246,29,115,99,154,209,212,142]) value052)=input064 := by rfl
#print axioms address064
def tree064 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [232,43,61,202,89,127,239,178,164,252,172,132,69,194,14,219,129,103,155,228,28,22,223,57,246,29,115,99,154,209,212,142])) tree052
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
def input065 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash065.message
def value065 : State := JFp_SHADigest.output JGf_TX2_M0.Hash065.result
theorem cast065_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash065.B00.input).map Fin.val=JGf_TX2_M0.Hash065.B00.input := by rfl
#print axioms cast065_0
theorem tail065 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash065.tail).map Fin.val=JGf_TX2_M0.Hash065.tail := by rfl
#print axioms tail065
theorem numeric065 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash065.message).map Fin.val=JGf_TX2_M0.Hash065.message := by
  simp only [JGf_TX2_M0.Hash065.message,JGf_TX2_M0.Hash065.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast065_0,tail065]
#print axioms numeric065
theorem hash065 : JFp_SHADigest.digest input065=value065 := by
  unfold input065 JFp_SHADigest.digest
  rw [numeric065,JGf_TX2_M0.Hash065.checked]
  rfl
#print axioms hash065
theorem address065 : BinMerkle32Path.nodeInput (children value053 (JGc_TX2_HashBytes.state [181,120,160,88,189,222,107,181,96,244,28,81,25,140,180,150,175,87,237,9,203,148,91,204,220,21,198,105,103,35,96,138]))=input065 := by rfl
#print axioms address065
def tree065 : Tree := .branch tree053 (.supplied (JGc_TX2_HashBytes.state [181,120,160,88,189,222,107,181,96,244,28,81,25,140,180,150,175,87,237,9,203,148,91,204,220,21,198,105,103,35,96,138]))
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
def input066 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash066.message
def value066 : State := JFp_SHADigest.output JGf_TX2_M0.Hash066.result
theorem cast066_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash066.B00.input).map Fin.val=JGf_TX2_M0.Hash066.B00.input := by rfl
#print axioms cast066_0
theorem tail066 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash066.tail).map Fin.val=JGf_TX2_M0.Hash066.tail := by rfl
#print axioms tail066
theorem numeric066 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash066.message).map Fin.val=JGf_TX2_M0.Hash066.message := by
  simp only [JGf_TX2_M0.Hash066.message,JGf_TX2_M0.Hash066.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast066_0,tail066]
#print axioms numeric066
theorem hash066 : JFp_SHADigest.digest input066=value066 := by
  unfold input066 JFp_SHADigest.digest
  rw [numeric066,JGf_TX2_M0.Hash066.checked]
  rfl
#print axioms hash066
theorem address066 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [74,79,195,118,176,12,148,193,77,27,85,13,238,87,14,156,121,19,122,222,225,237,101,211,139,37,137,146,47,23,186,28]) value054)=input066 := by rfl
#print axioms address066
def tree066 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [74,79,195,118,176,12,148,193,77,27,85,13,238,87,14,156,121,19,122,222,225,237,101,211,139,37,137,146,47,23,186,28])) tree054
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
def input067 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash067.message
def value067 : State := JFp_SHADigest.output JGf_TX2_M0.Hash067.result
theorem cast067_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash067.B00.input).map Fin.val=JGf_TX2_M0.Hash067.B00.input := by rfl
#print axioms cast067_0
theorem tail067 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash067.tail).map Fin.val=JGf_TX2_M0.Hash067.tail := by rfl
#print axioms tail067
theorem numeric067 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash067.message).map Fin.val=JGf_TX2_M0.Hash067.message := by
  simp only [JGf_TX2_M0.Hash067.message,JGf_TX2_M0.Hash067.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast067_0,tail067]
#print axioms numeric067
theorem hash067 : JFp_SHADigest.digest input067=value067 := by
  unfold input067 JFp_SHADigest.digest
  rw [numeric067,JGf_TX2_M0.Hash067.checked]
  rfl
#print axioms hash067
theorem address067 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [236,71,221,192,75,164,235,237,179,16,37,106,61,161,6,91,218,242,8,30,241,210,83,14,203,253,187,56,201,63,139,36]) value055)=input067 := by rfl
#print axioms address067
def tree067 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [236,71,221,192,75,164,235,237,179,16,37,106,61,161,6,91,218,242,8,30,241,210,83,14,203,253,187,56,201,63,139,36])) tree055
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
def input068 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash068.message
def value068 : State := JFp_SHADigest.output JGf_TX2_M0.Hash068.result
theorem cast068_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash068.B00.input).map Fin.val=JGf_TX2_M0.Hash068.B00.input := by rfl
#print axioms cast068_0
theorem tail068 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash068.tail).map Fin.val=JGf_TX2_M0.Hash068.tail := by rfl
#print axioms tail068
theorem numeric068 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash068.message).map Fin.val=JGf_TX2_M0.Hash068.message := by
  simp only [JGf_TX2_M0.Hash068.message,JGf_TX2_M0.Hash068.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast068_0,tail068]
#print axioms numeric068
theorem hash068 : JFp_SHADigest.digest input068=value068 := by
  unfold input068 JFp_SHADigest.digest
  rw [numeric068,JGf_TX2_M0.Hash068.checked]
  rfl
#print axioms hash068
theorem address068 : BinMerkle32Path.nodeInput (children value056 (JGc_TX2_HashBytes.state [78,250,7,72,16,216,71,74,26,234,2,9,118,165,33,43,11,133,50,39,185,77,226,223,198,161,69,135,218,121,178,32]))=input068 := by rfl
#print axioms address068
def tree068 : Tree := .branch tree056 (.supplied (JGc_TX2_HashBytes.state [78,250,7,72,16,216,71,74,26,234,2,9,118,165,33,43,11,133,50,39,185,77,226,223,198,161,69,135,218,121,178,32]))
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
def input069 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash069.message
def value069 : State := JFp_SHADigest.output JGf_TX2_M0.Hash069.result
theorem cast069_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash069.B00.input).map Fin.val=JGf_TX2_M0.Hash069.B00.input := by rfl
#print axioms cast069_0
theorem tail069 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash069.tail).map Fin.val=JGf_TX2_M0.Hash069.tail := by rfl
#print axioms tail069
theorem numeric069 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash069.message).map Fin.val=JGf_TX2_M0.Hash069.message := by
  simp only [JGf_TX2_M0.Hash069.message,JGf_TX2_M0.Hash069.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast069_0,tail069]
#print axioms numeric069
theorem hash069 : JFp_SHADigest.digest input069=value069 := by
  unfold input069 JFp_SHADigest.digest
  rw [numeric069,JGf_TX2_M0.Hash069.checked]
  rfl
#print axioms hash069
theorem address069 : BinMerkle32Path.nodeInput (children value057 (JGc_TX2_HashBytes.state [255,14,120,76,55,183,28,95,232,11,35,33,39,194,85,237,44,16,236,200,201,154,67,223,204,249,162,40,68,238,98,36]))=input069 := by rfl
#print axioms address069
def tree069 : Tree := .branch tree057 (.supplied (JGc_TX2_HashBytes.state [255,14,120,76,55,183,28,95,232,11,35,33,39,194,85,237,44,16,236,200,201,154,67,223,204,249,162,40,68,238,98,36]))
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
def input070 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash070.message
def value070 : State := JFp_SHADigest.output JGf_TX2_M0.Hash070.result
theorem cast070_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash070.B00.input).map Fin.val=JGf_TX2_M0.Hash070.B00.input := by rfl
#print axioms cast070_0
theorem tail070 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash070.tail).map Fin.val=JGf_TX2_M0.Hash070.tail := by rfl
#print axioms tail070
theorem numeric070 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash070.message).map Fin.val=JGf_TX2_M0.Hash070.message := by
  simp only [JGf_TX2_M0.Hash070.message,JGf_TX2_M0.Hash070.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast070_0,tail070]
#print axioms numeric070
theorem hash070 : JFp_SHADigest.digest input070=value070 := by
  unfold input070 JFp_SHADigest.digest
  rw [numeric070,JGf_TX2_M0.Hash070.checked]
  rfl
#print axioms hash070
theorem address070 : BinMerkle32Path.nodeInput (children value058 (JGc_TX2_HashBytes.state [12,1,102,41,19,231,98,113,104,116,64,27,50,45,147,198,229,182,251,242,122,40,57,213,164,182,204,107,63,233,49,141]))=input070 := by rfl
#print axioms address070
def tree070 : Tree := .branch tree058 (.supplied (JGc_TX2_HashBytes.state [12,1,102,41,19,231,98,113,104,116,64,27,50,45,147,198,229,182,251,242,122,40,57,213,164,182,204,107,63,233,49,141]))
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
def input071 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash071.message
def value071 : State := JFp_SHADigest.output JGf_TX2_M0.Hash071.result
theorem cast071_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash071.B00.input).map Fin.val=JGf_TX2_M0.Hash071.B00.input := by rfl
#print axioms cast071_0
theorem tail071 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash071.tail).map Fin.val=JGf_TX2_M0.Hash071.tail := by rfl
#print axioms tail071
theorem numeric071 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash071.message).map Fin.val=JGf_TX2_M0.Hash071.message := by
  simp only [JGf_TX2_M0.Hash071.message,JGf_TX2_M0.Hash071.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast071_0,tail071]
#print axioms numeric071
theorem hash071 : JFp_SHADigest.digest input071=value071 := by
  unfold input071 JFp_SHADigest.digest
  rw [numeric071,JGf_TX2_M0.Hash071.checked]
  rfl
#print axioms hash071
theorem address071 : BinMerkle32Path.nodeInput (children value059 (JGc_TX2_HashBytes.state [99,115,64,61,21,23,53,5,180,98,72,197,133,15,10,221,82,234,135,59,189,171,207,255,34,189,101,184,214,214,53,0]))=input071 := by rfl
#print axioms address071
def tree071 : Tree := .branch tree059 (.supplied (JGc_TX2_HashBytes.state [99,115,64,61,21,23,53,5,180,98,72,197,133,15,10,221,82,234,135,59,189,171,207,255,34,189,101,184,214,214,53,0]))
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
end AspisR1.JGf_TX2_M0Roots
end
