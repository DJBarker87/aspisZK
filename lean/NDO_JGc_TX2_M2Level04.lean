import NDO_JGc_TX2_M2Level03
import NDO_JGc_TX2_M2H060
import NDO_JGc_TX2_M2H064
import NDO_JGc_TX2_M2H068
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input060 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash060.message
def value060 : State := JFp_SHADigest.output JGc_TX2_M2.Hash060.result
theorem cast060_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash060.B00.input).map Fin.val=JGc_TX2_M2.Hash060.B00.input := by rfl
#print axioms cast060_0
theorem tail060 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash060.tail).map Fin.val=JGc_TX2_M2.Hash060.tail := by rfl
#print axioms tail060
theorem numeric060 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash060.message).map Fin.val=JGc_TX2_M2.Hash060.message := by
  simp only [JGc_TX2_M2.Hash060.message,JGc_TX2_M2.Hash060.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast060_0,tail060]
#print axioms numeric060
theorem hash060 : JFp_SHADigest.digest input060=value060 := by
  unfold input060 JFp_SHADigest.digest
  rw [numeric060,JGc_TX2_M2.Hash060.checked]
  rfl
#print axioms hash060
theorem address060 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [247,100,236,140,76,132,72,103,230,182,217,150,219,250,252,178,17,5,14,17,110,183,246,163,82,227,58,184,169,136,239,158]) value048)=input060 := by rfl
#print axioms address060
def tree060 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [247,100,236,140,76,132,72,103,230,182,217,150,219,250,252,178,17,5,14,17,110,183,246,163,82,227,58,184,169,136,239,158])) tree048
theorem root060 : root JFp_SHADigest.digest tree060=value060 := by
  rw [tree060,root,root048]
  exact (congrArg JFp_SHADigest.digest address060).trans hash060
#print axioms root060
theorem shape060 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 3552=tree060 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 3552)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 3552 (by decide),siblings 4 (by decide) 3552 (by decide)]
  rw [shape048 f g inputs siblings]
  rfl
#print axioms shape060
def input061 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash061.message
def value061 : State := JFp_SHADigest.output JGc_TX2_M2.Hash061.result
theorem cast061_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash061.B00.input).map Fin.val=JGc_TX2_M2.Hash061.B00.input := by rfl
#print axioms cast061_0
theorem tail061 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash061.tail).map Fin.val=JGc_TX2_M2.Hash061.tail := by rfl
#print axioms tail061
theorem numeric061 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash061.message).map Fin.val=JGc_TX2_M2.Hash061.message := by
  simp only [JGc_TX2_M2.Hash061.message,JGc_TX2_M2.Hash061.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast061_0,tail061]
#print axioms numeric061
theorem hash061 : JFp_SHADigest.digest input061=value061 := by
  unfold input061 JFp_SHADigest.digest
  rw [numeric061,JGc_TX2_M2.Hash061.checked]
  rfl
#print axioms hash061
theorem address061 : BinMerkle32Path.nodeInput (children value049 (JGc_TX2_HashBytes.state [175,214,251,74,56,98,215,165,147,235,8,16,138,10,129,140,104,24,70,95,255,124,239,8,248,145,212,161,195,57,205,112]))=input061 := by rfl
#print axioms address061
def tree061 : Tree := .branch tree049 (.supplied (JGc_TX2_HashBytes.state [175,214,251,74,56,98,215,165,147,235,8,16,138,10,129,140,104,24,70,95,255,124,239,8,248,145,212,161,195,57,205,112]))
theorem root061 : root JFp_SHADigest.digest tree061=value061 := by
  rw [tree061,root,root049]
  exact (congrArg JFp_SHADigest.digest address061).trans hash061
#print axioms root061
theorem shape061 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 5312=tree061 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 5312)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape049 f g inputs siblings]
  rw [unoccupied f g 4 5328 (by decide),siblings 4 (by decide) 5328 (by decide)]
  rfl
#print axioms shape061
def input062 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash062.message
def value062 : State := JFp_SHADigest.output JGc_TX2_M2.Hash062.result
theorem cast062_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash062.B00.input).map Fin.val=JGc_TX2_M2.Hash062.B00.input := by rfl
#print axioms cast062_0
theorem tail062 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash062.tail).map Fin.val=JGc_TX2_M2.Hash062.tail := by rfl
#print axioms tail062
theorem numeric062 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash062.message).map Fin.val=JGc_TX2_M2.Hash062.message := by
  simp only [JGc_TX2_M2.Hash062.message,JGc_TX2_M2.Hash062.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast062_0,tail062]
#print axioms numeric062
theorem hash062 : JFp_SHADigest.digest input062=value062 := by
  unfold input062 JFp_SHADigest.digest
  rw [numeric062,JGc_TX2_M2.Hash062.checked]
  rfl
#print axioms hash062
theorem address062 : BinMerkle32Path.nodeInput (children value050 (JGc_TX2_HashBytes.state [220,217,136,94,221,196,15,137,224,208,19,77,144,180,208,70,235,172,5,103,9,159,38,30,58,148,186,113,174,237,185,9]))=input062 := by rfl
#print axioms address062
def tree062 : Tree := .branch tree050 (.supplied (JGc_TX2_HashBytes.state [220,217,136,94,221,196,15,137,224,208,19,77,144,180,208,70,235,172,5,103,9,159,38,30,58,148,186,113,174,237,185,9]))
theorem root062 : root JFp_SHADigest.digest tree062=value062 := by
  rw [tree062,root,root050]
  exact (congrArg JFp_SHADigest.digest address062).trans hash062
#print axioms root062
theorem shape062 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 10528=tree062 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 10528)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape050 f g inputs siblings]
  rw [unoccupied f g 4 10544 (by decide),siblings 4 (by decide) 10544 (by decide)]
  rfl
#print axioms shape062
def input063 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash063.message
def value063 : State := JFp_SHADigest.output JGc_TX2_M2.Hash063.result
theorem cast063_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash063.B00.input).map Fin.val=JGc_TX2_M2.Hash063.B00.input := by rfl
#print axioms cast063_0
theorem tail063 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash063.tail).map Fin.val=JGc_TX2_M2.Hash063.tail := by rfl
#print axioms tail063
theorem numeric063 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash063.message).map Fin.val=JGc_TX2_M2.Hash063.message := by
  simp only [JGc_TX2_M2.Hash063.message,JGc_TX2_M2.Hash063.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast063_0,tail063]
#print axioms numeric063
theorem hash063 : JFp_SHADigest.digest input063=value063 := by
  unfold input063 JFp_SHADigest.digest
  rw [numeric063,JGc_TX2_M2.Hash063.checked]
  rfl
#print axioms hash063
theorem address063 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [240,86,123,40,144,253,125,166,16,245,72,190,206,15,158,196,221,57,211,112,69,169,129,144,132,13,152,226,128,228,247,41]) value051)=input063 := by rfl
#print axioms address063
def tree063 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [240,86,123,40,144,253,125,166,16,245,72,190,206,15,158,196,221,57,211,112,69,169,129,144,132,13,152,226,128,228,247,41])) tree051
theorem root063 : root JFp_SHADigest.digest tree063=value063 := by
  rw [tree063,root,root051]
  exact (congrArg JFp_SHADigest.digest address063).trans hash063
#print axioms root063
theorem shape063 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 13824=tree063 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 13824)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 13824 (by decide),siblings 4 (by decide) 13824 (by decide)]
  rw [shape051 f g inputs siblings]
  rfl
#print axioms shape063
def input064 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash064.message
def value064 : State := JFp_SHADigest.output JGc_TX2_M2.Hash064.result
theorem cast064_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash064.B00.input).map Fin.val=JGc_TX2_M2.Hash064.B00.input := by rfl
#print axioms cast064_0
theorem tail064 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash064.tail).map Fin.val=JGc_TX2_M2.Hash064.tail := by rfl
#print axioms tail064
theorem numeric064 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash064.message).map Fin.val=JGc_TX2_M2.Hash064.message := by
  simp only [JGc_TX2_M2.Hash064.message,JGc_TX2_M2.Hash064.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast064_0,tail064]
#print axioms numeric064
theorem hash064 : JFp_SHADigest.digest input064=value064 := by
  unfold input064 JFp_SHADigest.digest
  rw [numeric064,JGc_TX2_M2.Hash064.checked]
  rfl
#print axioms hash064
theorem address064 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [9,238,254,255,39,254,243,46,95,21,236,63,187,8,183,169,44,166,37,80,101,37,29,79,232,151,122,161,132,199,220,125]) value052)=input064 := by rfl
#print axioms address064
def tree064 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [9,238,254,255,39,254,243,46,95,21,236,63,187,8,183,169,44,166,37,80,101,37,29,79,232,151,122,161,132,199,220,125])) tree052
theorem root064 : root JFp_SHADigest.digest tree064=value064 := by
  rw [tree064,root,root052]
  exact (congrArg JFp_SHADigest.digest address064).trans hash064
#print axioms root064
theorem shape064 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 15936=tree064 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 15936)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 15936 (by decide),siblings 4 (by decide) 15936 (by decide)]
  rw [shape052 f g inputs siblings]
  rfl
#print axioms shape064
def input065 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash065.message
def value065 : State := JFp_SHADigest.output JGc_TX2_M2.Hash065.result
theorem cast065_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash065.B00.input).map Fin.val=JGc_TX2_M2.Hash065.B00.input := by rfl
#print axioms cast065_0
theorem tail065 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash065.tail).map Fin.val=JGc_TX2_M2.Hash065.tail := by rfl
#print axioms tail065
theorem numeric065 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash065.message).map Fin.val=JGc_TX2_M2.Hash065.message := by
  simp only [JGc_TX2_M2.Hash065.message,JGc_TX2_M2.Hash065.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast065_0,tail065]
#print axioms numeric065
theorem hash065 : JFp_SHADigest.digest input065=value065 := by
  unfold input065 JFp_SHADigest.digest
  rw [numeric065,JGc_TX2_M2.Hash065.checked]
  rfl
#print axioms hash065
theorem address065 : BinMerkle32Path.nodeInput (children value053 (JGc_TX2_HashBytes.state [100,212,44,109,255,78,23,21,146,213,56,218,252,246,125,196,178,169,158,114,87,64,92,68,191,82,154,132,247,33,109,192]))=input065 := by rfl
#print axioms address065
def tree065 : Tree := .branch tree053 (.supplied (JGc_TX2_HashBytes.state [100,212,44,109,255,78,23,21,146,213,56,218,252,246,125,196,178,169,158,114,87,64,92,68,191,82,154,132,247,33,109,192]))
theorem root065 : root JFp_SHADigest.digest tree065=value065 := by
  rw [tree065,root,root053]
  exact (congrArg JFp_SHADigest.digest address065).trans hash065
#print axioms root065
theorem shape065 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 33088=tree065 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 33088)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape053 f g inputs siblings]
  rw [unoccupied f g 4 33104 (by decide),siblings 4 (by decide) 33104 (by decide)]
  rfl
#print axioms shape065
def input066 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash066.message
def value066 : State := JFp_SHADigest.output JGc_TX2_M2.Hash066.result
theorem cast066_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash066.B00.input).map Fin.val=JGc_TX2_M2.Hash066.B00.input := by rfl
#print axioms cast066_0
theorem tail066 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash066.tail).map Fin.val=JGc_TX2_M2.Hash066.tail := by rfl
#print axioms tail066
theorem numeric066 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash066.message).map Fin.val=JGc_TX2_M2.Hash066.message := by
  simp only [JGc_TX2_M2.Hash066.message,JGc_TX2_M2.Hash066.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast066_0,tail066]
#print axioms numeric066
theorem hash066 : JFp_SHADigest.digest input066=value066 := by
  unfold input066 JFp_SHADigest.digest
  rw [numeric066,JGc_TX2_M2.Hash066.checked]
  rfl
#print axioms hash066
theorem address066 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [245,72,84,194,109,47,181,252,233,38,6,190,122,213,219,166,146,217,99,248,71,208,31,100,80,120,165,181,91,203,136,110]) value054)=input066 := by rfl
#print axioms address066
def tree066 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [245,72,84,194,109,47,181,252,233,38,6,190,122,213,219,166,146,217,99,248,71,208,31,100,80,120,165,181,91,203,136,110])) tree054
theorem root066 : root JFp_SHADigest.digest tree066=value066 := by
  rw [tree066,root,root054]
  exact (congrArg JFp_SHADigest.digest address066).trans hash066
#print axioms root066
theorem shape066 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 37376=tree066 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 37376)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 37376 (by decide),siblings 4 (by decide) 37376 (by decide)]
  rw [shape054 f g inputs siblings]
  rfl
#print axioms shape066
def input067 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash067.message
def value067 : State := JFp_SHADigest.output JGc_TX2_M2.Hash067.result
theorem cast067_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash067.B00.input).map Fin.val=JGc_TX2_M2.Hash067.B00.input := by rfl
#print axioms cast067_0
theorem tail067 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash067.tail).map Fin.val=JGc_TX2_M2.Hash067.tail := by rfl
#print axioms tail067
theorem numeric067 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash067.message).map Fin.val=JGc_TX2_M2.Hash067.message := by
  simp only [JGc_TX2_M2.Hash067.message,JGc_TX2_M2.Hash067.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast067_0,tail067]
#print axioms numeric067
theorem hash067 : JFp_SHADigest.digest input067=value067 := by
  unfold input067 JFp_SHADigest.digest
  rw [numeric067,JGc_TX2_M2.Hash067.checked]
  rfl
#print axioms hash067
theorem address067 : BinMerkle32Path.nodeInput (children value055 (JGc_TX2_HashBytes.state [106,188,178,230,119,169,216,143,108,241,225,128,42,214,225,250,113,247,35,216,252,247,44,106,56,109,25,126,244,160,227,251]))=input067 := by rfl
#print axioms address067
def tree067 : Tree := .branch tree055 (.supplied (JGc_TX2_HashBytes.state [106,188,178,230,119,169,216,143,108,241,225,128,42,214,225,250,113,247,35,216,252,247,44,106,56,109,25,126,244,160,227,251]))
theorem root067 : root JFp_SHADigest.digest tree067=value067 := by
  rw [tree067,root,root055]
  exact (congrArg JFp_SHADigest.digest address067).trans hash067
#print axioms root067
theorem shape067 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 41536=tree067 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 41536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape055 f g inputs siblings]
  rw [unoccupied f g 4 41552 (by decide),siblings 4 (by decide) 41552 (by decide)]
  rfl
#print axioms shape067
def input068 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash068.message
def value068 : State := JFp_SHADigest.output JGc_TX2_M2.Hash068.result
theorem cast068_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash068.B00.input).map Fin.val=JGc_TX2_M2.Hash068.B00.input := by rfl
#print axioms cast068_0
theorem tail068 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash068.tail).map Fin.val=JGc_TX2_M2.Hash068.tail := by rfl
#print axioms tail068
theorem numeric068 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash068.message).map Fin.val=JGc_TX2_M2.Hash068.message := by
  simp only [JGc_TX2_M2.Hash068.message,JGc_TX2_M2.Hash068.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast068_0,tail068]
#print axioms numeric068
theorem hash068 : JFp_SHADigest.digest input068=value068 := by
  unfold input068 JFp_SHADigest.digest
  rw [numeric068,JGc_TX2_M2.Hash068.checked]
  rfl
#print axioms hash068
theorem address068 : BinMerkle32Path.nodeInput (children value056 (JGc_TX2_HashBytes.state [155,130,8,91,15,187,131,135,196,217,122,123,47,107,17,16,212,157,238,253,47,129,67,155,161,159,151,86,58,173,37,177]))=input068 := by rfl
#print axioms address068
def tree068 : Tree := .branch tree056 (.supplied (JGc_TX2_HashBytes.state [155,130,8,91,15,187,131,135,196,217,122,123,47,107,17,16,212,157,238,253,47,129,67,155,161,159,151,86,58,173,37,177]))
theorem root068 : root JFp_SHADigest.digest tree068=value068 := by
  rw [tree068,root,root056]
  exact (congrArg JFp_SHADigest.digest address068).trans hash068
#print axioms root068
theorem shape068 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 44512=tree068 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 44512)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape056 f g inputs siblings]
  rw [unoccupied f g 4 44528 (by decide),siblings 4 (by decide) 44528 (by decide)]
  rfl
#print axioms shape068
def input069 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash069.message
def value069 : State := JFp_SHADigest.output JGc_TX2_M2.Hash069.result
theorem cast069_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash069.B00.input).map Fin.val=JGc_TX2_M2.Hash069.B00.input := by rfl
#print axioms cast069_0
theorem tail069 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash069.tail).map Fin.val=JGc_TX2_M2.Hash069.tail := by rfl
#print axioms tail069
theorem numeric069 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash069.message).map Fin.val=JGc_TX2_M2.Hash069.message := by
  simp only [JGc_TX2_M2.Hash069.message,JGc_TX2_M2.Hash069.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast069_0,tail069]
#print axioms numeric069
theorem hash069 : JFp_SHADigest.digest input069=value069 := by
  unfold input069 JFp_SHADigest.digest
  rw [numeric069,JGc_TX2_M2.Hash069.checked]
  rfl
#print axioms hash069
theorem address069 : BinMerkle32Path.nodeInput (children value057 (JGc_TX2_HashBytes.state [197,243,223,90,252,37,18,71,199,122,73,100,251,196,134,181,134,250,69,242,47,132,11,63,218,201,169,244,244,50,29,163]))=input069 := by rfl
#print axioms address069
def tree069 : Tree := .branch tree057 (.supplied (JGc_TX2_HashBytes.state [197,243,223,90,252,37,18,71,199,122,73,100,251,196,134,181,134,250,69,242,47,132,11,63,218,201,169,244,244,50,29,163]))
theorem root069 : root JFp_SHADigest.digest tree069=value069 := by
  rw [tree069,root,root057]
  exact (congrArg JFp_SHADigest.digest address069).trans hash069
#print axioms root069
theorem shape069 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 44896=tree069 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 44896)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape057 f g inputs siblings]
  rw [unoccupied f g 4 44912 (by decide),siblings 4 (by decide) 44912 (by decide)]
  rfl
#print axioms shape069
def input070 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash070.message
def value070 : State := JFp_SHADigest.output JGc_TX2_M2.Hash070.result
theorem cast070_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash070.B00.input).map Fin.val=JGc_TX2_M2.Hash070.B00.input := by rfl
#print axioms cast070_0
theorem tail070 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash070.tail).map Fin.val=JGc_TX2_M2.Hash070.tail := by rfl
#print axioms tail070
theorem numeric070 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash070.message).map Fin.val=JGc_TX2_M2.Hash070.message := by
  simp only [JGc_TX2_M2.Hash070.message,JGc_TX2_M2.Hash070.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast070_0,tail070]
#print axioms numeric070
theorem hash070 : JFp_SHADigest.digest input070=value070 := by
  unfold input070 JFp_SHADigest.digest
  rw [numeric070,JGc_TX2_M2.Hash070.checked]
  rfl
#print axioms hash070
theorem address070 : BinMerkle32Path.nodeInput (children value058 (JGc_TX2_HashBytes.state [41,80,148,57,53,114,10,3,122,75,219,82,120,38,161,206,250,203,250,125,171,10,160,248,198,226,154,77,68,219,2,125]))=input070 := by rfl
#print axioms address070
def tree070 : Tree := .branch tree058 (.supplied (JGc_TX2_HashBytes.state [41,80,148,57,53,114,10,3,122,75,219,82,120,38,161,206,250,203,250,125,171,10,160,248,198,226,154,77,68,219,2,125]))
theorem root070 : root JFp_SHADigest.digest tree070=value070 := by
  rw [tree070,root,root058]
  exact (congrArg JFp_SHADigest.digest address070).trans hash070
#print axioms root070
theorem shape070 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 46400=tree070 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 46400)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape058 f g inputs siblings]
  rw [unoccupied f g 4 46416 (by decide),siblings 4 (by decide) 46416 (by decide)]
  rfl
#print axioms shape070
def input071 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash071.message
def value071 : State := JFp_SHADigest.output JGc_TX2_M2.Hash071.result
theorem cast071_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash071.B00.input).map Fin.val=JGc_TX2_M2.Hash071.B00.input := by rfl
#print axioms cast071_0
theorem tail071 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash071.tail).map Fin.val=JGc_TX2_M2.Hash071.tail := by rfl
#print axioms tail071
theorem numeric071 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash071.message).map Fin.val=JGc_TX2_M2.Hash071.message := by
  simp only [JGc_TX2_M2.Hash071.message,JGc_TX2_M2.Hash071.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast071_0,tail071]
#print axioms numeric071
theorem hash071 : JFp_SHADigest.digest input071=value071 := by
  unfold input071 JFp_SHADigest.digest
  rw [numeric071,JGc_TX2_M2.Hash071.checked]
  rfl
#print axioms hash071
theorem address071 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [179,249,234,136,136,173,217,82,176,51,76,226,205,86,174,215,92,34,110,234,232,9,110,135,142,4,169,245,40,230,2,165]) value059)=input071 := by rfl
#print axioms address071
def tree071 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [179,249,234,136,136,173,217,82,176,51,76,226,205,86,174,215,92,34,110,234,232,9,110,135,142,4,169,245,40,230,2,165])) tree059
theorem root071 : root JFp_SHADigest.digest tree071=value071 := by
  rw [tree071,root,root059]
  exact (congrArg JFp_SHADigest.digest address071).trans hash071
#print axioms root071
theorem shape071 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 54496=tree071 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 54496)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 54496 (by decide),siblings 4 (by decide) 54496 (by decide)]
  rw [shape059 f g inputs siblings]
  rfl
#print axioms shape071
end AspisR1.JGc_TX2_M2Roots
end
