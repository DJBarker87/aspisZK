import NDO_JGh_TX2_M1Level07
import NDO_JGh_TX2_M1W028
import NDO_JGh_TX2_M1W029
import NDO_JGh_TX2_M1W030
import NDO_JGh_TX2_M1W031
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input108 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash108.message
def value108 : State := JFp_SHADigest.output JGh_TX2_M1.Hash108.result
theorem cast108_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash108.B00.input).map Fin.val=JGh_TX2_M1.Hash108.B00.input := by rfl
#print axioms cast108_0
theorem tail108 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash108.tail).map Fin.val=JGh_TX2_M1.Hash108.tail := by rfl
#print axioms tail108
theorem numeric108 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash108.message).map Fin.val=JGh_TX2_M1.Hash108.message := by
  simp only [JGh_TX2_M1.Hash108.message,JGh_TX2_M1.Hash108.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast108_0,tail108]
#print axioms numeric108
theorem hash108 : JFp_SHADigest.digest input108=value108 := by
  unfold input108 JFp_SHADigest.digest
  rw [numeric108,JGh_TX2_M1.Hash108.checked]
  rfl
#print axioms hash108
theorem address108 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [42,209,186,244,64,85,154,4,35,97,184,129,217,47,240,33,72,208,128,192,228,223,212,59,153,155,151,190,205,35,160,174]) value096)=input108 := by rfl
#print axioms address108
def tree108 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [42,209,186,244,64,85,154,4,35,97,184,129,217,47,240,33,72,208,128,192,228,223,212,59,153,155,151,190,205,35,160,174])) tree096
theorem root108 : root JFp_SHADigest.digest tree108=value108 := by
  rw [tree108,root,root096]
  exact (congrArg JFp_SHADigest.digest address108).trans hash108
#print axioms root108
theorem shape108 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 13824=tree108 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 13824)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 13824 (by decide),siblings 8 (by decide) 13824 (by decide)]
  rw [shape096 f g inputs siblings]
  rfl
#print axioms shape108
def input109 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash109.message
def value109 : State := JFp_SHADigest.output JGh_TX2_M1.Hash109.result
theorem cast109_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash109.B00.input).map Fin.val=JGh_TX2_M1.Hash109.B00.input := by rfl
#print axioms cast109_0
theorem tail109 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash109.tail).map Fin.val=JGh_TX2_M1.Hash109.tail := by rfl
#print axioms tail109
theorem numeric109 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash109.message).map Fin.val=JGh_TX2_M1.Hash109.message := by
  simp only [JGh_TX2_M1.Hash109.message,JGh_TX2_M1.Hash109.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast109_0,tail109]
#print axioms numeric109
theorem hash109 : JFp_SHADigest.digest input109=value109 := by
  unfold input109 JFp_SHADigest.digest
  rw [numeric109,JGh_TX2_M1.Hash109.checked]
  rfl
#print axioms hash109
theorem address109 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [82,94,77,0,170,233,221,217,248,59,144,8,3,70,235,166,198,116,219,79,252,184,193,194,47,240,55,247,228,123,125,80]) value097)=input109 := by rfl
#print axioms address109
def tree109 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [82,94,77,0,170,233,221,217,248,59,144,8,3,70,235,166,198,116,219,79,252,184,193,194,47,240,55,247,228,123,125,80])) tree097
theorem root109 : root JFp_SHADigest.digest tree109=value109 := by
  rw [tree109,root,root097]
  exact (congrArg JFp_SHADigest.digest address109).trans hash109
#print axioms root109
theorem shape109 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 20992=tree109 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 20992)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 20992 (by decide),siblings 8 (by decide) 20992 (by decide)]
  rw [shape097 f g inputs siblings]
  rfl
#print axioms shape109
def input110 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash110.message
def value110 : State := JFp_SHADigest.output JGh_TX2_M1.Hash110.result
theorem cast110_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash110.B00.input).map Fin.val=JGh_TX2_M1.Hash110.B00.input := by rfl
#print axioms cast110_0
theorem tail110 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash110.tail).map Fin.val=JGh_TX2_M1.Hash110.tail := by rfl
#print axioms tail110
theorem numeric110 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash110.message).map Fin.val=JGh_TX2_M1.Hash110.message := by
  simp only [JGh_TX2_M1.Hash110.message,JGh_TX2_M1.Hash110.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast110_0,tail110]
#print axioms numeric110
theorem hash110 : JFp_SHADigest.digest input110=value110 := by
  unfold input110 JFp_SHADigest.digest
  rw [numeric110,JGh_TX2_M1.Hash110.checked]
  rfl
#print axioms hash110
theorem address110 : BinMerkle32Path.nodeInput (children value098 (JGc_TX2_HashBytes.state [40,215,101,86,132,103,98,75,92,66,147,138,245,123,182,130,185,144,80,181,158,42,111,102,112,29,217,183,61,160,242,254]))=input110 := by rfl
#print axioms address110
def tree110 : Tree := .branch tree098 (.supplied (JGc_TX2_HashBytes.state [40,215,101,86,132,103,98,75,92,66,147,138,245,123,182,130,185,144,80,181,158,42,111,102,112,29,217,183,61,160,242,254]))
theorem root110 : root JFp_SHADigest.digest tree110=value110 := by
  rw [tree110,root,root098]
  exact (congrArg JFp_SHADigest.digest address110).trans hash110
#print axioms root110
theorem shape110 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 41984=tree110 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 41984)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape098 f g inputs siblings]
  rw [unoccupied f g 8 42240 (by decide),siblings 8 (by decide) 42240 (by decide)]
  rfl
#print axioms shape110
def input111 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash111.message
def value111 : State := JFp_SHADigest.output JGh_TX2_M1.Hash111.result
theorem cast111_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash111.B00.input).map Fin.val=JGh_TX2_M1.Hash111.B00.input := by rfl
#print axioms cast111_0
theorem tail111 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash111.tail).map Fin.val=JGh_TX2_M1.Hash111.tail := by rfl
#print axioms tail111
theorem numeric111 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash111.message).map Fin.val=JGh_TX2_M1.Hash111.message := by
  simp only [JGh_TX2_M1.Hash111.message,JGh_TX2_M1.Hash111.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast111_0,tail111]
#print axioms numeric111
theorem hash111 : JFp_SHADigest.digest input111=value111 := by
  unfold input111 JFp_SHADigest.digest
  rw [numeric111,JGh_TX2_M1.Hash111.checked]
  rfl
#print axioms hash111
theorem address111 : BinMerkle32Path.nodeInput (children value099 (JGc_TX2_HashBytes.state [160,57,196,196,130,249,248,110,80,135,72,195,79,96,23,162,223,76,2,127,239,150,180,152,54,38,56,11,44,236,208,13]))=input111 := by rfl
#print axioms address111
def tree111 : Tree := .branch tree099 (.supplied (JGc_TX2_HashBytes.state [160,57,196,196,130,249,248,110,80,135,72,195,79,96,23,162,223,76,2,127,239,150,180,152,54,38,56,11,44,236,208,13]))
theorem root111 : root JFp_SHADigest.digest tree111=value111 := by
  rw [tree111,root,root099]
  exact (congrArg JFp_SHADigest.digest address111).trans hash111
#print axioms root111
theorem shape111 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 55296=tree111 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 55296)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape099 f g inputs siblings]
  rw [unoccupied f g 8 55552 (by decide),siblings 8 (by decide) 55552 (by decide)]
  rfl
#print axioms shape111
def input112 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash112.message
def value112 : State := JFp_SHADigest.output JGh_TX2_M1.Hash112.result
theorem cast112_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash112.B00.input).map Fin.val=JGh_TX2_M1.Hash112.B00.input := by rfl
#print axioms cast112_0
theorem tail112 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash112.tail).map Fin.val=JGh_TX2_M1.Hash112.tail := by rfl
#print axioms tail112
theorem numeric112 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash112.message).map Fin.val=JGh_TX2_M1.Hash112.message := by
  simp only [JGh_TX2_M1.Hash112.message,JGh_TX2_M1.Hash112.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast112_0,tail112]
#print axioms numeric112
theorem hash112 : JFp_SHADigest.digest input112=value112 := by
  unfold input112 JFp_SHADigest.digest
  rw [numeric112,JGh_TX2_M1.Hash112.checked]
  rfl
#print axioms hash112
theorem address112 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [116,226,67,58,77,187,29,14,225,5,62,35,170,114,175,194,137,30,81,153,243,162,108,99,121,250,179,106,25,131,216,9]) value100)=input112 := by rfl
#print axioms address112
def tree112 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [116,226,67,58,77,187,29,14,225,5,62,35,170,114,175,194,137,30,81,153,243,162,108,99,121,250,179,106,25,131,216,9])) tree100
theorem root112 : root JFp_SHADigest.digest tree112=value112 := by
  rw [tree112,root,root100]
  exact (congrArg JFp_SHADigest.digest address112).trans hash112
#print axioms root112
theorem shape112 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 63488=tree112 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 63488)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 63488 (by decide),siblings 8 (by decide) 63488 (by decide)]
  rw [shape100 f g inputs siblings]
  rfl
#print axioms shape112
def input113 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash113.message
def value113 : State := JFp_SHADigest.output JGh_TX2_M1.Hash113.result
theorem cast113_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash113.B00.input).map Fin.val=JGh_TX2_M1.Hash113.B00.input := by rfl
#print axioms cast113_0
theorem tail113 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash113.tail).map Fin.val=JGh_TX2_M1.Hash113.tail := by rfl
#print axioms tail113
theorem numeric113 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash113.message).map Fin.val=JGh_TX2_M1.Hash113.message := by
  simp only [JGh_TX2_M1.Hash113.message,JGh_TX2_M1.Hash113.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast113_0,tail113]
#print axioms numeric113
theorem hash113 : JFp_SHADigest.digest input113=value113 := by
  unfold input113 JFp_SHADigest.digest
  rw [numeric113,JGh_TX2_M1.Hash113.checked]
  rfl
#print axioms hash113
theorem address113 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [205,24,234,108,136,47,149,179,24,92,160,33,27,250,125,135,39,186,138,44,20,150,255,151,244,164,122,137,231,156,227,56]) value101)=input113 := by rfl
#print axioms address113
def tree113 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [205,24,234,108,136,47,149,179,24,92,160,33,27,250,125,135,39,186,138,44,20,150,255,151,244,164,122,137,231,156,227,56])) tree101
theorem root113 : root JFp_SHADigest.digest tree113=value113 := by
  rw [tree113,root,root101]
  exact (congrArg JFp_SHADigest.digest address113).trans hash113
#print axioms root113
theorem shape113 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 132096=tree113 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 132096)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 132096 (by decide),siblings 8 (by decide) 132096 (by decide)]
  rw [shape101 f g inputs siblings]
  rfl
#print axioms shape113
def input114 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash114.message
def value114 : State := JFp_SHADigest.output JGh_TX2_M1.Hash114.result
theorem cast114_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash114.B00.input).map Fin.val=JGh_TX2_M1.Hash114.B00.input := by rfl
#print axioms cast114_0
theorem tail114 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash114.tail).map Fin.val=JGh_TX2_M1.Hash114.tail := by rfl
#print axioms tail114
theorem numeric114 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash114.message).map Fin.val=JGh_TX2_M1.Hash114.message := by
  simp only [JGh_TX2_M1.Hash114.message,JGh_TX2_M1.Hash114.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast114_0,tail114]
#print axioms numeric114
theorem hash114 : JFp_SHADigest.digest input114=value114 := by
  unfold input114 JFp_SHADigest.digest
  rw [numeric114,JGh_TX2_M1.Hash114.checked]
  rfl
#print axioms hash114
theorem address114 : BinMerkle32Path.nodeInput (children value102 (JGc_TX2_HashBytes.state [39,12,46,158,191,34,15,221,80,208,28,205,102,142,235,84,148,88,40,247,140,63,129,255,161,161,15,77,142,197,121,39]))=input114 := by rfl
#print axioms address114
def tree114 : Tree := .branch tree102 (.supplied (JGc_TX2_HashBytes.state [39,12,46,158,191,34,15,221,80,208,28,205,102,142,235,84,148,88,40,247,140,63,129,255,161,161,15,77,142,197,121,39]))
theorem root114 : root JFp_SHADigest.digest tree114=value114 := by
  rw [tree114,root,root102]
  exact (congrArg JFp_SHADigest.digest address114).trans hash114
#print axioms root114
theorem shape114 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 149504=tree114 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 149504)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape102 f g inputs siblings]
  rw [unoccupied f g 8 149760 (by decide),siblings 8 (by decide) 149760 (by decide)]
  rfl
#print axioms shape114
def input115 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash115.message
def value115 : State := JFp_SHADigest.output JGh_TX2_M1.Hash115.result
theorem cast115_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash115.B00.input).map Fin.val=JGh_TX2_M1.Hash115.B00.input := by rfl
#print axioms cast115_0
theorem tail115 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash115.tail).map Fin.val=JGh_TX2_M1.Hash115.tail := by rfl
#print axioms tail115
theorem numeric115 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash115.message).map Fin.val=JGh_TX2_M1.Hash115.message := by
  simp only [JGh_TX2_M1.Hash115.message,JGh_TX2_M1.Hash115.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast115_0,tail115]
#print axioms numeric115
theorem hash115 : JFp_SHADigest.digest input115=value115 := by
  unfold input115 JFp_SHADigest.digest
  rw [numeric115,JGh_TX2_M1.Hash115.checked]
  rfl
#print axioms hash115
theorem address115 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [38,238,25,53,205,238,129,18,16,93,50,14,32,86,40,21,253,116,219,94,108,165,120,233,186,94,13,166,208,144,221,232]) value103)=input115 := by rfl
#print axioms address115
def tree115 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [38,238,25,53,205,238,129,18,16,93,50,14,32,86,40,21,253,116,219,94,108,165,120,233,186,94,13,166,208,144,221,232])) tree103
theorem root115 : root JFp_SHADigest.digest tree115=value115 := by
  rw [tree115,root,root103]
  exact (congrArg JFp_SHADigest.digest address115).trans hash115
#print axioms root115
theorem shape115 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 165888=tree115 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 165888)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 165888 (by decide),siblings 8 (by decide) 165888 (by decide)]
  rw [shape103 f g inputs siblings]
  rfl
#print axioms shape115
def input116 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash116.message
def value116 : State := JFp_SHADigest.output JGh_TX2_M1.Hash116.result
theorem cast116_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash116.B00.input).map Fin.val=JGh_TX2_M1.Hash116.B00.input := by rfl
#print axioms cast116_0
theorem tail116 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash116.tail).map Fin.val=JGh_TX2_M1.Hash116.tail := by rfl
#print axioms tail116
theorem numeric116 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash116.message).map Fin.val=JGh_TX2_M1.Hash116.message := by
  simp only [JGh_TX2_M1.Hash116.message,JGh_TX2_M1.Hash116.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast116_0,tail116]
#print axioms numeric116
theorem hash116 : JFp_SHADigest.digest input116=value116 := by
  unfold input116 JFp_SHADigest.digest
  rw [numeric116,JGh_TX2_M1.Hash116.checked]
  rfl
#print axioms hash116
theorem address116 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [127,62,114,156,149,104,203,143,198,183,255,114,201,117,117,82,111,158,99,45,121,239,255,80,117,205,134,73,3,69,196,155]) value104)=input116 := by rfl
#print axioms address116
def tree116 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [127,62,114,156,149,104,203,143,198,183,255,114,201,117,117,82,111,158,99,45,121,239,255,80,117,205,134,73,3,69,196,155])) tree104
theorem root116 : root JFp_SHADigest.digest tree116=value116 := by
  rw [tree116,root,root104]
  exact (congrArg JFp_SHADigest.digest address116).trans hash116
#print axioms root116
theorem shape116 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 177664=tree116 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 177664)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 177664 (by decide),siblings 8 (by decide) 177664 (by decide)]
  rw [shape104 f g inputs siblings]
  rfl
#print axioms shape116
def input117 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash117.message
def value117 : State := JFp_SHADigest.output JGh_TX2_M1.Hash117.result
theorem cast117_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash117.B00.input).map Fin.val=JGh_TX2_M1.Hash117.B00.input := by rfl
#print axioms cast117_0
theorem tail117 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash117.tail).map Fin.val=JGh_TX2_M1.Hash117.tail := by rfl
#print axioms tail117
theorem numeric117 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash117.message).map Fin.val=JGh_TX2_M1.Hash117.message := by
  simp only [JGh_TX2_M1.Hash117.message,JGh_TX2_M1.Hash117.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast117_0,tail117]
#print axioms numeric117
theorem hash117 : JFp_SHADigest.digest input117=value117 := by
  unfold input117 JFp_SHADigest.digest
  rw [numeric117,JGh_TX2_M1.Hash117.checked]
  rfl
#print axioms hash117
theorem address117 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [224,37,184,12,191,94,24,26,69,182,112,205,185,74,122,3,77,167,47,60,187,191,139,12,139,18,24,163,135,242,85,237]) value105)=input117 := by rfl
#print axioms address117
def tree117 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [224,37,184,12,191,94,24,26,69,182,112,205,185,74,122,3,77,167,47,60,187,191,139,12,139,18,24,163,135,242,85,237])) tree105
theorem root117 : root JFp_SHADigest.digest tree117=value117 := by
  rw [tree117,root,root105]
  exact (congrArg JFp_SHADigest.digest address117).trans hash117
#print axioms root117
theorem shape117 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 179200=tree117 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 179200)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 179200 (by decide),siblings 8 (by decide) 179200 (by decide)]
  rw [shape105 f g inputs siblings]
  rfl
#print axioms shape117
def input118 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash118.message
def value118 : State := JFp_SHADigest.output JGh_TX2_M1.Hash118.result
theorem cast118_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash118.B00.input).map Fin.val=JGh_TX2_M1.Hash118.B00.input := by rfl
#print axioms cast118_0
theorem tail118 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash118.tail).map Fin.val=JGh_TX2_M1.Hash118.tail := by rfl
#print axioms tail118
theorem numeric118 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash118.message).map Fin.val=JGh_TX2_M1.Hash118.message := by
  simp only [JGh_TX2_M1.Hash118.message,JGh_TX2_M1.Hash118.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast118_0,tail118]
#print axioms numeric118
theorem hash118 : JFp_SHADigest.digest input118=value118 := by
  unfold input118 JFp_SHADigest.digest
  rw [numeric118,JGh_TX2_M1.Hash118.checked]
  rfl
#print axioms hash118
theorem address118 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [16,187,227,107,21,139,209,135,146,50,74,200,68,177,53,46,81,235,223,80,24,55,150,247,82,241,210,90,155,135,139,189]) value106)=input118 := by rfl
#print axioms address118
def tree118 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [16,187,227,107,21,139,209,135,146,50,74,200,68,177,53,46,81,235,223,80,24,55,150,247,82,241,210,90,155,135,139,189])) tree106
theorem root118 : root JFp_SHADigest.digest tree118=value118 := by
  rw [tree118,root,root106]
  exact (congrArg JFp_SHADigest.digest address118).trans hash118
#print axioms root118
theorem shape118 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 185344=tree118 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 185344)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 185344 (by decide),siblings 8 (by decide) 185344 (by decide)]
  rw [shape106 f g inputs siblings]
  rfl
#print axioms shape118
def input119 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash119.message
def value119 : State := JFp_SHADigest.output JGh_TX2_M1.Hash119.result
theorem cast119_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash119.B00.input).map Fin.val=JGh_TX2_M1.Hash119.B00.input := by rfl
#print axioms cast119_0
theorem tail119 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash119.tail).map Fin.val=JGh_TX2_M1.Hash119.tail := by rfl
#print axioms tail119
theorem numeric119 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash119.message).map Fin.val=JGh_TX2_M1.Hash119.message := by
  simp only [JGh_TX2_M1.Hash119.message,JGh_TX2_M1.Hash119.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast119_0,tail119]
#print axioms numeric119
theorem hash119 : JFp_SHADigest.digest input119=value119 := by
  unfold input119 JFp_SHADigest.digest
  rw [numeric119,JGh_TX2_M1.Hash119.checked]
  rfl
#print axioms hash119
theorem address119 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [45,226,164,129,82,202,216,10,56,42,239,25,88,158,122,240,236,117,68,125,2,101,195,154,23,85,105,223,50,236,125,117]) value107)=input119 := by rfl
#print axioms address119
def tree119 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [45,226,164,129,82,202,216,10,56,42,239,25,88,158,122,240,236,117,68,125,2,101,195,154,23,85,105,223,50,236,125,117])) tree107
theorem root119 : root JFp_SHADigest.digest tree119=value119 := by
  rw [tree119,root,root107]
  exact (congrArg JFp_SHADigest.digest address119).trans hash119
#print axioms root119
theorem shape119 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 217600=tree119 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 217600)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 217600 (by decide),siblings 8 (by decide) 217600 (by decide)]
  rw [shape107 f g inputs siblings]
  rfl
#print axioms shape119
end AspisR1.JGh_TX2_M1Roots
end
