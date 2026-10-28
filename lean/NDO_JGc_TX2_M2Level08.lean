import NDO_JGc_TX2_M2Level07
import NDO_JGc_TX2_M2H108
import NDO_JGc_TX2_M2H112
import NDO_JGc_TX2_M2H116
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input108 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash108.message
def value108 : State := JFp_SHADigest.output JGc_TX2_M2.Hash108.result
theorem cast108_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash108.B00.input).map Fin.val=JGc_TX2_M2.Hash108.B00.input := by rfl
#print axioms cast108_0
theorem tail108 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash108.tail).map Fin.val=JGc_TX2_M2.Hash108.tail := by rfl
#print axioms tail108
theorem numeric108 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash108.message).map Fin.val=JGc_TX2_M2.Hash108.message := by
  simp only [JGc_TX2_M2.Hash108.message,JGc_TX2_M2.Hash108.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast108_0,tail108]
#print axioms numeric108
theorem hash108 : JFp_SHADigest.digest input108=value108 := by
  unfold input108 JFp_SHADigest.digest
  rw [numeric108,JGc_TX2_M2.Hash108.checked]
  rfl
#print axioms hash108
theorem address108 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [218,238,50,200,63,122,205,112,1,96,129,225,174,219,13,23,105,209,62,106,22,187,3,131,78,242,137,23,141,221,53,36]) value096)=input108 := by rfl
#print axioms address108
def tree108 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [218,238,50,200,63,122,205,112,1,96,129,225,174,219,13,23,105,209,62,106,22,187,3,131,78,242,137,23,141,221,53,36])) tree096
theorem root108 : root JFp_SHADigest.digest tree108=value108 := by
  rw [tree108,root,root096]
  exact (congrArg JFp_SHADigest.digest address108).trans hash108
#print axioms root108
theorem shape108 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 3072=tree108 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 3072)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 3072 (by decide),siblings 8 (by decide) 3072 (by decide)]
  rw [shape096 f g inputs siblings]
  rfl
#print axioms shape108
def input109 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash109.message
def value109 : State := JFp_SHADigest.output JGc_TX2_M2.Hash109.result
theorem cast109_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash109.B00.input).map Fin.val=JGc_TX2_M2.Hash109.B00.input := by rfl
#print axioms cast109_0
theorem tail109 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash109.tail).map Fin.val=JGc_TX2_M2.Hash109.tail := by rfl
#print axioms tail109
theorem numeric109 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash109.message).map Fin.val=JGc_TX2_M2.Hash109.message := by
  simp only [JGc_TX2_M2.Hash109.message,JGc_TX2_M2.Hash109.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast109_0,tail109]
#print axioms numeric109
theorem hash109 : JFp_SHADigest.digest input109=value109 := by
  unfold input109 JFp_SHADigest.digest
  rw [numeric109,JGc_TX2_M2.Hash109.checked]
  rfl
#print axioms hash109
theorem address109 : BinMerkle32Path.nodeInput (children value097 (JGc_TX2_HashBytes.state [15,122,10,55,6,140,91,132,57,151,30,131,87,72,204,232,62,161,26,173,137,221,84,100,227,254,29,235,65,221,129,22]))=input109 := by rfl
#print axioms address109
def tree109 : Tree := .branch tree097 (.supplied (JGc_TX2_HashBytes.state [15,122,10,55,6,140,91,132,57,151,30,131,87,72,204,232,62,161,26,173,137,221,84,100,227,254,29,235,65,221,129,22]))
theorem root109 : root JFp_SHADigest.digest tree109=value109 := by
  rw [tree109,root,root097]
  exact (congrArg JFp_SHADigest.digest address109).trans hash109
#print axioms root109
theorem shape109 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 5120=tree109 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 5120)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape097 f g inputs siblings]
  rw [unoccupied f g 8 5376 (by decide),siblings 8 (by decide) 5376 (by decide)]
  rfl
#print axioms shape109
def input110 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash110.message
def value110 : State := JFp_SHADigest.output JGc_TX2_M2.Hash110.result
theorem cast110_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash110.B00.input).map Fin.val=JGc_TX2_M2.Hash110.B00.input := by rfl
#print axioms cast110_0
theorem tail110 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash110.tail).map Fin.val=JGc_TX2_M2.Hash110.tail := by rfl
#print axioms tail110
theorem numeric110 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash110.message).map Fin.val=JGc_TX2_M2.Hash110.message := by
  simp only [JGc_TX2_M2.Hash110.message,JGc_TX2_M2.Hash110.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast110_0,tail110]
#print axioms numeric110
theorem hash110 : JFp_SHADigest.digest input110=value110 := by
  unfold input110 JFp_SHADigest.digest
  rw [numeric110,JGc_TX2_M2.Hash110.checked]
  rfl
#print axioms hash110
theorem address110 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [11,224,123,69,59,20,49,235,7,135,199,210,67,32,45,15,0,196,88,133,47,103,208,79,73,87,177,173,105,72,84,224]) value098)=input110 := by rfl
#print axioms address110
def tree110 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [11,224,123,69,59,20,49,235,7,135,199,210,67,32,45,15,0,196,88,133,47,103,208,79,73,87,177,173,105,72,84,224])) tree098
theorem root110 : root JFp_SHADigest.digest tree110=value110 := by
  rw [tree110,root,root098]
  exact (congrArg JFp_SHADigest.digest address110).trans hash110
#print axioms root110
theorem shape110 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 10240=tree110 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 10240)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 10240 (by decide),siblings 8 (by decide) 10240 (by decide)]
  rw [shape098 f g inputs siblings]
  rfl
#print axioms shape110
def input111 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash111.message
def value111 : State := JFp_SHADigest.output JGc_TX2_M2.Hash111.result
theorem cast111_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash111.B00.input).map Fin.val=JGc_TX2_M2.Hash111.B00.input := by rfl
#print axioms cast111_0
theorem tail111 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash111.tail).map Fin.val=JGc_TX2_M2.Hash111.tail := by rfl
#print axioms tail111
theorem numeric111 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash111.message).map Fin.val=JGc_TX2_M2.Hash111.message := by
  simp only [JGc_TX2_M2.Hash111.message,JGc_TX2_M2.Hash111.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast111_0,tail111]
#print axioms numeric111
theorem hash111 : JFp_SHADigest.digest input111=value111 := by
  unfold input111 JFp_SHADigest.digest
  rw [numeric111,JGc_TX2_M2.Hash111.checked]
  rfl
#print axioms hash111
theorem address111 : BinMerkle32Path.nodeInput (children value099 (JGc_TX2_HashBytes.state [129,102,155,34,234,81,11,95,91,233,175,252,151,74,152,169,180,251,141,65,54,179,76,165,27,19,131,34,207,116,53,222]))=input111 := by rfl
#print axioms address111
def tree111 : Tree := .branch tree099 (.supplied (JGc_TX2_HashBytes.state [129,102,155,34,234,81,11,95,91,233,175,252,151,74,152,169,180,251,141,65,54,179,76,165,27,19,131,34,207,116,53,222]))
theorem root111 : root JFp_SHADigest.digest tree111=value111 := by
  rw [tree111,root,root099]
  exact (congrArg JFp_SHADigest.digest address111).trans hash111
#print axioms root111
theorem shape111 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 13824=tree111 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 13824)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape099 f g inputs siblings]
  rw [unoccupied f g 8 14080 (by decide),siblings 8 (by decide) 14080 (by decide)]
  rfl
#print axioms shape111
def input112 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash112.message
def value112 : State := JFp_SHADigest.output JGc_TX2_M2.Hash112.result
theorem cast112_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash112.B00.input).map Fin.val=JGc_TX2_M2.Hash112.B00.input := by rfl
#print axioms cast112_0
theorem tail112 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash112.tail).map Fin.val=JGc_TX2_M2.Hash112.tail := by rfl
#print axioms tail112
theorem numeric112 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash112.message).map Fin.val=JGc_TX2_M2.Hash112.message := by
  simp only [JGc_TX2_M2.Hash112.message,JGc_TX2_M2.Hash112.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast112_0,tail112]
#print axioms numeric112
theorem hash112 : JFp_SHADigest.digest input112=value112 := by
  unfold input112 JFp_SHADigest.digest
  rw [numeric112,JGc_TX2_M2.Hash112.checked]
  rfl
#print axioms hash112
theorem address112 : BinMerkle32Path.nodeInput (children value100 (JGc_TX2_HashBytes.state [223,15,252,170,76,199,28,197,19,110,150,124,50,238,246,246,53,155,152,179,125,169,80,124,193,41,198,224,244,251,125,62]))=input112 := by rfl
#print axioms address112
def tree112 : Tree := .branch tree100 (.supplied (JGc_TX2_HashBytes.state [223,15,252,170,76,199,28,197,19,110,150,124,50,238,246,246,53,155,152,179,125,169,80,124,193,41,198,224,244,251,125,62]))
theorem root112 : root JFp_SHADigest.digest tree112=value112 := by
  rw [tree112,root,root100]
  exact (congrArg JFp_SHADigest.digest address112).trans hash112
#print axioms root112
theorem shape112 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 15872=tree112 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 15872)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape100 f g inputs siblings]
  rw [unoccupied f g 8 16128 (by decide),siblings 8 (by decide) 16128 (by decide)]
  rfl
#print axioms shape112
def input113 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash113.message
def value113 : State := JFp_SHADigest.output JGc_TX2_M2.Hash113.result
theorem cast113_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash113.B00.input).map Fin.val=JGc_TX2_M2.Hash113.B00.input := by rfl
#print axioms cast113_0
theorem tail113 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash113.tail).map Fin.val=JGc_TX2_M2.Hash113.tail := by rfl
#print axioms tail113
theorem numeric113 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash113.message).map Fin.val=JGc_TX2_M2.Hash113.message := by
  simp only [JGc_TX2_M2.Hash113.message,JGc_TX2_M2.Hash113.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast113_0,tail113]
#print axioms numeric113
theorem hash113 : JFp_SHADigest.digest input113=value113 := by
  unfold input113 JFp_SHADigest.digest
  rw [numeric113,JGc_TX2_M2.Hash113.checked]
  rfl
#print axioms hash113
theorem address113 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [161,6,62,173,199,189,101,43,53,128,167,220,181,53,132,29,233,225,141,96,8,197,157,60,39,57,32,29,141,203,158,0]) value101)=input113 := by rfl
#print axioms address113
def tree113 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [161,6,62,173,199,189,101,43,53,128,167,220,181,53,132,29,233,225,141,96,8,197,157,60,39,57,32,29,141,203,158,0])) tree101
theorem root113 : root JFp_SHADigest.digest tree113=value113 := by
  rw [tree113,root,root101]
  exact (congrArg JFp_SHADigest.digest address113).trans hash113
#print axioms root113
theorem shape113 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 32768=tree113 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 32768)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 32768 (by decide),siblings 8 (by decide) 32768 (by decide)]
  rw [shape101 f g inputs siblings]
  rfl
#print axioms shape113
def input114 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash114.message
def value114 : State := JFp_SHADigest.output JGc_TX2_M2.Hash114.result
theorem cast114_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash114.B00.input).map Fin.val=JGc_TX2_M2.Hash114.B00.input := by rfl
#print axioms cast114_0
theorem tail114 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash114.tail).map Fin.val=JGc_TX2_M2.Hash114.tail := by rfl
#print axioms tail114
theorem numeric114 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash114.message).map Fin.val=JGc_TX2_M2.Hash114.message := by
  simp only [JGc_TX2_M2.Hash114.message,JGc_TX2_M2.Hash114.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast114_0,tail114]
#print axioms numeric114
theorem hash114 : JFp_SHADigest.digest input114=value114 := by
  unfold input114 JFp_SHADigest.digest
  rw [numeric114,JGc_TX2_M2.Hash114.checked]
  rfl
#print axioms hash114
theorem address114 : BinMerkle32Path.nodeInput (children value102 (JGc_TX2_HashBytes.state [32,61,232,250,65,134,84,127,55,144,151,156,243,30,160,217,254,133,111,178,149,51,211,242,194,156,234,13,169,205,98,129]))=input114 := by rfl
#print axioms address114
def tree114 : Tree := .branch tree102 (.supplied (JGc_TX2_HashBytes.state [32,61,232,250,65,134,84,127,55,144,151,156,243,30,160,217,254,133,111,178,149,51,211,242,194,156,234,13,169,205,98,129]))
theorem root114 : root JFp_SHADigest.digest tree114=value114 := by
  rw [tree114,root,root102]
  exact (congrArg JFp_SHADigest.digest address114).trans hash114
#print axioms root114
theorem shape114 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 37376=tree114 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 37376)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape102 f g inputs siblings]
  rw [unoccupied f g 8 37632 (by decide),siblings 8 (by decide) 37632 (by decide)]
  rfl
#print axioms shape114
def input115 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash115.message
def value115 : State := JFp_SHADigest.output JGc_TX2_M2.Hash115.result
theorem cast115_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash115.B00.input).map Fin.val=JGc_TX2_M2.Hash115.B00.input := by rfl
#print axioms cast115_0
theorem tail115 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash115.tail).map Fin.val=JGc_TX2_M2.Hash115.tail := by rfl
#print axioms tail115
theorem numeric115 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash115.message).map Fin.val=JGc_TX2_M2.Hash115.message := by
  simp only [JGc_TX2_M2.Hash115.message,JGc_TX2_M2.Hash115.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast115_0,tail115]
#print axioms numeric115
theorem hash115 : JFp_SHADigest.digest input115=value115 := by
  unfold input115 JFp_SHADigest.digest
  rw [numeric115,JGc_TX2_M2.Hash115.checked]
  rfl
#print axioms hash115
theorem address115 : BinMerkle32Path.nodeInput (children value103 (JGc_TX2_HashBytes.state [195,142,70,165,83,234,237,242,133,12,38,244,175,89,218,59,200,75,178,84,82,144,239,11,186,168,39,120,171,157,103,50]))=input115 := by rfl
#print axioms address115
def tree115 : Tree := .branch tree103 (.supplied (JGc_TX2_HashBytes.state [195,142,70,165,83,234,237,242,133,12,38,244,175,89,218,59,200,75,178,84,82,144,239,11,186,168,39,120,171,157,103,50]))
theorem root115 : root JFp_SHADigest.digest tree115=value115 := by
  rw [tree115,root,root103]
  exact (congrArg JFp_SHADigest.digest address115).trans hash115
#print axioms root115
theorem shape115 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 41472=tree115 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 41472)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape103 f g inputs siblings]
  rw [unoccupied f g 8 41728 (by decide),siblings 8 (by decide) 41728 (by decide)]
  rfl
#print axioms shape115
def input116 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash116.message
def value116 : State := JFp_SHADigest.output JGc_TX2_M2.Hash116.result
theorem cast116_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash116.B00.input).map Fin.val=JGc_TX2_M2.Hash116.B00.input := by rfl
#print axioms cast116_0
theorem tail116 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash116.tail).map Fin.val=JGc_TX2_M2.Hash116.tail := by rfl
#print axioms tail116
theorem numeric116 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash116.message).map Fin.val=JGc_TX2_M2.Hash116.message := by
  simp only [JGc_TX2_M2.Hash116.message,JGc_TX2_M2.Hash116.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast116_0,tail116]
#print axioms numeric116
theorem hash116 : JFp_SHADigest.digest input116=value116 := by
  unfold input116 JFp_SHADigest.digest
  rw [numeric116,JGc_TX2_M2.Hash116.checked]
  rfl
#print axioms hash116
theorem address116 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [120,246,194,40,100,13,43,67,172,255,221,65,73,215,185,58,140,17,192,106,47,103,7,109,141,22,236,224,213,222,56,35]) value104)=input116 := by rfl
#print axioms address116
def tree116 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [120,246,194,40,100,13,43,67,172,255,221,65,73,215,185,58,140,17,192,106,47,103,7,109,141,22,236,224,213,222,56,35])) tree104
theorem root116 : root JFp_SHADigest.digest tree116=value116 := by
  rw [tree116,root,root104]
  exact (congrArg JFp_SHADigest.digest address116).trans hash116
#print axioms root116
theorem shape116 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 44032=tree116 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 44032)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 44032 (by decide),siblings 8 (by decide) 44032 (by decide)]
  rw [shape104 f g inputs siblings]
  rfl
#print axioms shape116
def input117 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash117.message
def value117 : State := JFp_SHADigest.output JGc_TX2_M2.Hash117.result
theorem cast117_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash117.B00.input).map Fin.val=JGc_TX2_M2.Hash117.B00.input := by rfl
#print axioms cast117_0
theorem tail117 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash117.tail).map Fin.val=JGc_TX2_M2.Hash117.tail := by rfl
#print axioms tail117
theorem numeric117 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash117.message).map Fin.val=JGc_TX2_M2.Hash117.message := by
  simp only [JGc_TX2_M2.Hash117.message,JGc_TX2_M2.Hash117.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast117_0,tail117]
#print axioms numeric117
theorem hash117 : JFp_SHADigest.digest input117=value117 := by
  unfold input117 JFp_SHADigest.digest
  rw [numeric117,JGc_TX2_M2.Hash117.checked]
  rfl
#print axioms hash117
theorem address117 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [68,26,85,81,72,216,142,241,226,107,88,198,11,13,123,131,251,67,93,136,104,115,251,44,204,2,192,72,144,92,14,90]) value105)=input117 := by rfl
#print axioms address117
def tree117 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [68,26,85,81,72,216,142,241,226,107,88,198,11,13,123,131,251,67,93,136,104,115,251,44,204,2,192,72,144,92,14,90])) tree105
theorem root117 : root JFp_SHADigest.digest tree117=value117 := by
  rw [tree117,root,root105]
  exact (congrArg JFp_SHADigest.digest address117).trans hash117
#print axioms root117
theorem shape117 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 44544=tree117 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 44544)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 44544 (by decide),siblings 8 (by decide) 44544 (by decide)]
  rw [shape105 f g inputs siblings]
  rfl
#print axioms shape117
def input118 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash118.message
def value118 : State := JFp_SHADigest.output JGc_TX2_M2.Hash118.result
theorem cast118_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash118.B00.input).map Fin.val=JGc_TX2_M2.Hash118.B00.input := by rfl
#print axioms cast118_0
theorem tail118 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash118.tail).map Fin.val=JGc_TX2_M2.Hash118.tail := by rfl
#print axioms tail118
theorem numeric118 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash118.message).map Fin.val=JGc_TX2_M2.Hash118.message := by
  simp only [JGc_TX2_M2.Hash118.message,JGc_TX2_M2.Hash118.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast118_0,tail118]
#print axioms numeric118
theorem hash118 : JFp_SHADigest.digest input118=value118 := by
  unfold input118 JFp_SHADigest.digest
  rw [numeric118,JGc_TX2_M2.Hash118.checked]
  rfl
#print axioms hash118
theorem address118 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [124,231,161,169,115,69,108,68,119,53,3,24,134,43,151,144,104,169,143,201,144,171,181,140,24,93,179,174,204,97,196,133]) value106)=input118 := by rfl
#print axioms address118
def tree118 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [124,231,161,169,115,69,108,68,119,53,3,24,134,43,151,144,104,169,143,201,144,171,181,140,24,93,179,174,204,97,196,133])) tree106
theorem root118 : root JFp_SHADigest.digest tree118=value118 := by
  rw [tree118,root,root106]
  exact (congrArg JFp_SHADigest.digest address118).trans hash118
#print axioms root118
theorem shape118 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 46080=tree118 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 46080)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 46080 (by decide),siblings 8 (by decide) 46080 (by decide)]
  rw [shape106 f g inputs siblings]
  rfl
#print axioms shape118
def input119 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash119.message
def value119 : State := JFp_SHADigest.output JGc_TX2_M2.Hash119.result
theorem cast119_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash119.B00.input).map Fin.val=JGc_TX2_M2.Hash119.B00.input := by rfl
#print axioms cast119_0
theorem tail119 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash119.tail).map Fin.val=JGc_TX2_M2.Hash119.tail := by rfl
#print axioms tail119
theorem numeric119 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash119.message).map Fin.val=JGc_TX2_M2.Hash119.message := by
  simp only [JGc_TX2_M2.Hash119.message,JGc_TX2_M2.Hash119.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast119_0,tail119]
#print axioms numeric119
theorem hash119 : JFp_SHADigest.digest input119=value119 := by
  unfold input119 JFp_SHADigest.digest
  rw [numeric119,JGc_TX2_M2.Hash119.checked]
  rfl
#print axioms hash119
theorem address119 : BinMerkle32Path.nodeInput (children value107 (JGc_TX2_HashBytes.state [196,46,232,194,162,166,36,191,104,15,74,199,133,171,182,35,139,73,145,24,71,236,91,2,23,6,247,180,55,217,53,89]))=input119 := by rfl
#print axioms address119
def tree119 : Tree := .branch tree107 (.supplied (JGc_TX2_HashBytes.state [196,46,232,194,162,166,36,191,104,15,74,199,133,171,182,35,139,73,145,24,71,236,91,2,23,6,247,180,55,217,53,89]))
theorem root119 : root JFp_SHADigest.digest tree119=value119 := by
  rw [tree119,root,root107]
  exact (congrArg JFp_SHADigest.digest address119).trans hash119
#print axioms root119
theorem shape119 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 54272=tree119 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 54272)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape107 f g inputs siblings]
  rw [unoccupied f g 8 54528 (by decide),siblings 8 (by decide) 54528 (by decide)]
  rfl
#print axioms shape119
end AspisR1.JGc_TX2_M2Roots
end
