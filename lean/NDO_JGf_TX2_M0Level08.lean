import NDO_JGf_TX2_M0Level07
import NDO_JGf_TX2_M0W037
import NDO_JGf_TX2_M0W038
import NDO_JGf_TX2_M0W039
import NDO_JGf_TX2_M0W040
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGf_TX2_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input108 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash108.message
def value108 : State := JFp_SHADigest.output JGf_TX2_M0.Hash108.result
theorem cast108_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash108.B00.input).map Fin.val=JGf_TX2_M0.Hash108.B00.input := by rfl
#print axioms cast108_0
theorem tail108 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash108.tail).map Fin.val=JGf_TX2_M0.Hash108.tail := by rfl
#print axioms tail108
theorem numeric108 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash108.message).map Fin.val=JGf_TX2_M0.Hash108.message := by
  simp only [JGf_TX2_M0.Hash108.message,JGf_TX2_M0.Hash108.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast108_0,tail108]
#print axioms numeric108
theorem hash108 : JFp_SHADigest.digest input108=value108 := by
  unfold input108 JFp_SHADigest.digest
  rw [numeric108,JGf_TX2_M0.Hash108.checked]
  rfl
#print axioms hash108
theorem address108 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [2,46,34,254,218,4,158,107,130,46,114,8,60,95,94,87,229,185,115,156,99,154,199,78,59,36,238,72,42,151,211,188]) value096)=input108 := by rfl
#print axioms address108
def tree108 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [2,46,34,254,218,4,158,107,130,46,114,8,60,95,94,87,229,185,115,156,99,154,199,78,59,36,238,72,42,151,211,188])) tree096
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
def input109 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash109.message
def value109 : State := JFp_SHADigest.output JGf_TX2_M0.Hash109.result
theorem cast109_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash109.B00.input).map Fin.val=JGf_TX2_M0.Hash109.B00.input := by rfl
#print axioms cast109_0
theorem tail109 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash109.tail).map Fin.val=JGf_TX2_M0.Hash109.tail := by rfl
#print axioms tail109
theorem numeric109 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash109.message).map Fin.val=JGf_TX2_M0.Hash109.message := by
  simp only [JGf_TX2_M0.Hash109.message,JGf_TX2_M0.Hash109.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast109_0,tail109]
#print axioms numeric109
theorem hash109 : JFp_SHADigest.digest input109=value109 := by
  unfold input109 JFp_SHADigest.digest
  rw [numeric109,JGf_TX2_M0.Hash109.checked]
  rfl
#print axioms hash109
theorem address109 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [154,208,77,161,184,67,183,200,214,218,136,37,98,103,67,103,151,155,56,146,131,95,186,128,119,190,122,199,199,52,253,226]) value097)=input109 := by rfl
#print axioms address109
def tree109 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [154,208,77,161,184,67,183,200,214,218,136,37,98,103,67,103,151,155,56,146,131,95,186,128,119,190,122,199,199,52,253,226])) tree097
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
def input110 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash110.message
def value110 : State := JFp_SHADigest.output JGf_TX2_M0.Hash110.result
theorem cast110_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash110.B00.input).map Fin.val=JGf_TX2_M0.Hash110.B00.input := by rfl
#print axioms cast110_0
theorem tail110 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash110.tail).map Fin.val=JGf_TX2_M0.Hash110.tail := by rfl
#print axioms tail110
theorem numeric110 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash110.message).map Fin.val=JGf_TX2_M0.Hash110.message := by
  simp only [JGf_TX2_M0.Hash110.message,JGf_TX2_M0.Hash110.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast110_0,tail110]
#print axioms numeric110
theorem hash110 : JFp_SHADigest.digest input110=value110 := by
  unfold input110 JFp_SHADigest.digest
  rw [numeric110,JGf_TX2_M0.Hash110.checked]
  rfl
#print axioms hash110
theorem address110 : BinMerkle32Path.nodeInput (children value098 (JGc_TX2_HashBytes.state [176,111,170,43,1,17,170,220,146,210,5,234,213,229,223,243,68,212,160,189,189,189,180,163,254,22,150,205,181,134,121,150]))=input110 := by rfl
#print axioms address110
def tree110 : Tree := .branch tree098 (.supplied (JGc_TX2_HashBytes.state [176,111,170,43,1,17,170,220,146,210,5,234,213,229,223,243,68,212,160,189,189,189,180,163,254,22,150,205,181,134,121,150]))
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
def input111 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash111.message
def value111 : State := JFp_SHADigest.output JGf_TX2_M0.Hash111.result
theorem cast111_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash111.B00.input).map Fin.val=JGf_TX2_M0.Hash111.B00.input := by rfl
#print axioms cast111_0
theorem tail111 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash111.tail).map Fin.val=JGf_TX2_M0.Hash111.tail := by rfl
#print axioms tail111
theorem numeric111 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash111.message).map Fin.val=JGf_TX2_M0.Hash111.message := by
  simp only [JGf_TX2_M0.Hash111.message,JGf_TX2_M0.Hash111.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast111_0,tail111]
#print axioms numeric111
theorem hash111 : JFp_SHADigest.digest input111=value111 := by
  unfold input111 JFp_SHADigest.digest
  rw [numeric111,JGf_TX2_M0.Hash111.checked]
  rfl
#print axioms hash111
theorem address111 : BinMerkle32Path.nodeInput (children value099 (JGc_TX2_HashBytes.state [190,30,19,138,221,217,158,23,123,111,209,117,218,71,70,238,212,87,112,130,100,166,107,207,132,180,152,66,132,181,25,230]))=input111 := by rfl
#print axioms address111
def tree111 : Tree := .branch tree099 (.supplied (JGc_TX2_HashBytes.state [190,30,19,138,221,217,158,23,123,111,209,117,218,71,70,238,212,87,112,130,100,166,107,207,132,180,152,66,132,181,25,230]))
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
def input112 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash112.message
def value112 : State := JFp_SHADigest.output JGf_TX2_M0.Hash112.result
theorem cast112_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash112.B00.input).map Fin.val=JGf_TX2_M0.Hash112.B00.input := by rfl
#print axioms cast112_0
theorem tail112 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash112.tail).map Fin.val=JGf_TX2_M0.Hash112.tail := by rfl
#print axioms tail112
theorem numeric112 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash112.message).map Fin.val=JGf_TX2_M0.Hash112.message := by
  simp only [JGf_TX2_M0.Hash112.message,JGf_TX2_M0.Hash112.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast112_0,tail112]
#print axioms numeric112
theorem hash112 : JFp_SHADigest.digest input112=value112 := by
  unfold input112 JFp_SHADigest.digest
  rw [numeric112,JGf_TX2_M0.Hash112.checked]
  rfl
#print axioms hash112
theorem address112 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [133,166,92,247,178,14,164,71,151,110,197,203,112,216,136,220,103,44,2,220,22,22,191,100,50,245,93,176,39,78,244,152]) value100)=input112 := by rfl
#print axioms address112
def tree112 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [133,166,92,247,178,14,164,71,151,110,197,203,112,216,136,220,103,44,2,220,22,22,191,100,50,245,93,176,39,78,244,152])) tree100
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
def input113 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash113.message
def value113 : State := JFp_SHADigest.output JGf_TX2_M0.Hash113.result
theorem cast113_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash113.B00.input).map Fin.val=JGf_TX2_M0.Hash113.B00.input := by rfl
#print axioms cast113_0
theorem tail113 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash113.tail).map Fin.val=JGf_TX2_M0.Hash113.tail := by rfl
#print axioms tail113
theorem numeric113 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash113.message).map Fin.val=JGf_TX2_M0.Hash113.message := by
  simp only [JGf_TX2_M0.Hash113.message,JGf_TX2_M0.Hash113.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast113_0,tail113]
#print axioms numeric113
theorem hash113 : JFp_SHADigest.digest input113=value113 := by
  unfold input113 JFp_SHADigest.digest
  rw [numeric113,JGf_TX2_M0.Hash113.checked]
  rfl
#print axioms hash113
theorem address113 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [66,185,148,49,55,63,224,95,221,106,45,169,131,64,148,207,5,79,16,110,85,52,26,163,173,177,45,89,111,30,47,204]) value101)=input113 := by rfl
#print axioms address113
def tree113 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [66,185,148,49,55,63,224,95,221,106,45,169,131,64,148,207,5,79,16,110,85,52,26,163,173,177,45,89,111,30,47,204])) tree101
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
def input114 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash114.message
def value114 : State := JFp_SHADigest.output JGf_TX2_M0.Hash114.result
theorem cast114_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash114.B00.input).map Fin.val=JGf_TX2_M0.Hash114.B00.input := by rfl
#print axioms cast114_0
theorem tail114 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash114.tail).map Fin.val=JGf_TX2_M0.Hash114.tail := by rfl
#print axioms tail114
theorem numeric114 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash114.message).map Fin.val=JGf_TX2_M0.Hash114.message := by
  simp only [JGf_TX2_M0.Hash114.message,JGf_TX2_M0.Hash114.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast114_0,tail114]
#print axioms numeric114
theorem hash114 : JFp_SHADigest.digest input114=value114 := by
  unfold input114 JFp_SHADigest.digest
  rw [numeric114,JGf_TX2_M0.Hash114.checked]
  rfl
#print axioms hash114
theorem address114 : BinMerkle32Path.nodeInput (children value102 (JGc_TX2_HashBytes.state [203,231,182,96,201,188,17,123,246,219,105,254,212,38,128,220,25,18,216,70,109,209,62,47,85,82,139,104,54,108,26,95]))=input114 := by rfl
#print axioms address114
def tree114 : Tree := .branch tree102 (.supplied (JGc_TX2_HashBytes.state [203,231,182,96,201,188,17,123,246,219,105,254,212,38,128,220,25,18,216,70,109,209,62,47,85,82,139,104,54,108,26,95]))
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
def input115 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash115.message
def value115 : State := JFp_SHADigest.output JGf_TX2_M0.Hash115.result
theorem cast115_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash115.B00.input).map Fin.val=JGf_TX2_M0.Hash115.B00.input := by rfl
#print axioms cast115_0
theorem tail115 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash115.tail).map Fin.val=JGf_TX2_M0.Hash115.tail := by rfl
#print axioms tail115
theorem numeric115 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash115.message).map Fin.val=JGf_TX2_M0.Hash115.message := by
  simp only [JGf_TX2_M0.Hash115.message,JGf_TX2_M0.Hash115.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast115_0,tail115]
#print axioms numeric115
theorem hash115 : JFp_SHADigest.digest input115=value115 := by
  unfold input115 JFp_SHADigest.digest
  rw [numeric115,JGf_TX2_M0.Hash115.checked]
  rfl
#print axioms hash115
theorem address115 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [8,10,154,102,135,84,59,156,16,207,44,29,73,106,208,210,219,249,52,74,89,130,162,71,30,71,209,194,230,192,207,219]) value103)=input115 := by rfl
#print axioms address115
def tree115 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [8,10,154,102,135,84,59,156,16,207,44,29,73,106,208,210,219,249,52,74,89,130,162,71,30,71,209,194,230,192,207,219])) tree103
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
def input116 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash116.message
def value116 : State := JFp_SHADigest.output JGf_TX2_M0.Hash116.result
theorem cast116_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash116.B00.input).map Fin.val=JGf_TX2_M0.Hash116.B00.input := by rfl
#print axioms cast116_0
theorem tail116 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash116.tail).map Fin.val=JGf_TX2_M0.Hash116.tail := by rfl
#print axioms tail116
theorem numeric116 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash116.message).map Fin.val=JGf_TX2_M0.Hash116.message := by
  simp only [JGf_TX2_M0.Hash116.message,JGf_TX2_M0.Hash116.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast116_0,tail116]
#print axioms numeric116
theorem hash116 : JFp_SHADigest.digest input116=value116 := by
  unfold input116 JFp_SHADigest.digest
  rw [numeric116,JGf_TX2_M0.Hash116.checked]
  rfl
#print axioms hash116
theorem address116 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [240,111,122,80,145,91,112,149,1,108,228,205,17,59,20,157,121,182,38,17,182,149,228,59,217,0,133,119,93,88,71,12]) value104)=input116 := by rfl
#print axioms address116
def tree116 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [240,111,122,80,145,91,112,149,1,108,228,205,17,59,20,157,121,182,38,17,182,149,228,59,217,0,133,119,93,88,71,12])) tree104
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
def input117 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash117.message
def value117 : State := JFp_SHADigest.output JGf_TX2_M0.Hash117.result
theorem cast117_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash117.B00.input).map Fin.val=JGf_TX2_M0.Hash117.B00.input := by rfl
#print axioms cast117_0
theorem tail117 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash117.tail).map Fin.val=JGf_TX2_M0.Hash117.tail := by rfl
#print axioms tail117
theorem numeric117 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash117.message).map Fin.val=JGf_TX2_M0.Hash117.message := by
  simp only [JGf_TX2_M0.Hash117.message,JGf_TX2_M0.Hash117.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast117_0,tail117]
#print axioms numeric117
theorem hash117 : JFp_SHADigest.digest input117=value117 := by
  unfold input117 JFp_SHADigest.digest
  rw [numeric117,JGf_TX2_M0.Hash117.checked]
  rfl
#print axioms hash117
theorem address117 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [72,253,183,126,163,29,80,199,72,132,128,240,147,13,169,213,238,49,18,180,38,79,65,52,42,202,78,86,137,131,199,24]) value105)=input117 := by rfl
#print axioms address117
def tree117 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [72,253,183,126,163,29,80,199,72,132,128,240,147,13,169,213,238,49,18,180,38,79,65,52,42,202,78,86,137,131,199,24])) tree105
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
def input118 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash118.message
def value118 : State := JFp_SHADigest.output JGf_TX2_M0.Hash118.result
theorem cast118_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash118.B00.input).map Fin.val=JGf_TX2_M0.Hash118.B00.input := by rfl
#print axioms cast118_0
theorem tail118 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash118.tail).map Fin.val=JGf_TX2_M0.Hash118.tail := by rfl
#print axioms tail118
theorem numeric118 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash118.message).map Fin.val=JGf_TX2_M0.Hash118.message := by
  simp only [JGf_TX2_M0.Hash118.message,JGf_TX2_M0.Hash118.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast118_0,tail118]
#print axioms numeric118
theorem hash118 : JFp_SHADigest.digest input118=value118 := by
  unfold input118 JFp_SHADigest.digest
  rw [numeric118,JGf_TX2_M0.Hash118.checked]
  rfl
#print axioms hash118
theorem address118 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [33,112,127,42,228,224,95,157,136,181,107,4,15,173,123,113,22,13,51,115,167,196,208,116,229,137,5,14,34,253,89,94]) value106)=input118 := by rfl
#print axioms address118
def tree118 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [33,112,127,42,228,224,95,157,136,181,107,4,15,173,123,113,22,13,51,115,167,196,208,116,229,137,5,14,34,253,89,94])) tree106
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
def input119 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash119.message
def value119 : State := JFp_SHADigest.output JGf_TX2_M0.Hash119.result
theorem cast119_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash119.B00.input).map Fin.val=JGf_TX2_M0.Hash119.B00.input := by rfl
#print axioms cast119_0
theorem tail119 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash119.tail).map Fin.val=JGf_TX2_M0.Hash119.tail := by rfl
#print axioms tail119
theorem numeric119 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash119.message).map Fin.val=JGf_TX2_M0.Hash119.message := by
  simp only [JGf_TX2_M0.Hash119.message,JGf_TX2_M0.Hash119.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast119_0,tail119]
#print axioms numeric119
theorem hash119 : JFp_SHADigest.digest input119=value119 := by
  unfold input119 JFp_SHADigest.digest
  rw [numeric119,JGf_TX2_M0.Hash119.checked]
  rfl
#print axioms hash119
theorem address119 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [27,158,254,158,67,152,206,7,93,54,237,102,39,250,48,129,45,41,54,54,255,249,55,104,159,3,85,132,188,88,238,69]) value107)=input119 := by rfl
#print axioms address119
def tree119 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [27,158,254,158,67,152,206,7,93,54,237,102,39,250,48,129,45,41,54,54,255,249,55,104,159,3,85,132,188,88,238,69])) tree107
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
end AspisR1.JGf_TX2_M0Roots
end
