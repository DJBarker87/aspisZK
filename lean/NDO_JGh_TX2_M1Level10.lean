import NDO_JGh_TX2_M1Level09
import NDO_JGh_TX2_M1W034
import NDO_JGh_TX2_M1W035
import NDO_JGh_TX2_M1W036
import NDO_JGh_TX2_M1W037
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input132 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash132.message
def value132 : State := JFp_SHADigest.output JGh_TX2_M1.Hash132.result
theorem cast132_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash132.B00.input).map Fin.val=JGh_TX2_M1.Hash132.B00.input := by rfl
#print axioms cast132_0
theorem tail132 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash132.tail).map Fin.val=JGh_TX2_M1.Hash132.tail := by rfl
#print axioms tail132
theorem numeric132 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash132.message).map Fin.val=JGh_TX2_M1.Hash132.message := by
  simp only [JGh_TX2_M1.Hash132.message,JGh_TX2_M1.Hash132.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast132_0,tail132]
#print axioms numeric132
theorem hash132 : JFp_SHADigest.digest input132=value132 := by
  unfold input132 JFp_SHADigest.digest
  rw [numeric132,JGh_TX2_M1.Hash132.checked]
  rfl
#print axioms hash132
theorem address132 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [214,1,142,148,209,225,153,243,104,124,54,254,130,158,41,147,224,167,12,95,73,186,10,27,146,199,206,239,241,230,21,1]) value120)=input132 := by rfl
#print axioms address132
def tree132 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [214,1,142,148,209,225,153,243,104,124,54,254,130,158,41,147,224,167,12,95,73,186,10,27,146,199,206,239,241,230,21,1])) tree120
theorem root132 : root JFp_SHADigest.digest tree132=value132 := by
  rw [tree132,root,root120]
  exact (congrArg JFp_SHADigest.digest address132).trans hash132
#print axioms root132
theorem shape132 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 12288=tree132 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 12288)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 12288 (by decide),siblings 10 (by decide) 12288 (by decide)]
  rw [shape120 f g inputs siblings]
  rfl
#print axioms shape132
def input133 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash133.message
def value133 : State := JFp_SHADigest.output JGh_TX2_M1.Hash133.result
theorem cast133_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash133.B00.input).map Fin.val=JGh_TX2_M1.Hash133.B00.input := by rfl
#print axioms cast133_0
theorem tail133 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash133.tail).map Fin.val=JGh_TX2_M1.Hash133.tail := by rfl
#print axioms tail133
theorem numeric133 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash133.message).map Fin.val=JGh_TX2_M1.Hash133.message := by
  simp only [JGh_TX2_M1.Hash133.message,JGh_TX2_M1.Hash133.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast133_0,tail133]
#print axioms numeric133
theorem hash133 : JFp_SHADigest.digest input133=value133 := by
  unfold input133 JFp_SHADigest.digest
  rw [numeric133,JGh_TX2_M1.Hash133.checked]
  rfl
#print axioms hash133
theorem address133 : BinMerkle32Path.nodeInput (children value121 (JGc_TX2_HashBytes.state [22,58,92,37,133,168,27,180,9,74,169,17,60,144,184,205,205,168,118,146,189,175,80,131,216,0,29,32,254,203,206,245]))=input133 := by rfl
#print axioms address133
def tree133 : Tree := .branch tree121 (.supplied (JGc_TX2_HashBytes.state [22,58,92,37,133,168,27,180,9,74,169,17,60,144,184,205,205,168,118,146,189,175,80,131,216,0,29,32,254,203,206,245]))
theorem root133 : root JFp_SHADigest.digest tree133=value133 := by
  rw [tree133,root,root121]
  exact (congrArg JFp_SHADigest.digest address133).trans hash133
#print axioms root133
theorem shape133 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 20480=tree133 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 20480)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape121 f g inputs siblings]
  rw [unoccupied f g 10 21504 (by decide),siblings 10 (by decide) 21504 (by decide)]
  rfl
#print axioms shape133
def input134 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash134.message
def value134 : State := JFp_SHADigest.output JGh_TX2_M1.Hash134.result
theorem cast134_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash134.B00.input).map Fin.val=JGh_TX2_M1.Hash134.B00.input := by rfl
#print axioms cast134_0
theorem tail134 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash134.tail).map Fin.val=JGh_TX2_M1.Hash134.tail := by rfl
#print axioms tail134
theorem numeric134 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash134.message).map Fin.val=JGh_TX2_M1.Hash134.message := by
  simp only [JGh_TX2_M1.Hash134.message,JGh_TX2_M1.Hash134.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast134_0,tail134]
#print axioms numeric134
theorem hash134 : JFp_SHADigest.digest input134=value134 := by
  unfold input134 JFp_SHADigest.digest
  rw [numeric134,JGh_TX2_M1.Hash134.checked]
  rfl
#print axioms hash134
theorem address134 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [79,124,128,61,34,78,188,8,242,55,211,75,56,5,40,114,196,103,44,6,167,253,195,250,253,133,95,175,150,246,196,27]) value122)=input134 := by rfl
#print axioms address134
def tree134 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [79,124,128,61,34,78,188,8,242,55,211,75,56,5,40,114,196,103,44,6,167,253,195,250,253,133,95,175,150,246,196,27])) tree122
theorem root134 : root JFp_SHADigest.digest tree134=value134 := by
  rw [tree134,root,root122]
  exact (congrArg JFp_SHADigest.digest address134).trans hash134
#print axioms root134
theorem shape134 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 40960=tree134 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 40960)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 40960 (by decide),siblings 10 (by decide) 40960 (by decide)]
  rw [shape122 f g inputs siblings]
  rfl
#print axioms shape134
def input135 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash135.message
def value135 : State := JFp_SHADigest.output JGh_TX2_M1.Hash135.result
theorem cast135_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash135.B00.input).map Fin.val=JGh_TX2_M1.Hash135.B00.input := by rfl
#print axioms cast135_0
theorem tail135 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash135.tail).map Fin.val=JGh_TX2_M1.Hash135.tail := by rfl
#print axioms tail135
theorem numeric135 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash135.message).map Fin.val=JGh_TX2_M1.Hash135.message := by
  simp only [JGh_TX2_M1.Hash135.message,JGh_TX2_M1.Hash135.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast135_0,tail135]
#print axioms numeric135
theorem hash135 : JFp_SHADigest.digest input135=value135 := by
  unfold input135 JFp_SHADigest.digest
  rw [numeric135,JGh_TX2_M1.Hash135.checked]
  rfl
#print axioms hash135
theorem address135 : BinMerkle32Path.nodeInput (children value123 (JGc_TX2_HashBytes.state [93,176,85,114,2,120,79,71,60,85,183,175,176,8,78,63,86,157,192,86,180,50,223,29,35,193,19,180,187,176,195,70]))=input135 := by rfl
#print axioms address135
def tree135 : Tree := .branch tree123 (.supplied (JGc_TX2_HashBytes.state [93,176,85,114,2,120,79,71,60,85,183,175,176,8,78,63,86,157,192,86,180,50,223,29,35,193,19,180,187,176,195,70]))
theorem root135 : root JFp_SHADigest.digest tree135=value135 := by
  rw [tree135,root,root123]
  exact (congrArg JFp_SHADigest.digest address135).trans hash135
#print axioms root135
theorem shape135 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 55296=tree135 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 55296)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape123 f g inputs siblings]
  rw [unoccupied f g 10 56320 (by decide),siblings 10 (by decide) 56320 (by decide)]
  rfl
#print axioms shape135
def input136 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash136.message
def value136 : State := JFp_SHADigest.output JGh_TX2_M1.Hash136.result
theorem cast136_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash136.B00.input).map Fin.val=JGh_TX2_M1.Hash136.B00.input := by rfl
#print axioms cast136_0
theorem tail136 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash136.tail).map Fin.val=JGh_TX2_M1.Hash136.tail := by rfl
#print axioms tail136
theorem numeric136 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash136.message).map Fin.val=JGh_TX2_M1.Hash136.message := by
  simp only [JGh_TX2_M1.Hash136.message,JGh_TX2_M1.Hash136.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast136_0,tail136]
#print axioms numeric136
theorem hash136 : JFp_SHADigest.digest input136=value136 := by
  unfold input136 JFp_SHADigest.digest
  rw [numeric136,JGh_TX2_M1.Hash136.checked]
  rfl
#print axioms hash136
theorem address136 : BinMerkle32Path.nodeInput (children value124 (JGc_TX2_HashBytes.state [224,211,71,251,191,56,158,1,191,77,88,50,103,70,77,204,28,98,23,82,3,200,112,59,180,176,22,69,125,99,123,32]))=input136 := by rfl
#print axioms address136
def tree136 : Tree := .branch tree124 (.supplied (JGc_TX2_HashBytes.state [224,211,71,251,191,56,158,1,191,77,88,50,103,70,77,204,28,98,23,82,3,200,112,59,180,176,22,69,125,99,123,32]))
theorem root136 : root JFp_SHADigest.digest tree136=value136 := by
  rw [tree136,root,root124]
  exact (congrArg JFp_SHADigest.digest address136).trans hash136
#print axioms root136
theorem shape136 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 63488=tree136 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 63488)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape124 f g inputs siblings]
  rw [unoccupied f g 10 64512 (by decide),siblings 10 (by decide) 64512 (by decide)]
  rfl
#print axioms shape136
def input137 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash137.message
def value137 : State := JFp_SHADigest.output JGh_TX2_M1.Hash137.result
theorem cast137_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash137.B00.input).map Fin.val=JGh_TX2_M1.Hash137.B00.input := by rfl
#print axioms cast137_0
theorem tail137 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash137.tail).map Fin.val=JGh_TX2_M1.Hash137.tail := by rfl
#print axioms tail137
theorem numeric137 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash137.message).map Fin.val=JGh_TX2_M1.Hash137.message := by
  simp only [JGh_TX2_M1.Hash137.message,JGh_TX2_M1.Hash137.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast137_0,tail137]
#print axioms numeric137
theorem hash137 : JFp_SHADigest.digest input137=value137 := by
  unfold input137 JFp_SHADigest.digest
  rw [numeric137,JGh_TX2_M1.Hash137.checked]
  rfl
#print axioms hash137
theorem address137 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [48,70,166,177,18,169,52,0,34,185,101,251,162,104,216,157,41,217,181,189,98,170,156,72,200,109,198,130,61,106,58,105]) value125)=input137 := by rfl
#print axioms address137
def tree137 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [48,70,166,177,18,169,52,0,34,185,101,251,162,104,216,157,41,217,181,189,98,170,156,72,200,109,198,130,61,106,58,105])) tree125
theorem root137 : root JFp_SHADigest.digest tree137=value137 := by
  rw [tree137,root,root125]
  exact (congrArg JFp_SHADigest.digest address137).trans hash137
#print axioms root137
theorem shape137 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 131072=tree137 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 131072)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 131072 (by decide),siblings 10 (by decide) 131072 (by decide)]
  rw [shape125 f g inputs siblings]
  rfl
#print axioms shape137
def input138 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash138.message
def value138 : State := JFp_SHADigest.output JGh_TX2_M1.Hash138.result
theorem cast138_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash138.B00.input).map Fin.val=JGh_TX2_M1.Hash138.B00.input := by rfl
#print axioms cast138_0
theorem tail138 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash138.tail).map Fin.val=JGh_TX2_M1.Hash138.tail := by rfl
#print axioms tail138
theorem numeric138 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash138.message).map Fin.val=JGh_TX2_M1.Hash138.message := by
  simp only [JGh_TX2_M1.Hash138.message,JGh_TX2_M1.Hash138.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast138_0,tail138]
#print axioms numeric138
theorem hash138 : JFp_SHADigest.digest input138=value138 := by
  unfold input138 JFp_SHADigest.digest
  rw [numeric138,JGh_TX2_M1.Hash138.checked]
  rfl
#print axioms hash138
theorem address138 : BinMerkle32Path.nodeInput (children value126 (JGc_TX2_HashBytes.state [44,35,223,34,50,8,216,99,111,43,91,15,12,172,116,163,76,26,98,99,33,52,121,79,188,179,103,165,39,204,198,209]))=input138 := by rfl
#print axioms address138
def tree138 : Tree := .branch tree126 (.supplied (JGc_TX2_HashBytes.state [44,35,223,34,50,8,216,99,111,43,91,15,12,172,116,163,76,26,98,99,33,52,121,79,188,179,103,165,39,204,198,209]))
theorem root138 : root JFp_SHADigest.digest tree138=value138 := by
  rw [tree138,root,root126]
  exact (congrArg JFp_SHADigest.digest address138).trans hash138
#print axioms root138
theorem shape138 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 149504=tree138 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 149504)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape126 f g inputs siblings]
  rw [unoccupied f g 10 150528 (by decide),siblings 10 (by decide) 150528 (by decide)]
  rfl
#print axioms shape138
def input139 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash139.message
def value139 : State := JFp_SHADigest.output JGh_TX2_M1.Hash139.result
theorem cast139_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash139.B00.input).map Fin.val=JGh_TX2_M1.Hash139.B00.input := by rfl
#print axioms cast139_0
theorem tail139 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash139.tail).map Fin.val=JGh_TX2_M1.Hash139.tail := by rfl
#print axioms tail139
theorem numeric139 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash139.message).map Fin.val=JGh_TX2_M1.Hash139.message := by
  simp only [JGh_TX2_M1.Hash139.message,JGh_TX2_M1.Hash139.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast139_0,tail139]
#print axioms numeric139
theorem hash139 : JFp_SHADigest.digest input139=value139 := by
  unfold input139 JFp_SHADigest.digest
  rw [numeric139,JGh_TX2_M1.Hash139.checked]
  rfl
#print axioms hash139
theorem address139 : BinMerkle32Path.nodeInput (children value127 (JGc_TX2_HashBytes.state [194,186,133,142,40,36,51,31,17,148,199,89,78,189,142,237,50,64,225,196,161,189,3,136,73,18,22,74,83,158,252,200]))=input139 := by rfl
#print axioms address139
def tree139 : Tree := .branch tree127 (.supplied (JGc_TX2_HashBytes.state [194,186,133,142,40,36,51,31,17,148,199,89,78,189,142,237,50,64,225,196,161,189,3,136,73,18,22,74,83,158,252,200]))
theorem root139 : root JFp_SHADigest.digest tree139=value139 := by
  rw [tree139,root,root127]
  exact (congrArg JFp_SHADigest.digest address139).trans hash139
#print axioms root139
theorem shape139 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 165888=tree139 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 165888)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape127 f g inputs siblings]
  rw [unoccupied f g 10 166912 (by decide),siblings 10 (by decide) 166912 (by decide)]
  rfl
#print axioms shape139
def input140 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash140.message
def value140 : State := JFp_SHADigest.output JGh_TX2_M1.Hash140.result
theorem cast140_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash140.B00.input).map Fin.val=JGh_TX2_M1.Hash140.B00.input := by rfl
#print axioms cast140_0
theorem tail140 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash140.tail).map Fin.val=JGh_TX2_M1.Hash140.tail := by rfl
#print axioms tail140
theorem numeric140 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash140.message).map Fin.val=JGh_TX2_M1.Hash140.message := by
  simp only [JGh_TX2_M1.Hash140.message,JGh_TX2_M1.Hash140.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast140_0,tail140]
#print axioms numeric140
theorem hash140 : JFp_SHADigest.digest input140=value140 := by
  unfold input140 JFp_SHADigest.digest
  rw [numeric140,JGh_TX2_M1.Hash140.checked]
  rfl
#print axioms hash140
theorem address140 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [248,241,48,46,44,82,165,5,44,34,69,254,237,174,139,96,156,14,30,177,188,165,205,250,99,16,168,244,45,11,16,23]) value128)=input140 := by rfl
#print axioms address140
def tree140 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [248,241,48,46,44,82,165,5,44,34,69,254,237,174,139,96,156,14,30,177,188,165,205,250,99,16,168,244,45,11,16,23])) tree128
theorem root140 : root JFp_SHADigest.digest tree140=value140 := by
  rw [tree140,root,root128]
  exact (congrArg JFp_SHADigest.digest address140).trans hash140
#print axioms root140
theorem shape140 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 176128=tree140 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 176128)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 176128 (by decide),siblings 10 (by decide) 176128 (by decide)]
  rw [shape128 f g inputs siblings]
  rfl
#print axioms shape140
def input141 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash141.message
def value141 : State := JFp_SHADigest.output JGh_TX2_M1.Hash141.result
theorem cast141_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash141.B00.input).map Fin.val=JGh_TX2_M1.Hash141.B00.input := by rfl
#print axioms cast141_0
theorem tail141 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash141.tail).map Fin.val=JGh_TX2_M1.Hash141.tail := by rfl
#print axioms tail141
theorem numeric141 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash141.message).map Fin.val=JGh_TX2_M1.Hash141.message := by
  simp only [JGh_TX2_M1.Hash141.message,JGh_TX2_M1.Hash141.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast141_0,tail141]
#print axioms numeric141
theorem hash141 : JFp_SHADigest.digest input141=value141 := by
  unfold input141 JFp_SHADigest.digest
  rw [numeric141,JGh_TX2_M1.Hash141.checked]
  rfl
#print axioms hash141
theorem address141 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [207,109,113,42,136,235,167,31,40,145,169,101,27,31,13,234,244,215,141,151,108,9,61,116,189,208,82,164,126,234,27,199]) value129)=input141 := by rfl
#print axioms address141
def tree141 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [207,109,113,42,136,235,167,31,40,145,169,101,27,31,13,234,244,215,141,151,108,9,61,116,189,208,82,164,126,234,27,199])) tree129
theorem root141 : root JFp_SHADigest.digest tree141=value141 := by
  rw [tree141,root,root129]
  exact (congrArg JFp_SHADigest.digest address141).trans hash141
#print axioms root141
theorem shape141 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 178176=tree141 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 178176)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 178176 (by decide),siblings 10 (by decide) 178176 (by decide)]
  rw [shape129 f g inputs siblings]
  rfl
#print axioms shape141
def input142 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash142.message
def value142 : State := JFp_SHADigest.output JGh_TX2_M1.Hash142.result
theorem cast142_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash142.B00.input).map Fin.val=JGh_TX2_M1.Hash142.B00.input := by rfl
#print axioms cast142_0
theorem tail142 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash142.tail).map Fin.val=JGh_TX2_M1.Hash142.tail := by rfl
#print axioms tail142
theorem numeric142 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash142.message).map Fin.val=JGh_TX2_M1.Hash142.message := by
  simp only [JGh_TX2_M1.Hash142.message,JGh_TX2_M1.Hash142.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast142_0,tail142]
#print axioms numeric142
theorem hash142 : JFp_SHADigest.digest input142=value142 := by
  unfold input142 JFp_SHADigest.digest
  rw [numeric142,JGh_TX2_M1.Hash142.checked]
  rfl
#print axioms hash142
theorem address142 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [110,180,71,25,81,18,23,253,159,228,72,207,65,211,175,217,223,107,65,230,153,157,45,84,180,169,158,74,218,228,242,31]) value130)=input142 := by rfl
#print axioms address142
def tree142 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [110,180,71,25,81,18,23,253,159,228,72,207,65,211,175,217,223,107,65,230,153,157,45,84,180,169,158,74,218,228,242,31])) tree130
theorem root142 : root JFp_SHADigest.digest tree142=value142 := by
  rw [tree142,root,root130]
  exact (congrArg JFp_SHADigest.digest address142).trans hash142
#print axioms root142
theorem shape142 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 184320=tree142 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 184320)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 184320 (by decide),siblings 10 (by decide) 184320 (by decide)]
  rw [shape130 f g inputs siblings]
  rfl
#print axioms shape142
def input143 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash143.message
def value143 : State := JFp_SHADigest.output JGh_TX2_M1.Hash143.result
theorem cast143_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash143.B00.input).map Fin.val=JGh_TX2_M1.Hash143.B00.input := by rfl
#print axioms cast143_0
theorem tail143 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash143.tail).map Fin.val=JGh_TX2_M1.Hash143.tail := by rfl
#print axioms tail143
theorem numeric143 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash143.message).map Fin.val=JGh_TX2_M1.Hash143.message := by
  simp only [JGh_TX2_M1.Hash143.message,JGh_TX2_M1.Hash143.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast143_0,tail143]
#print axioms numeric143
theorem hash143 : JFp_SHADigest.digest input143=value143 := by
  unfold input143 JFp_SHADigest.digest
  rw [numeric143,JGh_TX2_M1.Hash143.checked]
  rfl
#print axioms hash143
theorem address143 : BinMerkle32Path.nodeInput (children value131 (JGc_TX2_HashBytes.state [90,176,120,28,113,204,45,102,181,106,125,21,214,97,153,130,219,198,138,161,135,41,42,89,10,58,45,221,28,120,96,89]))=input143 := by rfl
#print axioms address143
def tree143 : Tree := .branch tree131 (.supplied (JGc_TX2_HashBytes.state [90,176,120,28,113,204,45,102,181,106,125,21,214,97,153,130,219,198,138,161,135,41,42,89,10,58,45,221,28,120,96,89]))
theorem root143 : root JFp_SHADigest.digest tree143=value143 := by
  rw [tree143,root,root131]
  exact (congrArg JFp_SHADigest.digest address143).trans hash143
#print axioms root143
theorem shape143 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 217088=tree143 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 217088)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape131 f g inputs siblings]
  rw [unoccupied f g 10 218112 (by decide),siblings 10 (by decide) 218112 (by decide)]
  rfl
#print axioms shape143
end AspisR1.JGh_TX2_M1Roots
end
