import NDO_JGf_TX2_M0Level09
import NDO_JGf_TX2_M0W043
import NDO_JGf_TX2_M0W044
import NDO_JGf_TX2_M0W045
import NDO_JGf_TX2_M0W046
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGf_TX2_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input132 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash132.message
def value132 : State := JFp_SHADigest.output JGf_TX2_M0.Hash132.result
theorem cast132_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash132.B00.input).map Fin.val=JGf_TX2_M0.Hash132.B00.input := by rfl
#print axioms cast132_0
theorem tail132 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash132.tail).map Fin.val=JGf_TX2_M0.Hash132.tail := by rfl
#print axioms tail132
theorem numeric132 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash132.message).map Fin.val=JGf_TX2_M0.Hash132.message := by
  simp only [JGf_TX2_M0.Hash132.message,JGf_TX2_M0.Hash132.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast132_0,tail132]
#print axioms numeric132
theorem hash132 : JFp_SHADigest.digest input132=value132 := by
  unfold input132 JFp_SHADigest.digest
  rw [numeric132,JGf_TX2_M0.Hash132.checked]
  rfl
#print axioms hash132
theorem address132 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [72,180,73,182,98,64,191,234,128,146,240,255,73,14,27,166,200,56,147,223,196,200,249,249,189,122,13,171,27,214,43,203]) value120)=input132 := by rfl
#print axioms address132
def tree132 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [72,180,73,182,98,64,191,234,128,146,240,255,73,14,27,166,200,56,147,223,196,200,249,249,189,122,13,171,27,214,43,203])) tree120
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
def input133 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash133.message
def value133 : State := JFp_SHADigest.output JGf_TX2_M0.Hash133.result
theorem cast133_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash133.B00.input).map Fin.val=JGf_TX2_M0.Hash133.B00.input := by rfl
#print axioms cast133_0
theorem tail133 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash133.tail).map Fin.val=JGf_TX2_M0.Hash133.tail := by rfl
#print axioms tail133
theorem numeric133 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash133.message).map Fin.val=JGf_TX2_M0.Hash133.message := by
  simp only [JGf_TX2_M0.Hash133.message,JGf_TX2_M0.Hash133.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast133_0,tail133]
#print axioms numeric133
theorem hash133 : JFp_SHADigest.digest input133=value133 := by
  unfold input133 JFp_SHADigest.digest
  rw [numeric133,JGf_TX2_M0.Hash133.checked]
  rfl
#print axioms hash133
theorem address133 : BinMerkle32Path.nodeInput (children value121 (JGc_TX2_HashBytes.state [99,55,47,196,216,220,150,214,26,215,49,37,196,159,43,69,134,69,125,176,189,7,116,111,19,162,247,218,179,95,57,101]))=input133 := by rfl
#print axioms address133
def tree133 : Tree := .branch tree121 (.supplied (JGc_TX2_HashBytes.state [99,55,47,196,216,220,150,214,26,215,49,37,196,159,43,69,134,69,125,176,189,7,116,111,19,162,247,218,179,95,57,101]))
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
def input134 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash134.message
def value134 : State := JFp_SHADigest.output JGf_TX2_M0.Hash134.result
theorem cast134_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash134.B00.input).map Fin.val=JGf_TX2_M0.Hash134.B00.input := by rfl
#print axioms cast134_0
theorem tail134 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash134.tail).map Fin.val=JGf_TX2_M0.Hash134.tail := by rfl
#print axioms tail134
theorem numeric134 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash134.message).map Fin.val=JGf_TX2_M0.Hash134.message := by
  simp only [JGf_TX2_M0.Hash134.message,JGf_TX2_M0.Hash134.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast134_0,tail134]
#print axioms numeric134
theorem hash134 : JFp_SHADigest.digest input134=value134 := by
  unfold input134 JFp_SHADigest.digest
  rw [numeric134,JGf_TX2_M0.Hash134.checked]
  rfl
#print axioms hash134
theorem address134 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [48,35,138,61,209,36,109,184,163,56,38,182,136,104,9,198,1,40,217,79,189,78,236,56,74,180,157,230,46,56,48,127]) value122)=input134 := by rfl
#print axioms address134
def tree134 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [48,35,138,61,209,36,109,184,163,56,38,182,136,104,9,198,1,40,217,79,189,78,236,56,74,180,157,230,46,56,48,127])) tree122
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
def input135 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash135.message
def value135 : State := JFp_SHADigest.output JGf_TX2_M0.Hash135.result
theorem cast135_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash135.B00.input).map Fin.val=JGf_TX2_M0.Hash135.B00.input := by rfl
#print axioms cast135_0
theorem tail135 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash135.tail).map Fin.val=JGf_TX2_M0.Hash135.tail := by rfl
#print axioms tail135
theorem numeric135 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash135.message).map Fin.val=JGf_TX2_M0.Hash135.message := by
  simp only [JGf_TX2_M0.Hash135.message,JGf_TX2_M0.Hash135.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast135_0,tail135]
#print axioms numeric135
theorem hash135 : JFp_SHADigest.digest input135=value135 := by
  unfold input135 JFp_SHADigest.digest
  rw [numeric135,JGf_TX2_M0.Hash135.checked]
  rfl
#print axioms hash135
theorem address135 : BinMerkle32Path.nodeInput (children value123 (JGc_TX2_HashBytes.state [184,223,76,18,255,19,236,254,70,250,44,16,118,252,48,207,204,62,99,98,225,145,168,186,25,132,2,159,114,128,37,127]))=input135 := by rfl
#print axioms address135
def tree135 : Tree := .branch tree123 (.supplied (JGc_TX2_HashBytes.state [184,223,76,18,255,19,236,254,70,250,44,16,118,252,48,207,204,62,99,98,225,145,168,186,25,132,2,159,114,128,37,127]))
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
def input136 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash136.message
def value136 : State := JFp_SHADigest.output JGf_TX2_M0.Hash136.result
theorem cast136_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash136.B00.input).map Fin.val=JGf_TX2_M0.Hash136.B00.input := by rfl
#print axioms cast136_0
theorem tail136 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash136.tail).map Fin.val=JGf_TX2_M0.Hash136.tail := by rfl
#print axioms tail136
theorem numeric136 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash136.message).map Fin.val=JGf_TX2_M0.Hash136.message := by
  simp only [JGf_TX2_M0.Hash136.message,JGf_TX2_M0.Hash136.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast136_0,tail136]
#print axioms numeric136
theorem hash136 : JFp_SHADigest.digest input136=value136 := by
  unfold input136 JFp_SHADigest.digest
  rw [numeric136,JGf_TX2_M0.Hash136.checked]
  rfl
#print axioms hash136
theorem address136 : BinMerkle32Path.nodeInput (children value124 (JGc_TX2_HashBytes.state [66,141,179,78,169,251,218,97,201,26,66,226,78,26,2,34,37,59,246,203,179,179,241,151,182,171,135,192,49,236,167,185]))=input136 := by rfl
#print axioms address136
def tree136 : Tree := .branch tree124 (.supplied (JGc_TX2_HashBytes.state [66,141,179,78,169,251,218,97,201,26,66,226,78,26,2,34,37,59,246,203,179,179,241,151,182,171,135,192,49,236,167,185]))
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
def input137 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash137.message
def value137 : State := JFp_SHADigest.output JGf_TX2_M0.Hash137.result
theorem cast137_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash137.B00.input).map Fin.val=JGf_TX2_M0.Hash137.B00.input := by rfl
#print axioms cast137_0
theorem tail137 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash137.tail).map Fin.val=JGf_TX2_M0.Hash137.tail := by rfl
#print axioms tail137
theorem numeric137 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash137.message).map Fin.val=JGf_TX2_M0.Hash137.message := by
  simp only [JGf_TX2_M0.Hash137.message,JGf_TX2_M0.Hash137.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast137_0,tail137]
#print axioms numeric137
theorem hash137 : JFp_SHADigest.digest input137=value137 := by
  unfold input137 JFp_SHADigest.digest
  rw [numeric137,JGf_TX2_M0.Hash137.checked]
  rfl
#print axioms hash137
theorem address137 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [41,177,207,57,62,0,184,61,82,15,215,73,118,152,135,82,134,32,219,151,133,84,187,130,80,72,107,237,131,208,37,192]) value125)=input137 := by rfl
#print axioms address137
def tree137 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [41,177,207,57,62,0,184,61,82,15,215,73,118,152,135,82,134,32,219,151,133,84,187,130,80,72,107,237,131,208,37,192])) tree125
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
def input138 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash138.message
def value138 : State := JFp_SHADigest.output JGf_TX2_M0.Hash138.result
theorem cast138_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash138.B00.input).map Fin.val=JGf_TX2_M0.Hash138.B00.input := by rfl
#print axioms cast138_0
theorem tail138 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash138.tail).map Fin.val=JGf_TX2_M0.Hash138.tail := by rfl
#print axioms tail138
theorem numeric138 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash138.message).map Fin.val=JGf_TX2_M0.Hash138.message := by
  simp only [JGf_TX2_M0.Hash138.message,JGf_TX2_M0.Hash138.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast138_0,tail138]
#print axioms numeric138
theorem hash138 : JFp_SHADigest.digest input138=value138 := by
  unfold input138 JFp_SHADigest.digest
  rw [numeric138,JGf_TX2_M0.Hash138.checked]
  rfl
#print axioms hash138
theorem address138 : BinMerkle32Path.nodeInput (children value126 (JGc_TX2_HashBytes.state [232,58,255,55,61,162,16,23,237,138,180,89,16,0,29,233,199,125,198,23,154,183,15,126,29,226,80,163,57,60,144,18]))=input138 := by rfl
#print axioms address138
def tree138 : Tree := .branch tree126 (.supplied (JGc_TX2_HashBytes.state [232,58,255,55,61,162,16,23,237,138,180,89,16,0,29,233,199,125,198,23,154,183,15,126,29,226,80,163,57,60,144,18]))
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
def input139 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash139.message
def value139 : State := JFp_SHADigest.output JGf_TX2_M0.Hash139.result
theorem cast139_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash139.B00.input).map Fin.val=JGf_TX2_M0.Hash139.B00.input := by rfl
#print axioms cast139_0
theorem tail139 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash139.tail).map Fin.val=JGf_TX2_M0.Hash139.tail := by rfl
#print axioms tail139
theorem numeric139 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash139.message).map Fin.val=JGf_TX2_M0.Hash139.message := by
  simp only [JGf_TX2_M0.Hash139.message,JGf_TX2_M0.Hash139.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast139_0,tail139]
#print axioms numeric139
theorem hash139 : JFp_SHADigest.digest input139=value139 := by
  unfold input139 JFp_SHADigest.digest
  rw [numeric139,JGf_TX2_M0.Hash139.checked]
  rfl
#print axioms hash139
theorem address139 : BinMerkle32Path.nodeInput (children value127 (JGc_TX2_HashBytes.state [66,135,130,77,225,162,97,219,9,212,25,0,174,230,39,177,29,144,180,21,29,206,227,123,53,59,149,186,161,243,86,37]))=input139 := by rfl
#print axioms address139
def tree139 : Tree := .branch tree127 (.supplied (JGc_TX2_HashBytes.state [66,135,130,77,225,162,97,219,9,212,25,0,174,230,39,177,29,144,180,21,29,206,227,123,53,59,149,186,161,243,86,37]))
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
def input140 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash140.message
def value140 : State := JFp_SHADigest.output JGf_TX2_M0.Hash140.result
theorem cast140_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash140.B00.input).map Fin.val=JGf_TX2_M0.Hash140.B00.input := by rfl
#print axioms cast140_0
theorem tail140 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash140.tail).map Fin.val=JGf_TX2_M0.Hash140.tail := by rfl
#print axioms tail140
theorem numeric140 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash140.message).map Fin.val=JGf_TX2_M0.Hash140.message := by
  simp only [JGf_TX2_M0.Hash140.message,JGf_TX2_M0.Hash140.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast140_0,tail140]
#print axioms numeric140
theorem hash140 : JFp_SHADigest.digest input140=value140 := by
  unfold input140 JFp_SHADigest.digest
  rw [numeric140,JGf_TX2_M0.Hash140.checked]
  rfl
#print axioms hash140
theorem address140 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [87,231,15,129,229,140,140,137,141,83,142,209,172,213,234,174,242,147,38,64,211,180,251,125,80,101,85,191,4,119,233,205]) value128)=input140 := by rfl
#print axioms address140
def tree140 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [87,231,15,129,229,140,140,137,141,83,142,209,172,213,234,174,242,147,38,64,211,180,251,125,80,101,85,191,4,119,233,205])) tree128
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
def input141 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash141.message
def value141 : State := JFp_SHADigest.output JGf_TX2_M0.Hash141.result
theorem cast141_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash141.B00.input).map Fin.val=JGf_TX2_M0.Hash141.B00.input := by rfl
#print axioms cast141_0
theorem tail141 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash141.tail).map Fin.val=JGf_TX2_M0.Hash141.tail := by rfl
#print axioms tail141
theorem numeric141 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash141.message).map Fin.val=JGf_TX2_M0.Hash141.message := by
  simp only [JGf_TX2_M0.Hash141.message,JGf_TX2_M0.Hash141.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast141_0,tail141]
#print axioms numeric141
theorem hash141 : JFp_SHADigest.digest input141=value141 := by
  unfold input141 JFp_SHADigest.digest
  rw [numeric141,JGf_TX2_M0.Hash141.checked]
  rfl
#print axioms hash141
theorem address141 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [46,88,184,203,19,143,21,236,210,222,11,211,12,28,213,15,25,253,11,68,231,193,149,194,181,144,125,71,175,74,186,244]) value129)=input141 := by rfl
#print axioms address141
def tree141 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [46,88,184,203,19,143,21,236,210,222,11,211,12,28,213,15,25,253,11,68,231,193,149,194,181,144,125,71,175,74,186,244])) tree129
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
def input142 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash142.message
def value142 : State := JFp_SHADigest.output JGf_TX2_M0.Hash142.result
theorem cast142_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash142.B00.input).map Fin.val=JGf_TX2_M0.Hash142.B00.input := by rfl
#print axioms cast142_0
theorem tail142 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash142.tail).map Fin.val=JGf_TX2_M0.Hash142.tail := by rfl
#print axioms tail142
theorem numeric142 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash142.message).map Fin.val=JGf_TX2_M0.Hash142.message := by
  simp only [JGf_TX2_M0.Hash142.message,JGf_TX2_M0.Hash142.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast142_0,tail142]
#print axioms numeric142
theorem hash142 : JFp_SHADigest.digest input142=value142 := by
  unfold input142 JFp_SHADigest.digest
  rw [numeric142,JGf_TX2_M0.Hash142.checked]
  rfl
#print axioms hash142
theorem address142 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [219,159,99,156,149,23,192,251,78,146,99,40,200,112,21,200,102,96,128,83,23,240,114,66,84,178,247,49,16,64,10,17]) value130)=input142 := by rfl
#print axioms address142
def tree142 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [219,159,99,156,149,23,192,251,78,146,99,40,200,112,21,200,102,96,128,83,23,240,114,66,84,178,247,49,16,64,10,17])) tree130
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
def input143 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash143.message
def value143 : State := JFp_SHADigest.output JGf_TX2_M0.Hash143.result
theorem cast143_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash143.B00.input).map Fin.val=JGf_TX2_M0.Hash143.B00.input := by rfl
#print axioms cast143_0
theorem tail143 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash143.tail).map Fin.val=JGf_TX2_M0.Hash143.tail := by rfl
#print axioms tail143
theorem numeric143 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash143.message).map Fin.val=JGf_TX2_M0.Hash143.message := by
  simp only [JGf_TX2_M0.Hash143.message,JGf_TX2_M0.Hash143.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast143_0,tail143]
#print axioms numeric143
theorem hash143 : JFp_SHADigest.digest input143=value143 := by
  unfold input143 JFp_SHADigest.digest
  rw [numeric143,JGf_TX2_M0.Hash143.checked]
  rfl
#print axioms hash143
theorem address143 : BinMerkle32Path.nodeInput (children value131 (JGc_TX2_HashBytes.state [90,100,221,216,88,163,24,57,180,29,244,239,26,122,234,171,251,20,109,18,152,138,5,195,6,172,202,58,41,146,6,210]))=input143 := by rfl
#print axioms address143
def tree143 : Tree := .branch tree131 (.supplied (JGc_TX2_HashBytes.state [90,100,221,216,88,163,24,57,180,29,244,239,26,122,234,171,251,20,109,18,152,138,5,195,6,172,202,58,41,146,6,210]))
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
end AspisR1.JGf_TX2_M0Roots
end
