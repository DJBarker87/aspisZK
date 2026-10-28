import NDO_JGc_TX2_M2Level09
import NDO_JGc_TX2_M2H128
import NDO_JGc_TX2_M2H132
import NDO_JGc_TX2_M2H136
import NDO_JGc_TX2_M2H140
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input131 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash131.message
def value131 : State := JFp_SHADigest.output JGc_TX2_M2.Hash131.result
theorem cast131_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash131.B00.input).map Fin.val=JGc_TX2_M2.Hash131.B00.input := by rfl
#print axioms cast131_0
theorem tail131 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash131.tail).map Fin.val=JGc_TX2_M2.Hash131.tail := by rfl
#print axioms tail131
theorem numeric131 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash131.message).map Fin.val=JGc_TX2_M2.Hash131.message := by
  simp only [JGc_TX2_M2.Hash131.message,JGc_TX2_M2.Hash131.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast131_0,tail131]
#print axioms numeric131
theorem hash131 : JFp_SHADigest.digest input131=value131 := by
  unfold input131 JFp_SHADigest.digest
  rw [numeric131,JGc_TX2_M2.Hash131.checked]
  rfl
#print axioms hash131
theorem address131 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [118,66,45,191,131,189,214,251,21,46,147,15,77,250,5,72,98,206,157,150,181,2,58,191,80,5,149,160,25,124,36,129]) value120)=input131 := by rfl
#print axioms address131
def tree131 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [118,66,45,191,131,189,214,251,21,46,147,15,77,250,5,72,98,206,157,150,181,2,58,191,80,5,149,160,25,124,36,129])) tree120
theorem root131 : root JFp_SHADigest.digest tree131=value131 := by
  rw [tree131,root,root120]
  exact (congrArg JFp_SHADigest.digest address131).trans hash131
#print axioms root131
theorem shape131 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 2048=tree131 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 2048)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 2048 (by decide),siblings 10 (by decide) 2048 (by decide)]
  rw [shape120 f g inputs siblings]
  rfl
#print axioms shape131
def input132 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash132.message
def value132 : State := JFp_SHADigest.output JGc_TX2_M2.Hash132.result
theorem cast132_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash132.B00.input).map Fin.val=JGc_TX2_M2.Hash132.B00.input := by rfl
#print axioms cast132_0
theorem tail132 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash132.tail).map Fin.val=JGc_TX2_M2.Hash132.tail := by rfl
#print axioms tail132
theorem numeric132 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash132.message).map Fin.val=JGc_TX2_M2.Hash132.message := by
  simp only [JGc_TX2_M2.Hash132.message,JGc_TX2_M2.Hash132.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast132_0,tail132]
#print axioms numeric132
theorem hash132 : JFp_SHADigest.digest input132=value132 := by
  unfold input132 JFp_SHADigest.digest
  rw [numeric132,JGc_TX2_M2.Hash132.checked]
  rfl
#print axioms hash132
theorem address132 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [13,182,99,127,33,239,245,120,186,144,205,27,143,155,40,187,1,115,188,146,244,172,189,77,161,204,177,75,200,203,31,114]) value121)=input132 := by rfl
#print axioms address132
def tree132 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [13,182,99,127,33,239,245,120,186,144,205,27,143,155,40,187,1,115,188,146,244,172,189,77,161,204,177,75,200,203,31,114])) tree121
theorem root132 : root JFp_SHADigest.digest tree132=value132 := by
  rw [tree132,root,root121]
  exact (congrArg JFp_SHADigest.digest address132).trans hash132
#print axioms root132
theorem shape132 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 4096=tree132 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 4096)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 4096 (by decide),siblings 10 (by decide) 4096 (by decide)]
  rw [shape121 f g inputs siblings]
  rfl
#print axioms shape132
def input133 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash133.message
def value133 : State := JFp_SHADigest.output JGc_TX2_M2.Hash133.result
theorem cast133_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash133.B00.input).map Fin.val=JGc_TX2_M2.Hash133.B00.input := by rfl
#print axioms cast133_0
theorem tail133 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash133.tail).map Fin.val=JGc_TX2_M2.Hash133.tail := by rfl
#print axioms tail133
theorem numeric133 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash133.message).map Fin.val=JGc_TX2_M2.Hash133.message := by
  simp only [JGc_TX2_M2.Hash133.message,JGc_TX2_M2.Hash133.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast133_0,tail133]
#print axioms numeric133
theorem hash133 : JFp_SHADigest.digest input133=value133 := by
  unfold input133 JFp_SHADigest.digest
  rw [numeric133,JGc_TX2_M2.Hash133.checked]
  rfl
#print axioms hash133
theorem address133 : BinMerkle32Path.nodeInput (children value122 (JGc_TX2_HashBytes.state [146,164,89,170,7,232,232,36,21,165,44,55,215,245,238,204,47,130,161,56,58,13,100,85,148,93,194,212,175,75,132,243]))=input133 := by rfl
#print axioms address133
def tree133 : Tree := .branch tree122 (.supplied (JGc_TX2_HashBytes.state [146,164,89,170,7,232,232,36,21,165,44,55,215,245,238,204,47,130,161,56,58,13,100,85,148,93,194,212,175,75,132,243]))
theorem root133 : root JFp_SHADigest.digest tree133=value133 := by
  rw [tree133,root,root122]
  exact (congrArg JFp_SHADigest.digest address133).trans hash133
#print axioms root133
theorem shape133 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 10240=tree133 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 10240)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape122 f g inputs siblings]
  rw [unoccupied f g 10 11264 (by decide),siblings 10 (by decide) 11264 (by decide)]
  rfl
#print axioms shape133
def input134 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash134.message
def value134 : State := JFp_SHADigest.output JGc_TX2_M2.Hash134.result
theorem cast134_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash134.B00.input).map Fin.val=JGc_TX2_M2.Hash134.B00.input := by rfl
#print axioms cast134_0
theorem tail134 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash134.tail).map Fin.val=JGc_TX2_M2.Hash134.tail := by rfl
#print axioms tail134
theorem numeric134 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash134.message).map Fin.val=JGc_TX2_M2.Hash134.message := by
  simp only [JGc_TX2_M2.Hash134.message,JGc_TX2_M2.Hash134.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast134_0,tail134]
#print axioms numeric134
theorem hash134 : JFp_SHADigest.digest input134=value134 := by
  unfold input134 JFp_SHADigest.digest
  rw [numeric134,JGc_TX2_M2.Hash134.checked]
  rfl
#print axioms hash134
theorem address134 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [206,135,85,133,68,177,239,151,67,38,254,200,44,43,85,148,131,212,94,195,61,239,118,216,105,79,51,182,62,253,52,13]) value123)=input134 := by rfl
#print axioms address134
def tree134 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [206,135,85,133,68,177,239,151,67,38,254,200,44,43,85,148,131,212,94,195,61,239,118,216,105,79,51,182,62,253,52,13])) tree123
theorem root134 : root JFp_SHADigest.digest tree134=value134 := by
  rw [tree134,root,root123]
  exact (congrArg JFp_SHADigest.digest address134).trans hash134
#print axioms root134
theorem shape134 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 12288=tree134 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 12288)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 12288 (by decide),siblings 10 (by decide) 12288 (by decide)]
  rw [shape123 f g inputs siblings]
  rfl
#print axioms shape134
def input135 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash135.message
def value135 : State := JFp_SHADigest.output JGc_TX2_M2.Hash135.result
theorem cast135_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash135.B00.input).map Fin.val=JGc_TX2_M2.Hash135.B00.input := by rfl
#print axioms cast135_0
theorem tail135 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash135.tail).map Fin.val=JGc_TX2_M2.Hash135.tail := by rfl
#print axioms tail135
theorem numeric135 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash135.message).map Fin.val=JGc_TX2_M2.Hash135.message := by
  simp only [JGc_TX2_M2.Hash135.message,JGc_TX2_M2.Hash135.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast135_0,tail135]
#print axioms numeric135
theorem hash135 : JFp_SHADigest.digest input135=value135 := by
  unfold input135 JFp_SHADigest.digest
  rw [numeric135,JGc_TX2_M2.Hash135.checked]
  rfl
#print axioms hash135
theorem address135 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [139,68,231,55,255,62,12,158,36,47,30,226,50,53,120,240,179,138,248,240,27,198,183,236,70,243,193,170,222,73,29,118]) value124)=input135 := by rfl
#print axioms address135
def tree135 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [139,68,231,55,255,62,12,158,36,47,30,226,50,53,120,240,179,138,248,240,27,198,183,236,70,243,193,170,222,73,29,118])) tree124
theorem root135 : root JFp_SHADigest.digest tree135=value135 := by
  rw [tree135,root,root124]
  exact (congrArg JFp_SHADigest.digest address135).trans hash135
#print axioms root135
theorem shape135 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 14336=tree135 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 14336)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 14336 (by decide),siblings 10 (by decide) 14336 (by decide)]
  rw [shape124 f g inputs siblings]
  rfl
#print axioms shape135
def input136 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash136.message
def value136 : State := JFp_SHADigest.output JGc_TX2_M2.Hash136.result
theorem cast136_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash136.B00.input).map Fin.val=JGc_TX2_M2.Hash136.B00.input := by rfl
#print axioms cast136_0
theorem tail136 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash136.tail).map Fin.val=JGc_TX2_M2.Hash136.tail := by rfl
#print axioms tail136
theorem numeric136 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash136.message).map Fin.val=JGc_TX2_M2.Hash136.message := by
  simp only [JGc_TX2_M2.Hash136.message,JGc_TX2_M2.Hash136.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast136_0,tail136]
#print axioms numeric136
theorem hash136 : JFp_SHADigest.digest input136=value136 := by
  unfold input136 JFp_SHADigest.digest
  rw [numeric136,JGc_TX2_M2.Hash136.checked]
  rfl
#print axioms hash136
theorem address136 : BinMerkle32Path.nodeInput (children value125 (JGc_TX2_HashBytes.state [40,62,29,29,171,128,93,62,151,133,236,13,67,157,193,122,122,193,249,26,97,185,32,106,101,74,234,215,244,154,188,171]))=input136 := by rfl
#print axioms address136
def tree136 : Tree := .branch tree125 (.supplied (JGc_TX2_HashBytes.state [40,62,29,29,171,128,93,62,151,133,236,13,67,157,193,122,122,193,249,26,97,185,32,106,101,74,234,215,244,154,188,171]))
theorem root136 : root JFp_SHADigest.digest tree136=value136 := by
  rw [tree136,root,root125]
  exact (congrArg JFp_SHADigest.digest address136).trans hash136
#print axioms root136
theorem shape136 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 32768=tree136 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 32768)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape125 f g inputs siblings]
  rw [unoccupied f g 10 33792 (by decide),siblings 10 (by decide) 33792 (by decide)]
  rfl
#print axioms shape136
def input137 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash137.message
def value137 : State := JFp_SHADigest.output JGc_TX2_M2.Hash137.result
theorem cast137_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash137.B00.input).map Fin.val=JGc_TX2_M2.Hash137.B00.input := by rfl
#print axioms cast137_0
theorem tail137 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash137.tail).map Fin.val=JGc_TX2_M2.Hash137.tail := by rfl
#print axioms tail137
theorem numeric137 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash137.message).map Fin.val=JGc_TX2_M2.Hash137.message := by
  simp only [JGc_TX2_M2.Hash137.message,JGc_TX2_M2.Hash137.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast137_0,tail137]
#print axioms numeric137
theorem hash137 : JFp_SHADigest.digest input137=value137 := by
  unfold input137 JFp_SHADigest.digest
  rw [numeric137,JGc_TX2_M2.Hash137.checked]
  rfl
#print axioms hash137
theorem address137 : BinMerkle32Path.nodeInput (children value126 (JGc_TX2_HashBytes.state [233,55,27,237,249,242,100,244,152,233,196,144,235,235,188,45,24,60,248,32,79,165,176,201,186,138,207,29,188,87,191,26]))=input137 := by rfl
#print axioms address137
def tree137 : Tree := .branch tree126 (.supplied (JGc_TX2_HashBytes.state [233,55,27,237,249,242,100,244,152,233,196,144,235,235,188,45,24,60,248,32,79,165,176,201,186,138,207,29,188,87,191,26]))
theorem root137 : root JFp_SHADigest.digest tree137=value137 := by
  rw [tree137,root,root126]
  exact (congrArg JFp_SHADigest.digest address137).trans hash137
#print axioms root137
theorem shape137 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 36864=tree137 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 36864)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape126 f g inputs siblings]
  rw [unoccupied f g 10 37888 (by decide),siblings 10 (by decide) 37888 (by decide)]
  rfl
#print axioms shape137
def input138 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash138.message
def value138 : State := JFp_SHADigest.output JGc_TX2_M2.Hash138.result
theorem cast138_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash138.B00.input).map Fin.val=JGc_TX2_M2.Hash138.B00.input := by rfl
#print axioms cast138_0
theorem tail138 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash138.tail).map Fin.val=JGc_TX2_M2.Hash138.tail := by rfl
#print axioms tail138
theorem numeric138 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash138.message).map Fin.val=JGc_TX2_M2.Hash138.message := by
  simp only [JGc_TX2_M2.Hash138.message,JGc_TX2_M2.Hash138.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast138_0,tail138]
#print axioms numeric138
theorem hash138 : JFp_SHADigest.digest input138=value138 := by
  unfold input138 JFp_SHADigest.digest
  rw [numeric138,JGc_TX2_M2.Hash138.checked]
  rfl
#print axioms hash138
theorem address138 : BinMerkle32Path.nodeInput (children value127 (JGc_TX2_HashBytes.state [184,10,86,251,254,61,159,179,41,92,94,241,151,243,23,3,198,154,172,68,148,202,189,43,208,185,144,44,251,111,18,170]))=input138 := by rfl
#print axioms address138
def tree138 : Tree := .branch tree127 (.supplied (JGc_TX2_HashBytes.state [184,10,86,251,254,61,159,179,41,92,94,241,151,243,23,3,198,154,172,68,148,202,189,43,208,185,144,44,251,111,18,170]))
theorem root138 : root JFp_SHADigest.digest tree138=value138 := by
  rw [tree138,root,root127]
  exact (congrArg JFp_SHADigest.digest address138).trans hash138
#print axioms root138
theorem shape138 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 40960=tree138 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 40960)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape127 f g inputs siblings]
  rw [unoccupied f g 10 41984 (by decide),siblings 10 (by decide) 41984 (by decide)]
  rfl
#print axioms shape138
def input139 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash139.message
def value139 : State := JFp_SHADigest.output JGc_TX2_M2.Hash139.result
theorem cast139_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash139.B00.input).map Fin.val=JGc_TX2_M2.Hash139.B00.input := by rfl
#print axioms cast139_0
theorem tail139 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash139.tail).map Fin.val=JGc_TX2_M2.Hash139.tail := by rfl
#print axioms tail139
theorem numeric139 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash139.message).map Fin.val=JGc_TX2_M2.Hash139.message := by
  simp only [JGc_TX2_M2.Hash139.message,JGc_TX2_M2.Hash139.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast139_0,tail139]
#print axioms numeric139
theorem hash139 : JFp_SHADigest.digest input139=value139 := by
  unfold input139 JFp_SHADigest.digest
  rw [numeric139,JGc_TX2_M2.Hash139.checked]
  rfl
#print axioms hash139
theorem address139 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [159,19,201,111,140,252,191,130,202,209,248,162,240,25,45,27,112,122,190,136,102,53,38,21,57,21,29,77,105,239,78,248]) value128)=input139 := by rfl
#print axioms address139
def tree139 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [159,19,201,111,140,252,191,130,202,209,248,162,240,25,45,27,112,122,190,136,102,53,38,21,57,21,29,77,105,239,78,248])) tree128
theorem root139 : root JFp_SHADigest.digest tree139=value139 := by
  rw [tree139,root,root128]
  exact (congrArg JFp_SHADigest.digest address139).trans hash139
#print axioms root139
theorem shape139 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 43008=tree139 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 43008)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 43008 (by decide),siblings 10 (by decide) 43008 (by decide)]
  rw [shape128 f g inputs siblings]
  rfl
#print axioms shape139
def input140 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash140.message
def value140 : State := JFp_SHADigest.output JGc_TX2_M2.Hash140.result
theorem cast140_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash140.B00.input).map Fin.val=JGc_TX2_M2.Hash140.B00.input := by rfl
#print axioms cast140_0
theorem tail140 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash140.tail).map Fin.val=JGc_TX2_M2.Hash140.tail := by rfl
#print axioms tail140
theorem numeric140 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash140.message).map Fin.val=JGc_TX2_M2.Hash140.message := by
  simp only [JGc_TX2_M2.Hash140.message,JGc_TX2_M2.Hash140.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast140_0,tail140]
#print axioms numeric140
theorem hash140 : JFp_SHADigest.digest input140=value140 := by
  unfold input140 JFp_SHADigest.digest
  rw [numeric140,JGc_TX2_M2.Hash140.checked]
  rfl
#print axioms hash140
theorem address140 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [94,118,78,239,2,8,1,25,176,182,215,190,219,234,105,116,65,90,245,216,64,126,39,42,42,110,88,104,137,73,20,66]) value129)=input140 := by rfl
#print axioms address140
def tree140 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [94,118,78,239,2,8,1,25,176,182,215,190,219,234,105,116,65,90,245,216,64,126,39,42,42,110,88,104,137,73,20,66])) tree129
theorem root140 : root JFp_SHADigest.digest tree140=value140 := by
  rw [tree140,root,root129]
  exact (congrArg JFp_SHADigest.digest address140).trans hash140
#print axioms root140
theorem shape140 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 45056=tree140 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 45056)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 45056 (by decide),siblings 10 (by decide) 45056 (by decide)]
  rw [shape129 f g inputs siblings]
  rfl
#print axioms shape140
def input141 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash141.message
def value141 : State := JFp_SHADigest.output JGc_TX2_M2.Hash141.result
theorem cast141_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash141.B00.input).map Fin.val=JGc_TX2_M2.Hash141.B00.input := by rfl
#print axioms cast141_0
theorem tail141 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash141.tail).map Fin.val=JGc_TX2_M2.Hash141.tail := by rfl
#print axioms tail141
theorem numeric141 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash141.message).map Fin.val=JGc_TX2_M2.Hash141.message := by
  simp only [JGc_TX2_M2.Hash141.message,JGc_TX2_M2.Hash141.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast141_0,tail141]
#print axioms numeric141
theorem hash141 : JFp_SHADigest.digest input141=value141 := by
  unfold input141 JFp_SHADigest.digest
  rw [numeric141,JGc_TX2_M2.Hash141.checked]
  rfl
#print axioms hash141
theorem address141 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [15,137,65,155,185,84,11,183,87,116,45,119,133,164,15,130,191,246,245,116,232,109,27,17,212,41,117,167,202,176,51,212]) value130)=input141 := by rfl
#print axioms address141
def tree141 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [15,137,65,155,185,84,11,183,87,116,45,119,133,164,15,130,191,246,245,116,232,109,27,17,212,41,117,167,202,176,51,212])) tree130
theorem root141 : root JFp_SHADigest.digest tree141=value141 := by
  rw [tree141,root,root130]
  exact (congrArg JFp_SHADigest.digest address141).trans hash141
#print axioms root141
theorem shape141 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 11 53248=tree141 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 11 53248)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 10 53248 (by decide),siblings 10 (by decide) 53248 (by decide)]
  rw [shape130 f g inputs siblings]
  rfl
#print axioms shape141
end AspisR1.JGc_TX2_M2Roots
end
