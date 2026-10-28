import NDO_JGf_TX2_M0Level10
import NDO_JGf_TX2_M0W046
import NDO_JGf_TX2_M0W047
import NDO_JGf_TX2_M0W048
import NDO_JGf_TX2_M0W049
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGf_TX2_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input144 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash144.message
def value144 : State := JFp_SHADigest.output JGf_TX2_M0.Hash144.result
theorem cast144_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash144.B00.input).map Fin.val=JGf_TX2_M0.Hash144.B00.input := by rfl
#print axioms cast144_0
theorem tail144 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash144.tail).map Fin.val=JGf_TX2_M0.Hash144.tail := by rfl
#print axioms tail144
theorem numeric144 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash144.message).map Fin.val=JGf_TX2_M0.Hash144.message := by
  simp only [JGf_TX2_M0.Hash144.message,JGf_TX2_M0.Hash144.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast144_0,tail144]
#print axioms numeric144
theorem hash144 : JFp_SHADigest.digest input144=value144 := by
  unfold input144 JFp_SHADigest.digest
  rw [numeric144,JGf_TX2_M0.Hash144.checked]
  rfl
#print axioms hash144
theorem address144 : BinMerkle32Path.nodeInput (children value132 (JGc_TX2_HashBytes.state [114,148,20,49,255,49,68,76,135,83,19,44,119,158,59,216,21,44,122,133,175,18,178,173,193,9,78,227,133,100,104,175]))=input144 := by rfl
#print axioms address144
def tree144 : Tree := .branch tree132 (.supplied (JGc_TX2_HashBytes.state [114,148,20,49,255,49,68,76,135,83,19,44,119,158,59,216,21,44,122,133,175,18,178,173,193,9,78,227,133,100,104,175]))
theorem root144 : root JFp_SHADigest.digest tree144=value144 := by
  rw [tree144,root,root132]
  exact (congrArg JFp_SHADigest.digest address144).trans hash144
#print axioms root144
theorem shape144 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 12288=tree144 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 12288)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape132 f g inputs siblings]
  rw [unoccupied f g 11 14336 (by decide),siblings 11 (by decide) 14336 (by decide)]
  rfl
#print axioms shape144
def input145 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash145.message
def value145 : State := JFp_SHADigest.output JGf_TX2_M0.Hash145.result
theorem cast145_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash145.B00.input).map Fin.val=JGf_TX2_M0.Hash145.B00.input := by rfl
#print axioms cast145_0
theorem tail145 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash145.tail).map Fin.val=JGf_TX2_M0.Hash145.tail := by rfl
#print axioms tail145
theorem numeric145 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash145.message).map Fin.val=JGf_TX2_M0.Hash145.message := by
  simp only [JGf_TX2_M0.Hash145.message,JGf_TX2_M0.Hash145.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast145_0,tail145]
#print axioms numeric145
theorem hash145 : JFp_SHADigest.digest input145=value145 := by
  unfold input145 JFp_SHADigest.digest
  rw [numeric145,JGf_TX2_M0.Hash145.checked]
  rfl
#print axioms hash145
theorem address145 : BinMerkle32Path.nodeInput (children value133 (JGc_TX2_HashBytes.state [194,173,246,67,251,43,43,94,70,203,231,233,80,70,102,153,34,19,96,79,94,88,232,230,122,173,120,195,154,203,134,114]))=input145 := by rfl
#print axioms address145
def tree145 : Tree := .branch tree133 (.supplied (JGc_TX2_HashBytes.state [194,173,246,67,251,43,43,94,70,203,231,233,80,70,102,153,34,19,96,79,94,88,232,230,122,173,120,195,154,203,134,114]))
theorem root145 : root JFp_SHADigest.digest tree145=value145 := by
  rw [tree145,root,root133]
  exact (congrArg JFp_SHADigest.digest address145).trans hash145
#print axioms root145
theorem shape145 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 20480=tree145 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 20480)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape133 f g inputs siblings]
  rw [unoccupied f g 11 22528 (by decide),siblings 11 (by decide) 22528 (by decide)]
  rfl
#print axioms shape145
def input146 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash146.message
def value146 : State := JFp_SHADigest.output JGf_TX2_M0.Hash146.result
theorem cast146_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash146.B00.input).map Fin.val=JGf_TX2_M0.Hash146.B00.input := by rfl
#print axioms cast146_0
theorem tail146 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash146.tail).map Fin.val=JGf_TX2_M0.Hash146.tail := by rfl
#print axioms tail146
theorem numeric146 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash146.message).map Fin.val=JGf_TX2_M0.Hash146.message := by
  simp only [JGf_TX2_M0.Hash146.message,JGf_TX2_M0.Hash146.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast146_0,tail146]
#print axioms numeric146
theorem hash146 : JFp_SHADigest.digest input146=value146 := by
  unfold input146 JFp_SHADigest.digest
  rw [numeric146,JGf_TX2_M0.Hash146.checked]
  rfl
#print axioms hash146
theorem address146 : BinMerkle32Path.nodeInput (children value134 (JGc_TX2_HashBytes.state [243,50,132,14,129,195,144,44,143,138,67,220,184,178,3,248,231,245,215,8,226,150,46,136,109,71,173,21,51,6,233,194]))=input146 := by rfl
#print axioms address146
def tree146 : Tree := .branch tree134 (.supplied (JGc_TX2_HashBytes.state [243,50,132,14,129,195,144,44,143,138,67,220,184,178,3,248,231,245,215,8,226,150,46,136,109,71,173,21,51,6,233,194]))
theorem root146 : root JFp_SHADigest.digest tree146=value146 := by
  rw [tree146,root,root134]
  exact (congrArg JFp_SHADigest.digest address146).trans hash146
#print axioms root146
theorem shape146 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 40960=tree146 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 40960)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape134 f g inputs siblings]
  rw [unoccupied f g 11 43008 (by decide),siblings 11 (by decide) 43008 (by decide)]
  rfl
#print axioms shape146
def input147 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash147.message
def value147 : State := JFp_SHADigest.output JGf_TX2_M0.Hash147.result
theorem cast147_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash147.B00.input).map Fin.val=JGf_TX2_M0.Hash147.B00.input := by rfl
#print axioms cast147_0
theorem tail147 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash147.tail).map Fin.val=JGf_TX2_M0.Hash147.tail := by rfl
#print axioms tail147
theorem numeric147 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash147.message).map Fin.val=JGf_TX2_M0.Hash147.message := by
  simp only [JGf_TX2_M0.Hash147.message,JGf_TX2_M0.Hash147.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast147_0,tail147]
#print axioms numeric147
theorem hash147 : JFp_SHADigest.digest input147=value147 := by
  unfold input147 JFp_SHADigest.digest
  rw [numeric147,JGf_TX2_M0.Hash147.checked]
  rfl
#print axioms hash147
theorem address147 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [117,192,235,113,234,139,59,254,172,59,30,3,93,90,250,191,137,92,138,15,105,122,132,53,81,24,248,18,52,12,219,46]) value135)=input147 := by rfl
#print axioms address147
def tree147 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [117,192,235,113,234,139,59,254,172,59,30,3,93,90,250,191,137,92,138,15,105,122,132,53,81,24,248,18,52,12,219,46])) tree135
theorem root147 : root JFp_SHADigest.digest tree147=value147 := by
  rw [tree147,root,root135]
  exact (congrArg JFp_SHADigest.digest address147).trans hash147
#print axioms root147
theorem shape147 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 53248=tree147 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 53248)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 11 53248 (by decide),siblings 11 (by decide) 53248 (by decide)]
  rw [shape135 f g inputs siblings]
  rfl
#print axioms shape147
def input148 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash148.message
def value148 : State := JFp_SHADigest.output JGf_TX2_M0.Hash148.result
theorem cast148_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash148.B00.input).map Fin.val=JGf_TX2_M0.Hash148.B00.input := by rfl
#print axioms cast148_0
theorem tail148 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash148.tail).map Fin.val=JGf_TX2_M0.Hash148.tail := by rfl
#print axioms tail148
theorem numeric148 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash148.message).map Fin.val=JGf_TX2_M0.Hash148.message := by
  simp only [JGf_TX2_M0.Hash148.message,JGf_TX2_M0.Hash148.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast148_0,tail148]
#print axioms numeric148
theorem hash148 : JFp_SHADigest.digest input148=value148 := by
  unfold input148 JFp_SHADigest.digest
  rw [numeric148,JGf_TX2_M0.Hash148.checked]
  rfl
#print axioms hash148
theorem address148 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [160,58,63,142,126,197,86,149,245,225,86,191,132,55,153,31,169,133,207,36,139,134,11,148,28,196,194,144,52,30,99,207]) value136)=input148 := by rfl
#print axioms address148
def tree148 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [160,58,63,142,126,197,86,149,245,225,86,191,132,55,153,31,169,133,207,36,139,134,11,148,28,196,194,144,52,30,99,207])) tree136
theorem root148 : root JFp_SHADigest.digest tree148=value148 := by
  rw [tree148,root,root136]
  exact (congrArg JFp_SHADigest.digest address148).trans hash148
#print axioms root148
theorem shape148 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 61440=tree148 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 61440)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 11 61440 (by decide),siblings 11 (by decide) 61440 (by decide)]
  rw [shape136 f g inputs siblings]
  rfl
#print axioms shape148
def input149 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash149.message
def value149 : State := JFp_SHADigest.output JGf_TX2_M0.Hash149.result
theorem cast149_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash149.B00.input).map Fin.val=JGf_TX2_M0.Hash149.B00.input := by rfl
#print axioms cast149_0
theorem tail149 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash149.tail).map Fin.val=JGf_TX2_M0.Hash149.tail := by rfl
#print axioms tail149
theorem numeric149 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash149.message).map Fin.val=JGf_TX2_M0.Hash149.message := by
  simp only [JGf_TX2_M0.Hash149.message,JGf_TX2_M0.Hash149.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast149_0,tail149]
#print axioms numeric149
theorem hash149 : JFp_SHADigest.digest input149=value149 := by
  unfold input149 JFp_SHADigest.digest
  rw [numeric149,JGf_TX2_M0.Hash149.checked]
  rfl
#print axioms hash149
theorem address149 : BinMerkle32Path.nodeInput (children value137 (JGc_TX2_HashBytes.state [50,197,40,222,139,209,107,165,137,68,168,234,61,70,156,241,160,165,126,139,19,73,162,218,105,132,132,22,191,255,236,155]))=input149 := by rfl
#print axioms address149
def tree149 : Tree := .branch tree137 (.supplied (JGc_TX2_HashBytes.state [50,197,40,222,139,209,107,165,137,68,168,234,61,70,156,241,160,165,126,139,19,73,162,218,105,132,132,22,191,255,236,155]))
theorem root149 : root JFp_SHADigest.digest tree149=value149 := by
  rw [tree149,root,root137]
  exact (congrArg JFp_SHADigest.digest address149).trans hash149
#print axioms root149
theorem shape149 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 131072=tree149 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 131072)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape137 f g inputs siblings]
  rw [unoccupied f g 11 133120 (by decide),siblings 11 (by decide) 133120 (by decide)]
  rfl
#print axioms shape149
def input150 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash150.message
def value150 : State := JFp_SHADigest.output JGf_TX2_M0.Hash150.result
theorem cast150_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash150.B00.input).map Fin.val=JGf_TX2_M0.Hash150.B00.input := by rfl
#print axioms cast150_0
theorem tail150 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash150.tail).map Fin.val=JGf_TX2_M0.Hash150.tail := by rfl
#print axioms tail150
theorem numeric150 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash150.message).map Fin.val=JGf_TX2_M0.Hash150.message := by
  simp only [JGf_TX2_M0.Hash150.message,JGf_TX2_M0.Hash150.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast150_0,tail150]
#print axioms numeric150
theorem hash150 : JFp_SHADigest.digest input150=value150 := by
  unfold input150 JFp_SHADigest.digest
  rw [numeric150,JGf_TX2_M0.Hash150.checked]
  rfl
#print axioms hash150
theorem address150 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [200,149,232,121,62,170,158,191,139,66,112,106,15,240,19,35,93,149,69,157,116,120,66,42,111,20,228,21,7,29,203,75]) value138)=input150 := by rfl
#print axioms address150
def tree150 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [200,149,232,121,62,170,158,191,139,66,112,106,15,240,19,35,93,149,69,157,116,120,66,42,111,20,228,21,7,29,203,75])) tree138
theorem root150 : root JFp_SHADigest.digest tree150=value150 := by
  rw [tree150,root,root138]
  exact (congrArg JFp_SHADigest.digest address150).trans hash150
#print axioms root150
theorem shape150 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 147456=tree150 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 147456)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 11 147456 (by decide),siblings 11 (by decide) 147456 (by decide)]
  rw [shape138 f g inputs siblings]
  rfl
#print axioms shape150
def input151 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash151.message
def value151 : State := JFp_SHADigest.output JGf_TX2_M0.Hash151.result
theorem cast151_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash151.B00.input).map Fin.val=JGf_TX2_M0.Hash151.B00.input := by rfl
#print axioms cast151_0
theorem tail151 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash151.tail).map Fin.val=JGf_TX2_M0.Hash151.tail := by rfl
#print axioms tail151
theorem numeric151 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash151.message).map Fin.val=JGf_TX2_M0.Hash151.message := by
  simp only [JGf_TX2_M0.Hash151.message,JGf_TX2_M0.Hash151.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast151_0,tail151]
#print axioms numeric151
theorem hash151 : JFp_SHADigest.digest input151=value151 := by
  unfold input151 JFp_SHADigest.digest
  rw [numeric151,JGf_TX2_M0.Hash151.checked]
  rfl
#print axioms hash151
theorem address151 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [228,247,250,237,187,58,165,146,112,3,113,89,150,108,79,71,123,207,222,81,77,51,113,185,239,180,225,112,53,23,223,23]) value139)=input151 := by rfl
#print axioms address151
def tree151 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [228,247,250,237,187,58,165,146,112,3,113,89,150,108,79,71,123,207,222,81,77,51,113,185,239,180,225,112,53,23,223,23])) tree139
theorem root151 : root JFp_SHADigest.digest tree151=value151 := by
  rw [tree151,root,root139]
  exact (congrArg JFp_SHADigest.digest address151).trans hash151
#print axioms root151
theorem shape151 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 163840=tree151 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 163840)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 11 163840 (by decide),siblings 11 (by decide) 163840 (by decide)]
  rw [shape139 f g inputs siblings]
  rfl
#print axioms shape151
def input152 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash152.message
def value152 : State := JFp_SHADigest.output JGf_TX2_M0.Hash152.result
theorem cast152_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash152.B00.input).map Fin.val=JGf_TX2_M0.Hash152.B00.input := by rfl
#print axioms cast152_0
theorem tail152 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash152.tail).map Fin.val=JGf_TX2_M0.Hash152.tail := by rfl
#print axioms tail152
theorem numeric152 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash152.message).map Fin.val=JGf_TX2_M0.Hash152.message := by
  simp only [JGf_TX2_M0.Hash152.message,JGf_TX2_M0.Hash152.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast152_0,tail152]
#print axioms numeric152
theorem hash152 : JFp_SHADigest.digest input152=value152 := by
  unfold input152 JFp_SHADigest.digest
  rw [numeric152,JGf_TX2_M0.Hash152.checked]
  rfl
#print axioms hash152
theorem address152 : BinMerkle32Path.nodeInput (children value140 value141)=input152 := by rfl
#print axioms address152
def tree152 : Tree := .branch tree140 tree141
theorem root152 : root JFp_SHADigest.digest tree152=value152 := by
  rw [tree152,root,root140,root141]
  exact (congrArg JFp_SHADigest.digest address152).trans hash152
#print axioms root152
theorem shape152 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 176128=tree152 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 176128)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape140 f g inputs siblings]
  rw [shape141 f g inputs siblings]
  rfl
#print axioms shape152
def input153 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash153.message
def value153 : State := JFp_SHADigest.output JGf_TX2_M0.Hash153.result
theorem cast153_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash153.B00.input).map Fin.val=JGf_TX2_M0.Hash153.B00.input := by rfl
#print axioms cast153_0
theorem tail153 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash153.tail).map Fin.val=JGf_TX2_M0.Hash153.tail := by rfl
#print axioms tail153
theorem numeric153 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash153.message).map Fin.val=JGf_TX2_M0.Hash153.message := by
  simp only [JGf_TX2_M0.Hash153.message,JGf_TX2_M0.Hash153.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast153_0,tail153]
#print axioms numeric153
theorem hash153 : JFp_SHADigest.digest input153=value153 := by
  unfold input153 JFp_SHADigest.digest
  rw [numeric153,JGf_TX2_M0.Hash153.checked]
  rfl
#print axioms hash153
theorem address153 : BinMerkle32Path.nodeInput (children value142 (JGc_TX2_HashBytes.state [111,194,132,148,95,67,9,161,205,253,107,0,23,217,115,170,216,26,34,68,250,205,24,215,65,63,107,42,199,73,248,75]))=input153 := by rfl
#print axioms address153
def tree153 : Tree := .branch tree142 (.supplied (JGc_TX2_HashBytes.state [111,194,132,148,95,67,9,161,205,253,107,0,23,217,115,170,216,26,34,68,250,205,24,215,65,63,107,42,199,73,248,75]))
theorem root153 : root JFp_SHADigest.digest tree153=value153 := by
  rw [tree153,root,root142]
  exact (congrArg JFp_SHADigest.digest address153).trans hash153
#print axioms root153
theorem shape153 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 184320=tree153 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 184320)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape142 f g inputs siblings]
  rw [unoccupied f g 11 186368 (by decide),siblings 11 (by decide) 186368 (by decide)]
  rfl
#print axioms shape153
def input154 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash154.message
def value154 : State := JFp_SHADigest.output JGf_TX2_M0.Hash154.result
theorem cast154_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash154.B00.input).map Fin.val=JGf_TX2_M0.Hash154.B00.input := by rfl
#print axioms cast154_0
theorem tail154 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash154.tail).map Fin.val=JGf_TX2_M0.Hash154.tail := by rfl
#print axioms tail154
theorem numeric154 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash154.message).map Fin.val=JGf_TX2_M0.Hash154.message := by
  simp only [JGf_TX2_M0.Hash154.message,JGf_TX2_M0.Hash154.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast154_0,tail154]
#print axioms numeric154
theorem hash154 : JFp_SHADigest.digest input154=value154 := by
  unfold input154 JFp_SHADigest.digest
  rw [numeric154,JGf_TX2_M0.Hash154.checked]
  rfl
#print axioms hash154
theorem address154 : BinMerkle32Path.nodeInput (children value143 (JGc_TX2_HashBytes.state [245,160,40,221,224,244,207,132,246,70,222,149,160,74,117,252,124,239,209,144,161,31,18,157,250,20,133,24,79,33,188,124]))=input154 := by rfl
#print axioms address154
def tree154 : Tree := .branch tree143 (.supplied (JGc_TX2_HashBytes.state [245,160,40,221,224,244,207,132,246,70,222,149,160,74,117,252,124,239,209,144,161,31,18,157,250,20,133,24,79,33,188,124]))
theorem root154 : root JFp_SHADigest.digest tree154=value154 := by
  rw [tree154,root,root143]
  exact (congrArg JFp_SHADigest.digest address154).trans hash154
#print axioms root154
theorem shape154 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 217088=tree154 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 217088)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape143 f g inputs siblings]
  rw [unoccupied f g 11 219136 (by decide),siblings 11 (by decide) 219136 (by decide)]
  rfl
#print axioms shape154
end AspisR1.JGf_TX2_M0Roots
end
