import NDO_JGc_TX2_M2Level10
import NDO_JGc_TX2_M2H140
import NDO_JGc_TX2_M2H144
import NDO_JGc_TX2_M2H148
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input142 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash142.message
def value142 : State := JFp_SHADigest.output JGc_TX2_M2.Hash142.result
theorem cast142_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash142.B00.input).map Fin.val=JGc_TX2_M2.Hash142.B00.input := by rfl
#print axioms cast142_0
theorem tail142 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash142.tail).map Fin.val=JGc_TX2_M2.Hash142.tail := by rfl
#print axioms tail142
theorem numeric142 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash142.message).map Fin.val=JGc_TX2_M2.Hash142.message := by
  simp only [JGc_TX2_M2.Hash142.message,JGc_TX2_M2.Hash142.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast142_0,tail142]
#print axioms numeric142
theorem hash142 : JFp_SHADigest.digest input142=value142 := by
  unfold input142 JFp_SHADigest.digest
  rw [numeric142,JGc_TX2_M2.Hash142.checked]
  rfl
#print axioms hash142
theorem address142 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [211,133,42,121,71,214,171,121,23,238,229,220,232,81,226,140,158,215,181,120,225,232,91,161,20,254,78,111,27,194,178,137]) value131)=input142 := by rfl
#print axioms address142
def tree142 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [211,133,42,121,71,214,171,121,23,238,229,220,232,81,226,140,158,215,181,120,225,232,91,161,20,254,78,111,27,194,178,137])) tree131
theorem root142 : root JFp_SHADigest.digest tree142=value142 := by
  rw [tree142,root,root131]
  exact (congrArg JFp_SHADigest.digest address142).trans hash142
#print axioms root142
theorem shape142 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 0=tree142 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 0)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 11 0 (by decide),siblings 11 (by decide) 0 (by decide)]
  rw [shape131 f g inputs siblings]
  rfl
#print axioms shape142
def input143 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash143.message
def value143 : State := JFp_SHADigest.output JGc_TX2_M2.Hash143.result
theorem cast143_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash143.B00.input).map Fin.val=JGc_TX2_M2.Hash143.B00.input := by rfl
#print axioms cast143_0
theorem tail143 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash143.tail).map Fin.val=JGc_TX2_M2.Hash143.tail := by rfl
#print axioms tail143
theorem numeric143 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash143.message).map Fin.val=JGc_TX2_M2.Hash143.message := by
  simp only [JGc_TX2_M2.Hash143.message,JGc_TX2_M2.Hash143.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast143_0,tail143]
#print axioms numeric143
theorem hash143 : JFp_SHADigest.digest input143=value143 := by
  unfold input143 JFp_SHADigest.digest
  rw [numeric143,JGc_TX2_M2.Hash143.checked]
  rfl
#print axioms hash143
theorem address143 : BinMerkle32Path.nodeInput (children value132 (JGc_TX2_HashBytes.state [198,235,95,219,48,201,154,180,112,133,68,118,178,84,199,43,130,207,170,217,113,219,108,126,84,47,69,227,98,226,1,62]))=input143 := by rfl
#print axioms address143
def tree143 : Tree := .branch tree132 (.supplied (JGc_TX2_HashBytes.state [198,235,95,219,48,201,154,180,112,133,68,118,178,84,199,43,130,207,170,217,113,219,108,126,84,47,69,227,98,226,1,62]))
theorem root143 : root JFp_SHADigest.digest tree143=value143 := by
  rw [tree143,root,root132]
  exact (congrArg JFp_SHADigest.digest address143).trans hash143
#print axioms root143
theorem shape143 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 4096=tree143 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 4096)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape132 f g inputs siblings]
  rw [unoccupied f g 11 6144 (by decide),siblings 11 (by decide) 6144 (by decide)]
  rfl
#print axioms shape143
def input144 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash144.message
def value144 : State := JFp_SHADigest.output JGc_TX2_M2.Hash144.result
theorem cast144_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash144.B00.input).map Fin.val=JGc_TX2_M2.Hash144.B00.input := by rfl
#print axioms cast144_0
theorem tail144 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash144.tail).map Fin.val=JGc_TX2_M2.Hash144.tail := by rfl
#print axioms tail144
theorem numeric144 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash144.message).map Fin.val=JGc_TX2_M2.Hash144.message := by
  simp only [JGc_TX2_M2.Hash144.message,JGc_TX2_M2.Hash144.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast144_0,tail144]
#print axioms numeric144
theorem hash144 : JFp_SHADigest.digest input144=value144 := by
  unfold input144 JFp_SHADigest.digest
  rw [numeric144,JGc_TX2_M2.Hash144.checked]
  rfl
#print axioms hash144
theorem address144 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [196,172,155,7,60,230,128,63,182,108,156,51,168,201,201,45,142,35,248,168,200,108,177,201,75,68,200,95,159,135,109,197]) value133)=input144 := by rfl
#print axioms address144
def tree144 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [196,172,155,7,60,230,128,63,182,108,156,51,168,201,201,45,142,35,248,168,200,108,177,201,75,68,200,95,159,135,109,197])) tree133
theorem root144 : root JFp_SHADigest.digest tree144=value144 := by
  rw [tree144,root,root133]
  exact (congrArg JFp_SHADigest.digest address144).trans hash144
#print axioms root144
theorem shape144 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 8192=tree144 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 8192)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 11 8192 (by decide),siblings 11 (by decide) 8192 (by decide)]
  rw [shape133 f g inputs siblings]
  rfl
#print axioms shape144
def input145 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash145.message
def value145 : State := JFp_SHADigest.output JGc_TX2_M2.Hash145.result
theorem cast145_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash145.B00.input).map Fin.val=JGc_TX2_M2.Hash145.B00.input := by rfl
#print axioms cast145_0
theorem tail145 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash145.tail).map Fin.val=JGc_TX2_M2.Hash145.tail := by rfl
#print axioms tail145
theorem numeric145 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash145.message).map Fin.val=JGc_TX2_M2.Hash145.message := by
  simp only [JGc_TX2_M2.Hash145.message,JGc_TX2_M2.Hash145.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast145_0,tail145]
#print axioms numeric145
theorem hash145 : JFp_SHADigest.digest input145=value145 := by
  unfold input145 JFp_SHADigest.digest
  rw [numeric145,JGc_TX2_M2.Hash145.checked]
  rfl
#print axioms hash145
theorem address145 : BinMerkle32Path.nodeInput (children value134 value135)=input145 := by rfl
#print axioms address145
def tree145 : Tree := .branch tree134 tree135
theorem root145 : root JFp_SHADigest.digest tree145=value145 := by
  rw [tree145,root,root134,root135]
  exact (congrArg JFp_SHADigest.digest address145).trans hash145
#print axioms root145
theorem shape145 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 12288=tree145 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 12288)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape134 f g inputs siblings]
  rw [shape135 f g inputs siblings]
  rfl
#print axioms shape145
def input146 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash146.message
def value146 : State := JFp_SHADigest.output JGc_TX2_M2.Hash146.result
theorem cast146_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash146.B00.input).map Fin.val=JGc_TX2_M2.Hash146.B00.input := by rfl
#print axioms cast146_0
theorem tail146 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash146.tail).map Fin.val=JGc_TX2_M2.Hash146.tail := by rfl
#print axioms tail146
theorem numeric146 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash146.message).map Fin.val=JGc_TX2_M2.Hash146.message := by
  simp only [JGc_TX2_M2.Hash146.message,JGc_TX2_M2.Hash146.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast146_0,tail146]
#print axioms numeric146
theorem hash146 : JFp_SHADigest.digest input146=value146 := by
  unfold input146 JFp_SHADigest.digest
  rw [numeric146,JGc_TX2_M2.Hash146.checked]
  rfl
#print axioms hash146
theorem address146 : BinMerkle32Path.nodeInput (children value136 (JGc_TX2_HashBytes.state [121,23,125,210,125,87,98,114,18,205,236,39,242,57,3,114,212,23,7,123,228,197,5,167,29,229,50,51,51,48,231,9]))=input146 := by rfl
#print axioms address146
def tree146 : Tree := .branch tree136 (.supplied (JGc_TX2_HashBytes.state [121,23,125,210,125,87,98,114,18,205,236,39,242,57,3,114,212,23,7,123,228,197,5,167,29,229,50,51,51,48,231,9]))
theorem root146 : root JFp_SHADigest.digest tree146=value146 := by
  rw [tree146,root,root136]
  exact (congrArg JFp_SHADigest.digest address146).trans hash146
#print axioms root146
theorem shape146 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 32768=tree146 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 32768)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape136 f g inputs siblings]
  rw [unoccupied f g 11 34816 (by decide),siblings 11 (by decide) 34816 (by decide)]
  rfl
#print axioms shape146
def input147 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash147.message
def value147 : State := JFp_SHADigest.output JGc_TX2_M2.Hash147.result
theorem cast147_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash147.B00.input).map Fin.val=JGc_TX2_M2.Hash147.B00.input := by rfl
#print axioms cast147_0
theorem tail147 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash147.tail).map Fin.val=JGc_TX2_M2.Hash147.tail := by rfl
#print axioms tail147
theorem numeric147 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash147.message).map Fin.val=JGc_TX2_M2.Hash147.message := by
  simp only [JGc_TX2_M2.Hash147.message,JGc_TX2_M2.Hash147.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast147_0,tail147]
#print axioms numeric147
theorem hash147 : JFp_SHADigest.digest input147=value147 := by
  unfold input147 JFp_SHADigest.digest
  rw [numeric147,JGc_TX2_M2.Hash147.checked]
  rfl
#print axioms hash147
theorem address147 : BinMerkle32Path.nodeInput (children value137 (JGc_TX2_HashBytes.state [54,122,241,152,119,157,184,27,237,233,221,209,107,25,128,244,112,159,225,233,22,229,80,140,61,14,151,165,210,193,157,191]))=input147 := by rfl
#print axioms address147
def tree147 : Tree := .branch tree137 (.supplied (JGc_TX2_HashBytes.state [54,122,241,152,119,157,184,27,237,233,221,209,107,25,128,244,112,159,225,233,22,229,80,140,61,14,151,165,210,193,157,191]))
theorem root147 : root JFp_SHADigest.digest tree147=value147 := by
  rw [tree147,root,root137]
  exact (congrArg JFp_SHADigest.digest address147).trans hash147
#print axioms root147
theorem shape147 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 36864=tree147 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 36864)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape137 f g inputs siblings]
  rw [unoccupied f g 11 38912 (by decide),siblings 11 (by decide) 38912 (by decide)]
  rfl
#print axioms shape147
def input148 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash148.message
def value148 : State := JFp_SHADigest.output JGc_TX2_M2.Hash148.result
theorem cast148_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash148.B00.input).map Fin.val=JGc_TX2_M2.Hash148.B00.input := by rfl
#print axioms cast148_0
theorem tail148 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash148.tail).map Fin.val=JGc_TX2_M2.Hash148.tail := by rfl
#print axioms tail148
theorem numeric148 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash148.message).map Fin.val=JGc_TX2_M2.Hash148.message := by
  simp only [JGc_TX2_M2.Hash148.message,JGc_TX2_M2.Hash148.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast148_0,tail148]
#print axioms numeric148
theorem hash148 : JFp_SHADigest.digest input148=value148 := by
  unfold input148 JFp_SHADigest.digest
  rw [numeric148,JGc_TX2_M2.Hash148.checked]
  rfl
#print axioms hash148
theorem address148 : BinMerkle32Path.nodeInput (children value138 value139)=input148 := by rfl
#print axioms address148
def tree148 : Tree := .branch tree138 tree139
theorem root148 : root JFp_SHADigest.digest tree148=value148 := by
  rw [tree148,root,root138,root139]
  exact (congrArg JFp_SHADigest.digest address148).trans hash148
#print axioms root148
theorem shape148 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 40960=tree148 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 40960)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape138 f g inputs siblings]
  rw [shape139 f g inputs siblings]
  rfl
#print axioms shape148
def input149 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash149.message
def value149 : State := JFp_SHADigest.output JGc_TX2_M2.Hash149.result
theorem cast149_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash149.B00.input).map Fin.val=JGc_TX2_M2.Hash149.B00.input := by rfl
#print axioms cast149_0
theorem tail149 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash149.tail).map Fin.val=JGc_TX2_M2.Hash149.tail := by rfl
#print axioms tail149
theorem numeric149 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash149.message).map Fin.val=JGc_TX2_M2.Hash149.message := by
  simp only [JGc_TX2_M2.Hash149.message,JGc_TX2_M2.Hash149.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast149_0,tail149]
#print axioms numeric149
theorem hash149 : JFp_SHADigest.digest input149=value149 := by
  unfold input149 JFp_SHADigest.digest
  rw [numeric149,JGc_TX2_M2.Hash149.checked]
  rfl
#print axioms hash149
theorem address149 : BinMerkle32Path.nodeInput (children value140 (JGc_TX2_HashBytes.state [69,148,235,60,248,248,134,207,3,234,148,36,124,162,56,207,114,207,252,29,191,119,140,231,210,102,64,103,101,252,47,177]))=input149 := by rfl
#print axioms address149
def tree149 : Tree := .branch tree140 (.supplied (JGc_TX2_HashBytes.state [69,148,235,60,248,248,134,207,3,234,148,36,124,162,56,207,114,207,252,29,191,119,140,231,210,102,64,103,101,252,47,177]))
theorem root149 : root JFp_SHADigest.digest tree149=value149 := by
  rw [tree149,root,root140]
  exact (congrArg JFp_SHADigest.digest address149).trans hash149
#print axioms root149
theorem shape149 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 45056=tree149 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 45056)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape140 f g inputs siblings]
  rw [unoccupied f g 11 47104 (by decide),siblings 11 (by decide) 47104 (by decide)]
  rfl
#print axioms shape149
def input150 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash150.message
def value150 : State := JFp_SHADigest.output JGc_TX2_M2.Hash150.result
theorem cast150_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash150.B00.input).map Fin.val=JGc_TX2_M2.Hash150.B00.input := by rfl
#print axioms cast150_0
theorem tail150 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash150.tail).map Fin.val=JGc_TX2_M2.Hash150.tail := by rfl
#print axioms tail150
theorem numeric150 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash150.message).map Fin.val=JGc_TX2_M2.Hash150.message := by
  simp only [JGc_TX2_M2.Hash150.message,JGc_TX2_M2.Hash150.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast150_0,tail150]
#print axioms numeric150
theorem hash150 : JFp_SHADigest.digest input150=value150 := by
  unfold input150 JFp_SHADigest.digest
  rw [numeric150,JGc_TX2_M2.Hash150.checked]
  rfl
#print axioms hash150
theorem address150 : BinMerkle32Path.nodeInput (children value141 (JGc_TX2_HashBytes.state [6,129,243,133,201,8,108,81,39,87,79,34,75,133,83,63,178,115,227,174,129,80,5,186,58,198,235,77,231,201,140,216]))=input150 := by rfl
#print axioms address150
def tree150 : Tree := .branch tree141 (.supplied (JGc_TX2_HashBytes.state [6,129,243,133,201,8,108,81,39,87,79,34,75,133,83,63,178,115,227,174,129,80,5,186,58,198,235,77,231,201,140,216]))
theorem root150 : root JFp_SHADigest.digest tree150=value150 := by
  rw [tree150,root,root141]
  exact (congrArg JFp_SHADigest.digest address150).trans hash150
#print axioms root150
theorem shape150 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 12 53248=tree150 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 12 53248)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape141 f g inputs siblings]
  rw [unoccupied f g 11 55296 (by decide),siblings 11 (by decide) 55296 (by decide)]
  rfl
#print axioms shape150
end AspisR1.JGc_TX2_M2Roots
end
