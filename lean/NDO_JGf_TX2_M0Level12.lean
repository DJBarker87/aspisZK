import NDO_JGf_TX2_M0Level11
import NDO_JGf_TX2_M0W049
import NDO_JGf_TX2_M0W050
import NDO_JGf_TX2_M0W051
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGf_TX2_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input155 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash155.message
def value155 : State := JFp_SHADigest.output JGf_TX2_M0.Hash155.result
theorem cast155_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash155.B00.input).map Fin.val=JGf_TX2_M0.Hash155.B00.input := by rfl
#print axioms cast155_0
theorem tail155 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash155.tail).map Fin.val=JGf_TX2_M0.Hash155.tail := by rfl
#print axioms tail155
theorem numeric155 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash155.message).map Fin.val=JGf_TX2_M0.Hash155.message := by
  simp only [JGf_TX2_M0.Hash155.message,JGf_TX2_M0.Hash155.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast155_0,tail155]
#print axioms numeric155
theorem hash155 : JFp_SHADigest.digest input155=value155 := by
  unfold input155 JFp_SHADigest.digest
  rw [numeric155,JGf_TX2_M0.Hash155.checked]
  rfl
#print axioms hash155
theorem address155 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [54,37,81,80,14,248,39,98,134,93,133,113,58,219,160,108,225,164,80,187,51,143,134,251,235,73,132,228,23,159,252,45]) value144)=input155 := by rfl
#print axioms address155
def tree155 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [54,37,81,80,14,248,39,98,134,93,133,113,58,219,160,108,225,164,80,187,51,143,134,251,235,73,132,228,23,159,252,45])) tree144
theorem root155 : root JFp_SHADigest.digest tree155=value155 := by
  rw [tree155,root,root144]
  exact (congrArg JFp_SHADigest.digest address155).trans hash155
#print axioms root155
theorem shape155 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 8192=tree155 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 8192)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 12 8192 (by decide),siblings 12 (by decide) 8192 (by decide)]
  rw [shape144 f g inputs siblings]
  rfl
#print axioms shape155
def input156 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash156.message
def value156 : State := JFp_SHADigest.output JGf_TX2_M0.Hash156.result
theorem cast156_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash156.B00.input).map Fin.val=JGf_TX2_M0.Hash156.B00.input := by rfl
#print axioms cast156_0
theorem tail156 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash156.tail).map Fin.val=JGf_TX2_M0.Hash156.tail := by rfl
#print axioms tail156
theorem numeric156 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash156.message).map Fin.val=JGf_TX2_M0.Hash156.message := by
  simp only [JGf_TX2_M0.Hash156.message,JGf_TX2_M0.Hash156.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast156_0,tail156]
#print axioms numeric156
theorem hash156 : JFp_SHADigest.digest input156=value156 := by
  unfold input156 JFp_SHADigest.digest
  rw [numeric156,JGf_TX2_M0.Hash156.checked]
  rfl
#print axioms hash156
theorem address156 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [109,31,24,121,203,117,68,41,248,74,89,113,201,44,234,105,30,21,213,81,195,14,18,232,230,164,128,211,204,94,71,50]) value145)=input156 := by rfl
#print axioms address156
def tree156 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [109,31,24,121,203,117,68,41,248,74,89,113,201,44,234,105,30,21,213,81,195,14,18,232,230,164,128,211,204,94,71,50])) tree145
theorem root156 : root JFp_SHADigest.digest tree156=value156 := by
  rw [tree156,root,root145]
  exact (congrArg JFp_SHADigest.digest address156).trans hash156
#print axioms root156
theorem shape156 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 16384=tree156 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 16384)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 12 16384 (by decide),siblings 12 (by decide) 16384 (by decide)]
  rw [shape145 f g inputs siblings]
  rfl
#print axioms shape156
def input157 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash157.message
def value157 : State := JFp_SHADigest.output JGf_TX2_M0.Hash157.result
theorem cast157_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash157.B00.input).map Fin.val=JGf_TX2_M0.Hash157.B00.input := by rfl
#print axioms cast157_0
theorem tail157 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash157.tail).map Fin.val=JGf_TX2_M0.Hash157.tail := by rfl
#print axioms tail157
theorem numeric157 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash157.message).map Fin.val=JGf_TX2_M0.Hash157.message := by
  simp only [JGf_TX2_M0.Hash157.message,JGf_TX2_M0.Hash157.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast157_0,tail157]
#print axioms numeric157
theorem hash157 : JFp_SHADigest.digest input157=value157 := by
  unfold input157 JFp_SHADigest.digest
  rw [numeric157,JGf_TX2_M0.Hash157.checked]
  rfl
#print axioms hash157
theorem address157 : BinMerkle32Path.nodeInput (children value146 (JGc_TX2_HashBytes.state [68,134,178,206,192,86,204,108,100,187,21,109,185,102,7,44,171,214,163,8,147,246,252,242,249,173,4,3,55,255,210,154]))=input157 := by rfl
#print axioms address157
def tree157 : Tree := .branch tree146 (.supplied (JGc_TX2_HashBytes.state [68,134,178,206,192,86,204,108,100,187,21,109,185,102,7,44,171,214,163,8,147,246,252,242,249,173,4,3,55,255,210,154]))
theorem root157 : root JFp_SHADigest.digest tree157=value157 := by
  rw [tree157,root,root146]
  exact (congrArg JFp_SHADigest.digest address157).trans hash157
#print axioms root157
theorem shape157 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 40960=tree157 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 40960)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape146 f g inputs siblings]
  rw [unoccupied f g 12 45056 (by decide),siblings 12 (by decide) 45056 (by decide)]
  rfl
#print axioms shape157
def input158 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash158.message
def value158 : State := JFp_SHADigest.output JGf_TX2_M0.Hash158.result
theorem cast158_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash158.B00.input).map Fin.val=JGf_TX2_M0.Hash158.B00.input := by rfl
#print axioms cast158_0
theorem tail158 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash158.tail).map Fin.val=JGf_TX2_M0.Hash158.tail := by rfl
#print axioms tail158
theorem numeric158 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash158.message).map Fin.val=JGf_TX2_M0.Hash158.message := by
  simp only [JGf_TX2_M0.Hash158.message,JGf_TX2_M0.Hash158.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast158_0,tail158]
#print axioms numeric158
theorem hash158 : JFp_SHADigest.digest input158=value158 := by
  unfold input158 JFp_SHADigest.digest
  rw [numeric158,JGf_TX2_M0.Hash158.checked]
  rfl
#print axioms hash158
theorem address158 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [78,103,24,50,79,181,66,116,124,191,53,207,205,8,148,29,135,30,12,148,35,219,253,99,246,34,204,225,141,35,118,128]) value147)=input158 := by rfl
#print axioms address158
def tree158 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [78,103,24,50,79,181,66,116,124,191,53,207,205,8,148,29,135,30,12,148,35,219,253,99,246,34,204,225,141,35,118,128])) tree147
theorem root158 : root JFp_SHADigest.digest tree158=value158 := by
  rw [tree158,root,root147]
  exact (congrArg JFp_SHADigest.digest address158).trans hash158
#print axioms root158
theorem shape158 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 49152=tree158 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 49152)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 12 49152 (by decide),siblings 12 (by decide) 49152 (by decide)]
  rw [shape147 f g inputs siblings]
  rfl
#print axioms shape158
def input159 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash159.message
def value159 : State := JFp_SHADigest.output JGf_TX2_M0.Hash159.result
theorem cast159_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash159.B00.input).map Fin.val=JGf_TX2_M0.Hash159.B00.input := by rfl
#print axioms cast159_0
theorem tail159 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash159.tail).map Fin.val=JGf_TX2_M0.Hash159.tail := by rfl
#print axioms tail159
theorem numeric159 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash159.message).map Fin.val=JGf_TX2_M0.Hash159.message := by
  simp only [JGf_TX2_M0.Hash159.message,JGf_TX2_M0.Hash159.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast159_0,tail159]
#print axioms numeric159
theorem hash159 : JFp_SHADigest.digest input159=value159 := by
  unfold input159 JFp_SHADigest.digest
  rw [numeric159,JGf_TX2_M0.Hash159.checked]
  rfl
#print axioms hash159
theorem address159 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [1,216,7,245,98,207,203,167,39,146,2,37,67,147,201,148,126,0,80,104,23,47,165,185,232,214,110,222,23,176,142,226]) value148)=input159 := by rfl
#print axioms address159
def tree159 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [1,216,7,245,98,207,203,167,39,146,2,37,67,147,201,148,126,0,80,104,23,47,165,185,232,214,110,222,23,176,142,226])) tree148
theorem root159 : root JFp_SHADigest.digest tree159=value159 := by
  rw [tree159,root,root148]
  exact (congrArg JFp_SHADigest.digest address159).trans hash159
#print axioms root159
theorem shape159 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 57344=tree159 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 57344)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 12 57344 (by decide),siblings 12 (by decide) 57344 (by decide)]
  rw [shape148 f g inputs siblings]
  rfl
#print axioms shape159
def input160 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash160.message
def value160 : State := JFp_SHADigest.output JGf_TX2_M0.Hash160.result
theorem cast160_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash160.B00.input).map Fin.val=JGf_TX2_M0.Hash160.B00.input := by rfl
#print axioms cast160_0
theorem tail160 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash160.tail).map Fin.val=JGf_TX2_M0.Hash160.tail := by rfl
#print axioms tail160
theorem numeric160 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash160.message).map Fin.val=JGf_TX2_M0.Hash160.message := by
  simp only [JGf_TX2_M0.Hash160.message,JGf_TX2_M0.Hash160.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast160_0,tail160]
#print axioms numeric160
theorem hash160 : JFp_SHADigest.digest input160=value160 := by
  unfold input160 JFp_SHADigest.digest
  rw [numeric160,JGf_TX2_M0.Hash160.checked]
  rfl
#print axioms hash160
theorem address160 : BinMerkle32Path.nodeInput (children value149 (JGc_TX2_HashBytes.state [144,13,77,6,23,250,174,77,80,91,196,128,153,34,178,214,62,67,161,153,121,211,3,14,65,129,101,93,149,250,164,113]))=input160 := by rfl
#print axioms address160
def tree160 : Tree := .branch tree149 (.supplied (JGc_TX2_HashBytes.state [144,13,77,6,23,250,174,77,80,91,196,128,153,34,178,214,62,67,161,153,121,211,3,14,65,129,101,93,149,250,164,113]))
theorem root160 : root JFp_SHADigest.digest tree160=value160 := by
  rw [tree160,root,root149]
  exact (congrArg JFp_SHADigest.digest address160).trans hash160
#print axioms root160
theorem shape160 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 131072=tree160 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 131072)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape149 f g inputs siblings]
  rw [unoccupied f g 12 135168 (by decide),siblings 12 (by decide) 135168 (by decide)]
  rfl
#print axioms shape160
def input161 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash161.message
def value161 : State := JFp_SHADigest.output JGf_TX2_M0.Hash161.result
theorem cast161_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash161.B00.input).map Fin.val=JGf_TX2_M0.Hash161.B00.input := by rfl
#print axioms cast161_0
theorem tail161 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash161.tail).map Fin.val=JGf_TX2_M0.Hash161.tail := by rfl
#print axioms tail161
theorem numeric161 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash161.message).map Fin.val=JGf_TX2_M0.Hash161.message := by
  simp only [JGf_TX2_M0.Hash161.message,JGf_TX2_M0.Hash161.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast161_0,tail161]
#print axioms numeric161
theorem hash161 : JFp_SHADigest.digest input161=value161 := by
  unfold input161 JFp_SHADigest.digest
  rw [numeric161,JGf_TX2_M0.Hash161.checked]
  rfl
#print axioms hash161
theorem address161 : BinMerkle32Path.nodeInput (children value150 (JGc_TX2_HashBytes.state [211,48,75,83,168,253,130,42,18,106,192,164,216,10,63,11,154,197,231,229,193,137,184,83,8,108,208,85,178,162,241,238]))=input161 := by rfl
#print axioms address161
def tree161 : Tree := .branch tree150 (.supplied (JGc_TX2_HashBytes.state [211,48,75,83,168,253,130,42,18,106,192,164,216,10,63,11,154,197,231,229,193,137,184,83,8,108,208,85,178,162,241,238]))
theorem root161 : root JFp_SHADigest.digest tree161=value161 := by
  rw [tree161,root,root150]
  exact (congrArg JFp_SHADigest.digest address161).trans hash161
#print axioms root161
theorem shape161 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 147456=tree161 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 147456)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape150 f g inputs siblings]
  rw [unoccupied f g 12 151552 (by decide),siblings 12 (by decide) 151552 (by decide)]
  rfl
#print axioms shape161
def input162 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash162.message
def value162 : State := JFp_SHADigest.output JGf_TX2_M0.Hash162.result
theorem cast162_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash162.B00.input).map Fin.val=JGf_TX2_M0.Hash162.B00.input := by rfl
#print axioms cast162_0
theorem tail162 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash162.tail).map Fin.val=JGf_TX2_M0.Hash162.tail := by rfl
#print axioms tail162
theorem numeric162 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash162.message).map Fin.val=JGf_TX2_M0.Hash162.message := by
  simp only [JGf_TX2_M0.Hash162.message,JGf_TX2_M0.Hash162.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast162_0,tail162]
#print axioms numeric162
theorem hash162 : JFp_SHADigest.digest input162=value162 := by
  unfold input162 JFp_SHADigest.digest
  rw [numeric162,JGf_TX2_M0.Hash162.checked]
  rfl
#print axioms hash162
theorem address162 : BinMerkle32Path.nodeInput (children value151 (JGc_TX2_HashBytes.state [155,26,86,145,61,238,175,58,249,43,40,68,3,91,218,177,119,143,43,127,15,124,26,25,175,51,185,132,100,88,195,245]))=input162 := by rfl
#print axioms address162
def tree162 : Tree := .branch tree151 (.supplied (JGc_TX2_HashBytes.state [155,26,86,145,61,238,175,58,249,43,40,68,3,91,218,177,119,143,43,127,15,124,26,25,175,51,185,132,100,88,195,245]))
theorem root162 : root JFp_SHADigest.digest tree162=value162 := by
  rw [tree162,root,root151]
  exact (congrArg JFp_SHADigest.digest address162).trans hash162
#print axioms root162
theorem shape162 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 163840=tree162 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 163840)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape151 f g inputs siblings]
  rw [unoccupied f g 12 167936 (by decide),siblings 12 (by decide) 167936 (by decide)]
  rfl
#print axioms shape162
def input163 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash163.message
def value163 : State := JFp_SHADigest.output JGf_TX2_M0.Hash163.result
theorem cast163_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash163.B00.input).map Fin.val=JGf_TX2_M0.Hash163.B00.input := by rfl
#print axioms cast163_0
theorem tail163 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash163.tail).map Fin.val=JGf_TX2_M0.Hash163.tail := by rfl
#print axioms tail163
theorem numeric163 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash163.message).map Fin.val=JGf_TX2_M0.Hash163.message := by
  simp only [JGf_TX2_M0.Hash163.message,JGf_TX2_M0.Hash163.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast163_0,tail163]
#print axioms numeric163
theorem hash163 : JFp_SHADigest.digest input163=value163 := by
  unfold input163 JFp_SHADigest.digest
  rw [numeric163,JGf_TX2_M0.Hash163.checked]
  rfl
#print axioms hash163
theorem address163 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [223,166,97,80,46,62,73,205,87,193,172,16,22,119,225,211,130,51,58,140,50,145,15,55,53,24,235,163,95,57,200,35]) value152)=input163 := by rfl
#print axioms address163
def tree163 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [223,166,97,80,46,62,73,205,87,193,172,16,22,119,225,211,130,51,58,140,50,145,15,55,53,24,235,163,95,57,200,35])) tree152
theorem root163 : root JFp_SHADigest.digest tree163=value163 := by
  rw [tree163,root,root152]
  exact (congrArg JFp_SHADigest.digest address163).trans hash163
#print axioms root163
theorem shape163 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 172032=tree163 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 172032)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 12 172032 (by decide),siblings 12 (by decide) 172032 (by decide)]
  rw [shape152 f g inputs siblings]
  rfl
#print axioms shape163
def input164 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash164.message
def value164 : State := JFp_SHADigest.output JGf_TX2_M0.Hash164.result
theorem cast164_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash164.B00.input).map Fin.val=JGf_TX2_M0.Hash164.B00.input := by rfl
#print axioms cast164_0
theorem tail164 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash164.tail).map Fin.val=JGf_TX2_M0.Hash164.tail := by rfl
#print axioms tail164
theorem numeric164 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash164.message).map Fin.val=JGf_TX2_M0.Hash164.message := by
  simp only [JGf_TX2_M0.Hash164.message,JGf_TX2_M0.Hash164.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast164_0,tail164]
#print axioms numeric164
theorem hash164 : JFp_SHADigest.digest input164=value164 := by
  unfold input164 JFp_SHADigest.digest
  rw [numeric164,JGf_TX2_M0.Hash164.checked]
  rfl
#print axioms hash164
theorem address164 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [46,112,186,227,143,116,95,251,244,227,253,73,237,28,50,19,45,36,191,178,91,62,214,150,172,212,233,209,219,85,54,48]) value153)=input164 := by rfl
#print axioms address164
def tree164 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [46,112,186,227,143,116,95,251,244,227,253,73,237,28,50,19,45,36,191,178,91,62,214,150,172,212,233,209,219,85,54,48])) tree153
theorem root164 : root JFp_SHADigest.digest tree164=value164 := by
  rw [tree164,root,root153]
  exact (congrArg JFp_SHADigest.digest address164).trans hash164
#print axioms root164
theorem shape164 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 180224=tree164 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 180224)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 12 180224 (by decide),siblings 12 (by decide) 180224 (by decide)]
  rw [shape153 f g inputs siblings]
  rfl
#print axioms shape164
def input165 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash165.message
def value165 : State := JFp_SHADigest.output JGf_TX2_M0.Hash165.result
theorem cast165_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash165.B00.input).map Fin.val=JGf_TX2_M0.Hash165.B00.input := by rfl
#print axioms cast165_0
theorem tail165 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash165.tail).map Fin.val=JGf_TX2_M0.Hash165.tail := by rfl
#print axioms tail165
theorem numeric165 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash165.message).map Fin.val=JGf_TX2_M0.Hash165.message := by
  simp only [JGf_TX2_M0.Hash165.message,JGf_TX2_M0.Hash165.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast165_0,tail165]
#print axioms numeric165
theorem hash165 : JFp_SHADigest.digest input165=value165 := by
  unfold input165 JFp_SHADigest.digest
  rw [numeric165,JGf_TX2_M0.Hash165.checked]
  rfl
#print axioms hash165
theorem address165 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [175,181,236,203,48,173,73,209,55,123,255,73,239,241,75,158,193,143,72,107,220,11,205,159,95,140,159,245,12,16,163,198]) value154)=input165 := by rfl
#print axioms address165
def tree165 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [175,181,236,203,48,173,73,209,55,123,255,73,239,241,75,158,193,143,72,107,220,11,205,159,95,140,159,245,12,16,163,198])) tree154
theorem root165 : root JFp_SHADigest.digest tree165=value165 := by
  rw [tree165,root,root154]
  exact (congrArg JFp_SHADigest.digest address165).trans hash165
#print axioms root165
theorem shape165 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 13 212992=tree165 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 13 212992)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 12 212992 (by decide),siblings 12 (by decide) 212992 (by decide)]
  rw [shape154 f g inputs siblings]
  rfl
#print axioms shape165
end AspisR1.JGf_TX2_M0Roots
end
