import NDO_JGh_TX2_M1Level11
import NDO_JGh_TX2_M1W040
import NDO_JGh_TX2_M1W041
import NDO_JGh_TX2_M1W042
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input155 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash155.message
def value155 : State := JFp_SHADigest.output JGh_TX2_M1.Hash155.result
theorem cast155_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash155.B00.input).map Fin.val=JGh_TX2_M1.Hash155.B00.input := by rfl
#print axioms cast155_0
theorem tail155 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash155.tail).map Fin.val=JGh_TX2_M1.Hash155.tail := by rfl
#print axioms tail155
theorem numeric155 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash155.message).map Fin.val=JGh_TX2_M1.Hash155.message := by
  simp only [JGh_TX2_M1.Hash155.message,JGh_TX2_M1.Hash155.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast155_0,tail155]
#print axioms numeric155
theorem hash155 : JFp_SHADigest.digest input155=value155 := by
  unfold input155 JFp_SHADigest.digest
  rw [numeric155,JGh_TX2_M1.Hash155.checked]
  rfl
#print axioms hash155
theorem address155 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [88,200,200,81,100,47,155,128,194,217,234,133,129,18,210,1,199,237,115,41,149,114,203,147,5,111,43,248,223,43,115,216]) value144)=input155 := by rfl
#print axioms address155
def tree155 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [88,200,200,81,100,47,155,128,194,217,234,133,129,18,210,1,199,237,115,41,149,114,203,147,5,111,43,248,223,43,115,216])) tree144
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
def input156 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash156.message
def value156 : State := JFp_SHADigest.output JGh_TX2_M1.Hash156.result
theorem cast156_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash156.B00.input).map Fin.val=JGh_TX2_M1.Hash156.B00.input := by rfl
#print axioms cast156_0
theorem tail156 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash156.tail).map Fin.val=JGh_TX2_M1.Hash156.tail := by rfl
#print axioms tail156
theorem numeric156 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash156.message).map Fin.val=JGh_TX2_M1.Hash156.message := by
  simp only [JGh_TX2_M1.Hash156.message,JGh_TX2_M1.Hash156.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast156_0,tail156]
#print axioms numeric156
theorem hash156 : JFp_SHADigest.digest input156=value156 := by
  unfold input156 JFp_SHADigest.digest
  rw [numeric156,JGh_TX2_M1.Hash156.checked]
  rfl
#print axioms hash156
theorem address156 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [79,108,89,128,240,221,233,127,228,95,64,148,219,84,123,220,220,94,159,117,164,89,181,53,206,197,95,79,70,7,116,207]) value145)=input156 := by rfl
#print axioms address156
def tree156 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [79,108,89,128,240,221,233,127,228,95,64,148,219,84,123,220,220,94,159,117,164,89,181,53,206,197,95,79,70,7,116,207])) tree145
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
def input157 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash157.message
def value157 : State := JFp_SHADigest.output JGh_TX2_M1.Hash157.result
theorem cast157_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash157.B00.input).map Fin.val=JGh_TX2_M1.Hash157.B00.input := by rfl
#print axioms cast157_0
theorem tail157 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash157.tail).map Fin.val=JGh_TX2_M1.Hash157.tail := by rfl
#print axioms tail157
theorem numeric157 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash157.message).map Fin.val=JGh_TX2_M1.Hash157.message := by
  simp only [JGh_TX2_M1.Hash157.message,JGh_TX2_M1.Hash157.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast157_0,tail157]
#print axioms numeric157
theorem hash157 : JFp_SHADigest.digest input157=value157 := by
  unfold input157 JFp_SHADigest.digest
  rw [numeric157,JGh_TX2_M1.Hash157.checked]
  rfl
#print axioms hash157
theorem address157 : BinMerkle32Path.nodeInput (children value146 (JGc_TX2_HashBytes.state [74,28,108,176,140,202,10,70,55,105,207,14,98,39,31,53,103,54,134,75,220,181,149,104,222,170,139,72,19,184,148,224]))=input157 := by rfl
#print axioms address157
def tree157 : Tree := .branch tree146 (.supplied (JGc_TX2_HashBytes.state [74,28,108,176,140,202,10,70,55,105,207,14,98,39,31,53,103,54,134,75,220,181,149,104,222,170,139,72,19,184,148,224]))
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
def input158 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash158.message
def value158 : State := JFp_SHADigest.output JGh_TX2_M1.Hash158.result
theorem cast158_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash158.B00.input).map Fin.val=JGh_TX2_M1.Hash158.B00.input := by rfl
#print axioms cast158_0
theorem tail158 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash158.tail).map Fin.val=JGh_TX2_M1.Hash158.tail := by rfl
#print axioms tail158
theorem numeric158 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash158.message).map Fin.val=JGh_TX2_M1.Hash158.message := by
  simp only [JGh_TX2_M1.Hash158.message,JGh_TX2_M1.Hash158.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast158_0,tail158]
#print axioms numeric158
theorem hash158 : JFp_SHADigest.digest input158=value158 := by
  unfold input158 JFp_SHADigest.digest
  rw [numeric158,JGh_TX2_M1.Hash158.checked]
  rfl
#print axioms hash158
theorem address158 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [180,193,203,72,70,35,220,107,55,36,139,66,87,30,135,220,78,200,66,26,142,34,206,196,104,172,191,246,63,199,196,214]) value147)=input158 := by rfl
#print axioms address158
def tree158 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [180,193,203,72,70,35,220,107,55,36,139,66,87,30,135,220,78,200,66,26,142,34,206,196,104,172,191,246,63,199,196,214])) tree147
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
def input159 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash159.message
def value159 : State := JFp_SHADigest.output JGh_TX2_M1.Hash159.result
theorem cast159_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash159.B00.input).map Fin.val=JGh_TX2_M1.Hash159.B00.input := by rfl
#print axioms cast159_0
theorem tail159 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash159.tail).map Fin.val=JGh_TX2_M1.Hash159.tail := by rfl
#print axioms tail159
theorem numeric159 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash159.message).map Fin.val=JGh_TX2_M1.Hash159.message := by
  simp only [JGh_TX2_M1.Hash159.message,JGh_TX2_M1.Hash159.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast159_0,tail159]
#print axioms numeric159
theorem hash159 : JFp_SHADigest.digest input159=value159 := by
  unfold input159 JFp_SHADigest.digest
  rw [numeric159,JGh_TX2_M1.Hash159.checked]
  rfl
#print axioms hash159
theorem address159 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [222,183,124,211,163,44,129,50,210,200,8,43,44,53,37,161,107,120,175,184,161,143,43,8,208,74,107,208,67,251,215,209]) value148)=input159 := by rfl
#print axioms address159
def tree159 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [222,183,124,211,163,44,129,50,210,200,8,43,44,53,37,161,107,120,175,184,161,143,43,8,208,74,107,208,67,251,215,209])) tree148
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
def input160 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash160.message
def value160 : State := JFp_SHADigest.output JGh_TX2_M1.Hash160.result
theorem cast160_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash160.B00.input).map Fin.val=JGh_TX2_M1.Hash160.B00.input := by rfl
#print axioms cast160_0
theorem tail160 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash160.tail).map Fin.val=JGh_TX2_M1.Hash160.tail := by rfl
#print axioms tail160
theorem numeric160 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash160.message).map Fin.val=JGh_TX2_M1.Hash160.message := by
  simp only [JGh_TX2_M1.Hash160.message,JGh_TX2_M1.Hash160.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast160_0,tail160]
#print axioms numeric160
theorem hash160 : JFp_SHADigest.digest input160=value160 := by
  unfold input160 JFp_SHADigest.digest
  rw [numeric160,JGh_TX2_M1.Hash160.checked]
  rfl
#print axioms hash160
theorem address160 : BinMerkle32Path.nodeInput (children value149 (JGc_TX2_HashBytes.state [254,189,31,81,29,208,193,233,179,91,165,212,189,33,236,89,123,93,223,227,10,198,30,75,72,135,26,14,69,64,45,249]))=input160 := by rfl
#print axioms address160
def tree160 : Tree := .branch tree149 (.supplied (JGc_TX2_HashBytes.state [254,189,31,81,29,208,193,233,179,91,165,212,189,33,236,89,123,93,223,227,10,198,30,75,72,135,26,14,69,64,45,249]))
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
def input161 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash161.message
def value161 : State := JFp_SHADigest.output JGh_TX2_M1.Hash161.result
theorem cast161_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash161.B00.input).map Fin.val=JGh_TX2_M1.Hash161.B00.input := by rfl
#print axioms cast161_0
theorem tail161 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash161.tail).map Fin.val=JGh_TX2_M1.Hash161.tail := by rfl
#print axioms tail161
theorem numeric161 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash161.message).map Fin.val=JGh_TX2_M1.Hash161.message := by
  simp only [JGh_TX2_M1.Hash161.message,JGh_TX2_M1.Hash161.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast161_0,tail161]
#print axioms numeric161
theorem hash161 : JFp_SHADigest.digest input161=value161 := by
  unfold input161 JFp_SHADigest.digest
  rw [numeric161,JGh_TX2_M1.Hash161.checked]
  rfl
#print axioms hash161
theorem address161 : BinMerkle32Path.nodeInput (children value150 (JGc_TX2_HashBytes.state [125,179,140,223,84,63,248,207,79,4,254,76,50,105,252,113,154,218,31,6,172,77,212,91,67,94,96,253,37,229,243,212]))=input161 := by rfl
#print axioms address161
def tree161 : Tree := .branch tree150 (.supplied (JGc_TX2_HashBytes.state [125,179,140,223,84,63,248,207,79,4,254,76,50,105,252,113,154,218,31,6,172,77,212,91,67,94,96,253,37,229,243,212]))
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
def input162 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash162.message
def value162 : State := JFp_SHADigest.output JGh_TX2_M1.Hash162.result
theorem cast162_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash162.B00.input).map Fin.val=JGh_TX2_M1.Hash162.B00.input := by rfl
#print axioms cast162_0
theorem tail162 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash162.tail).map Fin.val=JGh_TX2_M1.Hash162.tail := by rfl
#print axioms tail162
theorem numeric162 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash162.message).map Fin.val=JGh_TX2_M1.Hash162.message := by
  simp only [JGh_TX2_M1.Hash162.message,JGh_TX2_M1.Hash162.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast162_0,tail162]
#print axioms numeric162
theorem hash162 : JFp_SHADigest.digest input162=value162 := by
  unfold input162 JFp_SHADigest.digest
  rw [numeric162,JGh_TX2_M1.Hash162.checked]
  rfl
#print axioms hash162
theorem address162 : BinMerkle32Path.nodeInput (children value151 (JGc_TX2_HashBytes.state [148,185,120,73,129,121,117,223,246,81,133,240,79,138,206,51,127,230,60,221,213,155,35,140,62,115,215,223,145,85,229,14]))=input162 := by rfl
#print axioms address162
def tree162 : Tree := .branch tree151 (.supplied (JGc_TX2_HashBytes.state [148,185,120,73,129,121,117,223,246,81,133,240,79,138,206,51,127,230,60,221,213,155,35,140,62,115,215,223,145,85,229,14]))
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
def input163 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash163.message
def value163 : State := JFp_SHADigest.output JGh_TX2_M1.Hash163.result
theorem cast163_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash163.B00.input).map Fin.val=JGh_TX2_M1.Hash163.B00.input := by rfl
#print axioms cast163_0
theorem tail163 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash163.tail).map Fin.val=JGh_TX2_M1.Hash163.tail := by rfl
#print axioms tail163
theorem numeric163 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash163.message).map Fin.val=JGh_TX2_M1.Hash163.message := by
  simp only [JGh_TX2_M1.Hash163.message,JGh_TX2_M1.Hash163.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast163_0,tail163]
#print axioms numeric163
theorem hash163 : JFp_SHADigest.digest input163=value163 := by
  unfold input163 JFp_SHADigest.digest
  rw [numeric163,JGh_TX2_M1.Hash163.checked]
  rfl
#print axioms hash163
theorem address163 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [82,44,102,52,93,97,36,97,250,159,210,80,233,1,56,234,81,171,0,214,205,101,168,12,128,47,171,190,96,28,134,18]) value152)=input163 := by rfl
#print axioms address163
def tree163 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [82,44,102,52,93,97,36,97,250,159,210,80,233,1,56,234,81,171,0,214,205,101,168,12,128,47,171,190,96,28,134,18])) tree152
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
def input164 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash164.message
def value164 : State := JFp_SHADigest.output JGh_TX2_M1.Hash164.result
theorem cast164_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash164.B00.input).map Fin.val=JGh_TX2_M1.Hash164.B00.input := by rfl
#print axioms cast164_0
theorem tail164 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash164.tail).map Fin.val=JGh_TX2_M1.Hash164.tail := by rfl
#print axioms tail164
theorem numeric164 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash164.message).map Fin.val=JGh_TX2_M1.Hash164.message := by
  simp only [JGh_TX2_M1.Hash164.message,JGh_TX2_M1.Hash164.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast164_0,tail164]
#print axioms numeric164
theorem hash164 : JFp_SHADigest.digest input164=value164 := by
  unfold input164 JFp_SHADigest.digest
  rw [numeric164,JGh_TX2_M1.Hash164.checked]
  rfl
#print axioms hash164
theorem address164 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [54,157,250,112,154,175,37,244,121,98,202,70,16,157,20,193,216,197,16,217,246,49,23,128,81,70,252,84,93,154,96,211]) value153)=input164 := by rfl
#print axioms address164
def tree164 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [54,157,250,112,154,175,37,244,121,98,202,70,16,157,20,193,216,197,16,217,246,49,23,128,81,70,252,84,93,154,96,211])) tree153
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
def input165 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash165.message
def value165 : State := JFp_SHADigest.output JGh_TX2_M1.Hash165.result
theorem cast165_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash165.B00.input).map Fin.val=JGh_TX2_M1.Hash165.B00.input := by rfl
#print axioms cast165_0
theorem tail165 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash165.tail).map Fin.val=JGh_TX2_M1.Hash165.tail := by rfl
#print axioms tail165
theorem numeric165 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash165.message).map Fin.val=JGh_TX2_M1.Hash165.message := by
  simp only [JGh_TX2_M1.Hash165.message,JGh_TX2_M1.Hash165.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast165_0,tail165]
#print axioms numeric165
theorem hash165 : JFp_SHADigest.digest input165=value165 := by
  unfold input165 JFp_SHADigest.digest
  rw [numeric165,JGh_TX2_M1.Hash165.checked]
  rfl
#print axioms hash165
theorem address165 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [8,95,41,129,128,138,153,200,28,88,203,75,164,57,175,143,60,217,244,161,197,157,250,28,153,248,23,196,237,237,138,91]) value154)=input165 := by rfl
#print axioms address165
def tree165 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [8,95,41,129,128,138,153,200,28,88,203,75,164,57,175,143,60,217,244,161,197,157,250,28,153,248,23,196,237,237,138,91])) tree154
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
end AspisR1.JGh_TX2_M1Roots
end
