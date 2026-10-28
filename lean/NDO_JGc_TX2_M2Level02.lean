import NDO_JGc_TX2_M2Level01
import NDO_JGc_TX2_M2H036
import NDO_JGc_TX2_M2H040
import NDO_JGc_TX2_M2H044
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input036 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash036.message
def value036 : State := JFp_SHADigest.output JGc_TX2_M2.Hash036.result
theorem cast036_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash036.B00.input).map Fin.val=JGc_TX2_M2.Hash036.B00.input := by rfl
#print axioms cast036_0
theorem tail036 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash036.tail).map Fin.val=JGc_TX2_M2.Hash036.tail := by rfl
#print axioms tail036
theorem numeric036 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash036.message).map Fin.val=JGc_TX2_M2.Hash036.message := by
  simp only [JGc_TX2_M2.Hash036.message,JGc_TX2_M2.Hash036.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast036_0,tail036]
#print axioms numeric036
theorem hash036 : JFp_SHADigest.digest input036=value036 := by
  unfold input036 JFp_SHADigest.digest
  rw [numeric036,JGc_TX2_M2.Hash036.checked]
  rfl
#print axioms hash036
theorem address036 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [142,71,54,188,107,133,110,82,78,24,73,35,118,78,156,74,51,2,8,253,198,10,145,101,147,12,247,219,22,143,114,74]) value024)=input036 := by rfl
#print axioms address036
def tree036 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [142,71,54,188,107,133,110,82,78,24,73,35,118,78,156,74,51,2,8,253,198,10,145,101,147,12,247,219,22,143,114,74])) tree024
theorem root036 : root JFp_SHADigest.digest tree036=value036 := by
  rw [tree036,root,root024]
  exact (congrArg JFp_SHADigest.digest address036).trans hash036
#print axioms root036
theorem shape036 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 3568=tree036 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 3568)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 3568 (by decide),siblings 2 (by decide) 3568 (by decide)]
  rw [shape024 f g inputs siblings]
  rfl
#print axioms shape036
def input037 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash037.message
def value037 : State := JFp_SHADigest.output JGc_TX2_M2.Hash037.result
theorem cast037_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash037.B00.input).map Fin.val=JGc_TX2_M2.Hash037.B00.input := by rfl
#print axioms cast037_0
theorem tail037 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash037.tail).map Fin.val=JGc_TX2_M2.Hash037.tail := by rfl
#print axioms tail037
theorem numeric037 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash037.message).map Fin.val=JGc_TX2_M2.Hash037.message := by
  simp only [JGc_TX2_M2.Hash037.message,JGc_TX2_M2.Hash037.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast037_0,tail037]
#print axioms numeric037
theorem hash037 : JFp_SHADigest.digest input037=value037 := by
  unfold input037 JFp_SHADigest.digest
  rw [numeric037,JGc_TX2_M2.Hash037.checked]
  rfl
#print axioms hash037
theorem address037 : BinMerkle32Path.nodeInput (children value025 (JGc_TX2_HashBytes.state [74,30,88,56,127,42,19,72,31,188,143,39,106,80,217,195,93,172,40,241,251,138,112,28,199,224,139,49,101,237,114,234]))=input037 := by rfl
#print axioms address037
def tree037 : Tree := .branch tree025 (.supplied (JGc_TX2_HashBytes.state [74,30,88,56,127,42,19,72,31,188,143,39,106,80,217,195,93,172,40,241,251,138,112,28,199,224,139,49,101,237,114,234]))
theorem root037 : root JFp_SHADigest.digest tree037=value037 := by
  rw [tree037,root,root025]
  exact (congrArg JFp_SHADigest.digest address037).trans hash037
#print axioms root037
theorem shape037 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 5312=tree037 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 5312)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape025 f g inputs siblings]
  rw [unoccupied f g 2 5316 (by decide),siblings 2 (by decide) 5316 (by decide)]
  rfl
#print axioms shape037
def input038 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash038.message
def value038 : State := JFp_SHADigest.output JGc_TX2_M2.Hash038.result
theorem cast038_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash038.B00.input).map Fin.val=JGc_TX2_M2.Hash038.B00.input := by rfl
#print axioms cast038_0
theorem tail038 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash038.tail).map Fin.val=JGc_TX2_M2.Hash038.tail := by rfl
#print axioms tail038
theorem numeric038 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash038.message).map Fin.val=JGc_TX2_M2.Hash038.message := by
  simp only [JGc_TX2_M2.Hash038.message,JGc_TX2_M2.Hash038.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast038_0,tail038]
#print axioms numeric038
theorem hash038 : JFp_SHADigest.digest input038=value038 := by
  unfold input038 JFp_SHADigest.digest
  rw [numeric038,JGc_TX2_M2.Hash038.checked]
  rfl
#print axioms hash038
theorem address038 : BinMerkle32Path.nodeInput (children value026 (JGc_TX2_HashBytes.state [206,11,178,87,46,111,7,245,239,183,26,116,42,155,14,231,45,73,139,243,181,182,22,57,169,101,81,27,133,115,213,188]))=input038 := by rfl
#print axioms address038
def tree038 : Tree := .branch tree026 (.supplied (JGc_TX2_HashBytes.state [206,11,178,87,46,111,7,245,239,183,26,116,42,155,14,231,45,73,139,243,181,182,22,57,169,101,81,27,133,115,213,188]))
theorem root038 : root JFp_SHADigest.digest tree038=value038 := by
  rw [tree038,root,root026]
  exact (congrArg JFp_SHADigest.digest address038).trans hash038
#print axioms root038
theorem shape038 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 10536=tree038 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 10536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape026 f g inputs siblings]
  rw [unoccupied f g 2 10540 (by decide),siblings 2 (by decide) 10540 (by decide)]
  rfl
#print axioms shape038
def input039 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash039.message
def value039 : State := JFp_SHADigest.output JGc_TX2_M2.Hash039.result
theorem cast039_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash039.B00.input).map Fin.val=JGc_TX2_M2.Hash039.B00.input := by rfl
#print axioms cast039_0
theorem tail039 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash039.tail).map Fin.val=JGc_TX2_M2.Hash039.tail := by rfl
#print axioms tail039
theorem numeric039 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash039.message).map Fin.val=JGc_TX2_M2.Hash039.message := by
  simp only [JGc_TX2_M2.Hash039.message,JGc_TX2_M2.Hash039.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast039_0,tail039]
#print axioms numeric039
theorem hash039 : JFp_SHADigest.digest input039=value039 := by
  unfold input039 JFp_SHADigest.digest
  rw [numeric039,JGc_TX2_M2.Hash039.checked]
  rfl
#print axioms hash039
theorem address039 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [156,227,32,66,1,53,116,61,225,43,126,205,31,159,50,40,201,176,218,21,156,174,60,26,165,45,21,219,171,1,178,128]) value027)=input039 := by rfl
#print axioms address039
def tree039 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [156,227,32,66,1,53,116,61,225,43,126,205,31,159,50,40,201,176,218,21,156,174,60,26,165,45,21,219,171,1,178,128])) tree027
theorem root039 : root JFp_SHADigest.digest tree039=value039 := by
  rw [tree039,root,root027]
  exact (congrArg JFp_SHADigest.digest address039).trans hash039
#print axioms root039
theorem shape039 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 13840=tree039 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 13840)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 13840 (by decide),siblings 2 (by decide) 13840 (by decide)]
  rw [shape027 f g inputs siblings]
  rfl
#print axioms shape039
def input040 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash040.message
def value040 : State := JFp_SHADigest.output JGc_TX2_M2.Hash040.result
theorem cast040_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash040.B00.input).map Fin.val=JGc_TX2_M2.Hash040.B00.input := by rfl
#print axioms cast040_0
theorem tail040 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash040.tail).map Fin.val=JGc_TX2_M2.Hash040.tail := by rfl
#print axioms tail040
theorem numeric040 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash040.message).map Fin.val=JGc_TX2_M2.Hash040.message := by
  simp only [JGc_TX2_M2.Hash040.message,JGc_TX2_M2.Hash040.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast040_0,tail040]
#print axioms numeric040
theorem hash040 : JFp_SHADigest.digest input040=value040 := by
  unfold input040 JFp_SHADigest.digest
  rw [numeric040,JGc_TX2_M2.Hash040.checked]
  rfl
#print axioms hash040
theorem address040 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [203,230,190,57,102,61,126,184,252,81,69,36,204,93,127,113,125,96,51,17,206,230,4,207,149,49,250,81,52,72,1,82]) value028)=input040 := by rfl
#print axioms address040
def tree040 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [203,230,190,57,102,61,126,184,252,81,69,36,204,93,127,113,125,96,51,17,206,230,4,207,149,49,250,81,52,72,1,82])) tree028
theorem root040 : root JFp_SHADigest.digest tree040=value040 := by
  rw [tree040,root,root028]
  exact (congrArg JFp_SHADigest.digest address040).trans hash040
#print axioms root040
theorem shape040 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 15960=tree040 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 15960)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 15960 (by decide),siblings 2 (by decide) 15960 (by decide)]
  rw [shape028 f g inputs siblings]
  rfl
#print axioms shape040
def input041 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash041.message
def value041 : State := JFp_SHADigest.output JGc_TX2_M2.Hash041.result
theorem cast041_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash041.B00.input).map Fin.val=JGc_TX2_M2.Hash041.B00.input := by rfl
#print axioms cast041_0
theorem tail041 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash041.tail).map Fin.val=JGc_TX2_M2.Hash041.tail := by rfl
#print axioms tail041
theorem numeric041 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash041.message).map Fin.val=JGc_TX2_M2.Hash041.message := by
  simp only [JGc_TX2_M2.Hash041.message,JGc_TX2_M2.Hash041.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast041_0,tail041]
#print axioms numeric041
theorem hash041 : JFp_SHADigest.digest input041=value041 := by
  unfold input041 JFp_SHADigest.digest
  rw [numeric041,JGc_TX2_M2.Hash041.checked]
  rfl
#print axioms hash041
theorem address041 : BinMerkle32Path.nodeInput (children value029 (JGc_TX2_HashBytes.state [120,163,23,75,229,163,190,245,25,235,189,36,155,129,116,31,246,96,195,137,212,238,94,152,43,249,59,40,204,149,245,225]))=input041 := by rfl
#print axioms address041
def tree041 : Tree := .branch tree029 (.supplied (JGc_TX2_HashBytes.state [120,163,23,75,229,163,190,245,25,235,189,36,155,129,116,31,246,96,195,137,212,238,94,152,43,249,59,40,204,149,245,225]))
theorem root041 : root JFp_SHADigest.digest tree041=value041 := by
  rw [tree041,root,root029]
  exact (congrArg JFp_SHADigest.digest address041).trans hash041
#print axioms root041
theorem shape041 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 33088=tree041 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 33088)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape029 f g inputs siblings]
  rw [unoccupied f g 2 33092 (by decide),siblings 2 (by decide) 33092 (by decide)]
  rfl
#print axioms shape041
def input042 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash042.message
def value042 : State := JFp_SHADigest.output JGc_TX2_M2.Hash042.result
theorem cast042_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash042.B00.input).map Fin.val=JGc_TX2_M2.Hash042.B00.input := by rfl
#print axioms cast042_0
theorem tail042 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash042.tail).map Fin.val=JGc_TX2_M2.Hash042.tail := by rfl
#print axioms tail042
theorem numeric042 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash042.message).map Fin.val=JGc_TX2_M2.Hash042.message := by
  simp only [JGc_TX2_M2.Hash042.message,JGc_TX2_M2.Hash042.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast042_0,tail042]
#print axioms numeric042
theorem hash042 : JFp_SHADigest.digest input042=value042 := by
  unfold input042 JFp_SHADigest.digest
  rw [numeric042,JGc_TX2_M2.Hash042.checked]
  rfl
#print axioms hash042
theorem address042 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [14,28,34,57,248,175,178,171,228,145,45,180,7,239,120,13,208,166,227,58,25,179,76,71,40,183,89,53,119,141,253,147]) value030)=input042 := by rfl
#print axioms address042
def tree042 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [14,28,34,57,248,175,178,171,228,145,45,180,7,239,120,13,208,166,227,58,25,179,76,71,40,183,89,53,119,141,253,147])) tree030
theorem root042 : root JFp_SHADigest.digest tree042=value042 := by
  rw [tree042,root,root030]
  exact (congrArg JFp_SHADigest.digest address042).trans hash042
#print axioms root042
theorem shape042 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 37400=tree042 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 37400)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 37400 (by decide),siblings 2 (by decide) 37400 (by decide)]
  rw [shape030 f g inputs siblings]
  rfl
#print axioms shape042
def input043 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash043.message
def value043 : State := JFp_SHADigest.output JGc_TX2_M2.Hash043.result
theorem cast043_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash043.B00.input).map Fin.val=JGc_TX2_M2.Hash043.B00.input := by rfl
#print axioms cast043_0
theorem tail043 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash043.tail).map Fin.val=JGc_TX2_M2.Hash043.tail := by rfl
#print axioms tail043
theorem numeric043 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash043.message).map Fin.val=JGc_TX2_M2.Hash043.message := by
  simp only [JGc_TX2_M2.Hash043.message,JGc_TX2_M2.Hash043.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast043_0,tail043]
#print axioms numeric043
theorem hash043 : JFp_SHADigest.digest input043=value043 := by
  unfold input043 JFp_SHADigest.digest
  rw [numeric043,JGc_TX2_M2.Hash043.checked]
  rfl
#print axioms hash043
theorem address043 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [178,62,234,178,9,104,69,132,134,195,173,184,104,113,115,99,58,180,164,232,36,99,7,108,99,193,68,245,243,39,190,128]) value031)=input043 := by rfl
#print axioms address043
def tree043 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [178,62,234,178,9,104,69,132,134,195,173,184,104,113,115,99,58,180,164,232,36,99,7,108,99,193,68,245,243,39,190,128])) tree031
theorem root043 : root JFp_SHADigest.digest tree043=value043 := by
  rw [tree043,root,root031]
  exact (congrArg JFp_SHADigest.digest address043).trans hash043
#print axioms root043
theorem shape043 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 41536=tree043 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 41536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 41536 (by decide),siblings 2 (by decide) 41536 (by decide)]
  rw [shape031 f g inputs siblings]
  rfl
#print axioms shape043
def input044 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash044.message
def value044 : State := JFp_SHADigest.output JGc_TX2_M2.Hash044.result
theorem cast044_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash044.B00.input).map Fin.val=JGc_TX2_M2.Hash044.B00.input := by rfl
#print axioms cast044_0
theorem tail044 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash044.tail).map Fin.val=JGc_TX2_M2.Hash044.tail := by rfl
#print axioms tail044
theorem numeric044 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash044.message).map Fin.val=JGc_TX2_M2.Hash044.message := by
  simp only [JGc_TX2_M2.Hash044.message,JGc_TX2_M2.Hash044.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast044_0,tail044]
#print axioms numeric044
theorem hash044 : JFp_SHADigest.digest input044=value044 := by
  unfold input044 JFp_SHADigest.digest
  rw [numeric044,JGc_TX2_M2.Hash044.checked]
  rfl
#print axioms hash044
theorem address044 : BinMerkle32Path.nodeInput (children value032 (JGc_TX2_HashBytes.state [221,48,192,214,43,179,218,136,161,122,96,85,118,17,76,248,85,214,125,182,28,105,218,151,59,182,71,42,135,79,183,244]))=input044 := by rfl
#print axioms address044
def tree044 : Tree := .branch tree032 (.supplied (JGc_TX2_HashBytes.state [221,48,192,214,43,179,218,136,161,122,96,85,118,17,76,248,85,214,125,182,28,105,218,151,59,182,71,42,135,79,183,244]))
theorem root044 : root JFp_SHADigest.digest tree044=value044 := by
  rw [tree044,root,root032]
  exact (congrArg JFp_SHADigest.digest address044).trans hash044
#print axioms root044
theorem shape044 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 44520=tree044 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 44520)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape032 f g inputs siblings]
  rw [unoccupied f g 2 44524 (by decide),siblings 2 (by decide) 44524 (by decide)]
  rfl
#print axioms shape044
def input045 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash045.message
def value045 : State := JFp_SHADigest.output JGc_TX2_M2.Hash045.result
theorem cast045_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash045.B00.input).map Fin.val=JGc_TX2_M2.Hash045.B00.input := by rfl
#print axioms cast045_0
theorem tail045 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash045.tail).map Fin.val=JGc_TX2_M2.Hash045.tail := by rfl
#print axioms tail045
theorem numeric045 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash045.message).map Fin.val=JGc_TX2_M2.Hash045.message := by
  simp only [JGc_TX2_M2.Hash045.message,JGc_TX2_M2.Hash045.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast045_0,tail045]
#print axioms numeric045
theorem hash045 : JFp_SHADigest.digest input045=value045 := by
  unfold input045 JFp_SHADigest.digest
  rw [numeric045,JGc_TX2_M2.Hash045.checked]
  rfl
#print axioms hash045
theorem address045 : BinMerkle32Path.nodeInput (children value033 (JGc_TX2_HashBytes.state [217,198,135,10,247,252,247,246,146,73,29,244,198,43,86,74,43,7,122,190,168,254,172,72,101,127,251,76,155,109,142,243]))=input045 := by rfl
#print axioms address045
def tree045 : Tree := .branch tree033 (.supplied (JGc_TX2_HashBytes.state [217,198,135,10,247,252,247,246,146,73,29,244,198,43,86,74,43,7,122,190,168,254,172,72,101,127,251,76,155,109,142,243]))
theorem root045 : root JFp_SHADigest.digest tree045=value045 := by
  rw [tree045,root,root033]
  exact (congrArg JFp_SHADigest.digest address045).trans hash045
#print axioms root045
theorem shape045 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 44904=tree045 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 44904)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape033 f g inputs siblings]
  rw [unoccupied f g 2 44908 (by decide),siblings 2 (by decide) 44908 (by decide)]
  rfl
#print axioms shape045
def input046 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash046.message
def value046 : State := JFp_SHADigest.output JGc_TX2_M2.Hash046.result
theorem cast046_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash046.B00.input).map Fin.val=JGc_TX2_M2.Hash046.B00.input := by rfl
#print axioms cast046_0
theorem tail046 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash046.tail).map Fin.val=JGc_TX2_M2.Hash046.tail := by rfl
#print axioms tail046
theorem numeric046 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash046.message).map Fin.val=JGc_TX2_M2.Hash046.message := by
  simp only [JGc_TX2_M2.Hash046.message,JGc_TX2_M2.Hash046.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast046_0,tail046]
#print axioms numeric046
theorem hash046 : JFp_SHADigest.digest input046=value046 := by
  unfold input046 JFp_SHADigest.digest
  rw [numeric046,JGc_TX2_M2.Hash046.checked]
  rfl
#print axioms hash046
theorem address046 : BinMerkle32Path.nodeInput (children value034 (JGc_TX2_HashBytes.state [109,115,192,31,41,81,198,223,206,2,158,136,206,203,255,61,129,211,85,123,147,41,151,174,213,209,220,252,211,163,108,220]))=input046 := by rfl
#print axioms address046
def tree046 : Tree := .branch tree034 (.supplied (JGc_TX2_HashBytes.state [109,115,192,31,41,81,198,223,206,2,158,136,206,203,255,61,129,211,85,123,147,41,151,174,213,209,220,252,211,163,108,220]))
theorem root046 : root JFp_SHADigest.digest tree046=value046 := by
  rw [tree046,root,root034]
  exact (congrArg JFp_SHADigest.digest address046).trans hash046
#print axioms root046
theorem shape046 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 46408=tree046 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 46408)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape034 f g inputs siblings]
  rw [unoccupied f g 2 46412 (by decide),siblings 2 (by decide) 46412 (by decide)]
  rfl
#print axioms shape046
def input047 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash047.message
def value047 : State := JFp_SHADigest.output JGc_TX2_M2.Hash047.result
theorem cast047_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash047.B00.input).map Fin.val=JGc_TX2_M2.Hash047.B00.input := by rfl
#print axioms cast047_0
theorem tail047 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash047.tail).map Fin.val=JGc_TX2_M2.Hash047.tail := by rfl
#print axioms tail047
theorem numeric047 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash047.message).map Fin.val=JGc_TX2_M2.Hash047.message := by
  simp only [JGc_TX2_M2.Hash047.message,JGc_TX2_M2.Hash047.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast047_0,tail047]
#print axioms numeric047
theorem hash047 : JFp_SHADigest.digest input047=value047 := by
  unfold input047 JFp_SHADigest.digest
  rw [numeric047,JGc_TX2_M2.Hash047.checked]
  rfl
#print axioms hash047
theorem address047 : BinMerkle32Path.nodeInput (children value035 (JGc_TX2_HashBytes.state [29,225,72,200,54,205,19,189,140,62,230,165,80,225,188,225,255,120,73,38,198,94,209,252,38,156,219,161,245,119,125,66]))=input047 := by rfl
#print axioms address047
def tree047 : Tree := .branch tree035 (.supplied (JGc_TX2_HashBytes.state [29,225,72,200,54,205,19,189,140,62,230,165,80,225,188,225,255,120,73,38,198,94,209,252,38,156,219,161,245,119,125,66]))
theorem root047 : root JFp_SHADigest.digest tree047=value047 := by
  rw [tree047,root,root035]
  exact (congrArg JFp_SHADigest.digest address047).trans hash047
#print axioms root047
theorem shape047 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 54520=tree047 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 54520)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape035 f g inputs siblings]
  rw [unoccupied f g 2 54524 (by decide),siblings 2 (by decide) 54524 (by decide)]
  rfl
#print axioms shape047
end AspisR1.JGc_TX2_M2Roots
end
