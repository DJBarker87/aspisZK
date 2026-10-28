import NDO_JGh_TX2_M1Level01
import NDO_JGf_TX2_M1W010
import NDO_JGf_TX2_M1W011
import NDO_JGf_TX2_M1W012
import NDO_JGh_TX2_M1W013
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input036 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash036.message
def value036 : State := JFp_SHADigest.output JGf_TX2_M1.Hash036.result
theorem cast036_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash036.B00.input).map Fin.val=JGf_TX2_M1.Hash036.B00.input := by rfl
#print axioms cast036_0
theorem tail036 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash036.tail).map Fin.val=JGf_TX2_M1.Hash036.tail := by rfl
#print axioms tail036
theorem numeric036 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash036.message).map Fin.val=JGf_TX2_M1.Hash036.message := by
  simp only [JGf_TX2_M1.Hash036.message,JGf_TX2_M1.Hash036.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast036_0,tail036]
#print axioms numeric036
theorem hash036 : JFp_SHADigest.digest input036=value036 := by
  unfold input036 JFp_SHADigest.digest
  rw [numeric036,JGf_TX2_M1.Hash036.checked]
  rfl
#print axioms hash036
theorem address036 : BinMerkle32Path.nodeInput (children value024 (JGc_TX2_HashBytes.state [97,127,45,224,226,170,233,49,234,134,73,253,142,237,10,38,127,193,71,183,230,237,164,189,249,186,117,212,49,152,176,19]))=input036 := by rfl
#print axioms address036
def tree036 : Tree := .branch tree024 (.supplied (JGc_TX2_HashBytes.state [97,127,45,224,226,170,233,49,234,134,73,253,142,237,10,38,127,193,71,183,230,237,164,189,249,186,117,212,49,152,176,19]))
theorem root036 : root JFp_SHADigest.digest tree036=value036 := by
  rw [tree036,root,root024]
  exact (congrArg JFp_SHADigest.digest address036).trans hash036
#print axioms root036
theorem shape036 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 14296=tree036 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 14296)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape024 f g inputs siblings]
  rw [unoccupied f g 2 14300 (by decide),siblings 2 (by decide) 14300 (by decide)]
  rfl
#print axioms shape036
def input037 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash037.message
def value037 : State := JFp_SHADigest.output JGf_TX2_M1.Hash037.result
theorem cast037_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash037.B00.input).map Fin.val=JGf_TX2_M1.Hash037.B00.input := by rfl
#print axioms cast037_0
theorem tail037 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash037.tail).map Fin.val=JGf_TX2_M1.Hash037.tail := by rfl
#print axioms tail037
theorem numeric037 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash037.message).map Fin.val=JGf_TX2_M1.Hash037.message := by
  simp only [JGf_TX2_M1.Hash037.message,JGf_TX2_M1.Hash037.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast037_0,tail037]
#print axioms numeric037
theorem hash037 : JFp_SHADigest.digest input037=value037 := by
  unfold input037 JFp_SHADigest.digest
  rw [numeric037,JGf_TX2_M1.Hash037.checked]
  rfl
#print axioms hash037
theorem address037 : BinMerkle32Path.nodeInput (children value025 (JGc_TX2_HashBytes.state [55,134,167,154,32,84,223,159,219,123,45,8,206,182,36,8,143,2,22,155,30,49,237,73,95,111,245,167,63,236,244,215]))=input037 := by rfl
#print axioms address037
def tree037 : Tree := .branch tree025 (.supplied (JGc_TX2_HashBytes.state [55,134,167,154,32,84,223,159,219,123,45,8,206,182,36,8,143,2,22,155,30,49,237,73,95,111,245,167,63,236,244,215]))
theorem root037 : root JFp_SHADigest.digest tree037=value037 := by
  rw [tree037,root,root025]
  exact (congrArg JFp_SHADigest.digest address037).trans hash037
#print axioms root037
theorem shape037 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 21248=tree037 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 21248)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape025 f g inputs siblings]
  rw [unoccupied f g 2 21252 (by decide),siblings 2 (by decide) 21252 (by decide)]
  rfl
#print axioms shape037
def input038 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash038.message
def value038 : State := JFp_SHADigest.output JGf_TX2_M1.Hash038.result
theorem cast038_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash038.B00.input).map Fin.val=JGf_TX2_M1.Hash038.B00.input := by rfl
#print axioms cast038_0
theorem tail038 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash038.tail).map Fin.val=JGf_TX2_M1.Hash038.tail := by rfl
#print axioms tail038
theorem numeric038 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash038.message).map Fin.val=JGf_TX2_M1.Hash038.message := by
  simp only [JGf_TX2_M1.Hash038.message,JGf_TX2_M1.Hash038.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast038_0,tail038]
#print axioms numeric038
theorem hash038 : JFp_SHADigest.digest input038=value038 := by
  unfold input038 JFp_SHADigest.digest
  rw [numeric038,JGf_TX2_M1.Hash038.checked]
  rfl
#print axioms hash038
theorem address038 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [64,2,44,46,241,45,160,34,120,196,208,37,152,255,204,191,252,202,201,221,153,96,198,26,94,15,113,122,33,88,64,28]) value026)=input038 := by rfl
#print axioms address038
def tree038 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [64,2,44,46,241,45,160,34,120,196,208,37,152,255,204,191,252,202,201,221,153,96,198,26,94,15,113,122,33,88,64,28])) tree026
theorem root038 : root JFp_SHADigest.digest tree038=value038 := by
  rw [tree038,root,root026]
  exact (congrArg JFp_SHADigest.digest address038).trans hash038
#print axioms root038
theorem shape038 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 42152=tree038 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 42152)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 42152 (by decide),siblings 2 (by decide) 42152 (by decide)]
  rw [shape026 f g inputs siblings]
  rfl
#print axioms shape038
def input039 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash039.message
def value039 : State := JFp_SHADigest.output JGf_TX2_M1.Hash039.result
theorem cast039_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash039.B00.input).map Fin.val=JGf_TX2_M1.Hash039.B00.input := by rfl
#print axioms cast039_0
theorem tail039 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash039.tail).map Fin.val=JGf_TX2_M1.Hash039.tail := by rfl
#print axioms tail039
theorem numeric039 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash039.message).map Fin.val=JGf_TX2_M1.Hash039.message := by
  simp only [JGf_TX2_M1.Hash039.message,JGf_TX2_M1.Hash039.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast039_0,tail039]
#print axioms numeric039
theorem hash039 : JFp_SHADigest.digest input039=value039 := by
  unfold input039 JFp_SHADigest.digest
  rw [numeric039,JGf_TX2_M1.Hash039.checked]
  rfl
#print axioms hash039
theorem address039 : BinMerkle32Path.nodeInput (children value027 (JGc_TX2_HashBytes.state [94,143,135,120,251,114,163,154,6,3,87,192,188,32,202,66,233,97,109,140,6,215,197,145,60,155,46,91,223,31,174,88]))=input039 := by rfl
#print axioms address039
def tree039 : Tree := .branch tree027 (.supplied (JGc_TX2_HashBytes.state [94,143,135,120,251,114,163,154,6,3,87,192,188,32,202,66,233,97,109,140,6,215,197,145,60,155,46,91,223,31,174,88]))
theorem root039 : root JFp_SHADigest.digest tree039=value039 := by
  rw [tree039,root,root027]
  exact (congrArg JFp_SHADigest.digest address039).trans hash039
#print axioms root039
theorem shape039 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 55376=tree039 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 55376)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape027 f g inputs siblings]
  rw [unoccupied f g 2 55380 (by decide),siblings 2 (by decide) 55380 (by decide)]
  rfl
#print axioms shape039
def input040 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash040.message
def value040 : State := JFp_SHADigest.output JGf_TX2_M1.Hash040.result
theorem cast040_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash040.B00.input).map Fin.val=JGf_TX2_M1.Hash040.B00.input := by rfl
#print axioms cast040_0
theorem tail040 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash040.tail).map Fin.val=JGf_TX2_M1.Hash040.tail := by rfl
#print axioms tail040
theorem numeric040 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash040.message).map Fin.val=JGf_TX2_M1.Hash040.message := by
  simp only [JGf_TX2_M1.Hash040.message,JGf_TX2_M1.Hash040.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast040_0,tail040]
#print axioms numeric040
theorem hash040 : JFp_SHADigest.digest input040=value040 := by
  unfold input040 JFp_SHADigest.digest
  rw [numeric040,JGf_TX2_M1.Hash040.checked]
  rfl
#print axioms hash040
theorem address040 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [166,240,188,205,87,246,220,78,119,242,202,113,95,112,228,101,111,124,44,88,53,182,231,191,10,212,92,239,228,176,66,74]) value028)=input040 := by rfl
#print axioms address040
def tree040 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [166,240,188,205,87,246,220,78,119,242,202,113,95,112,228,101,111,124,44,88,53,182,231,191,10,212,92,239,228,176,66,74])) tree028
theorem root040 : root JFp_SHADigest.digest tree040=value040 := by
  rw [tree040,root,root028]
  exact (congrArg JFp_SHADigest.digest address040).trans hash040
#print axioms root040
theorem shape040 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 63856=tree040 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 63856)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 63856 (by decide),siblings 2 (by decide) 63856 (by decide)]
  rw [shape028 f g inputs siblings]
  rfl
#print axioms shape040
def input041 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash041.message
def value041 : State := JFp_SHADigest.output JGf_TX2_M1.Hash041.result
theorem cast041_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash041.B00.input).map Fin.val=JGf_TX2_M1.Hash041.B00.input := by rfl
#print axioms cast041_0
theorem tail041 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash041.tail).map Fin.val=JGf_TX2_M1.Hash041.tail := by rfl
#print axioms tail041
theorem numeric041 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash041.message).map Fin.val=JGf_TX2_M1.Hash041.message := by
  simp only [JGf_TX2_M1.Hash041.message,JGf_TX2_M1.Hash041.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast041_0,tail041]
#print axioms numeric041
theorem hash041 : JFp_SHADigest.digest input041=value041 := by
  unfold input041 JFp_SHADigest.digest
  rw [numeric041,JGf_TX2_M1.Hash041.checked]
  rfl
#print axioms hash041
theorem address041 : BinMerkle32Path.nodeInput (children value029 (JGc_TX2_HashBytes.state [50,110,138,55,85,52,37,101,181,66,44,4,215,27,106,50,145,156,227,241,190,145,73,161,14,84,188,105,217,219,70,28]))=input041 := by rfl
#print axioms address041
def tree041 : Tree := .branch tree029 (.supplied (JGc_TX2_HashBytes.state [50,110,138,55,85,52,37,101,181,66,44,4,215,27,106,50,145,156,227,241,190,145,73,161,14,84,188,105,217,219,70,28]))
theorem root041 : root JFp_SHADigest.digest tree041=value041 := by
  rw [tree041,root,root029]
  exact (congrArg JFp_SHADigest.digest address041).trans hash041
#print axioms root041
theorem shape041 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 132352=tree041 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 132352)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape029 f g inputs siblings]
  rw [unoccupied f g 2 132356 (by decide),siblings 2 (by decide) 132356 (by decide)]
  rfl
#print axioms shape041
def input042 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash042.message
def value042 : State := JFp_SHADigest.output JGf_TX2_M1.Hash042.result
theorem cast042_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash042.B00.input).map Fin.val=JGf_TX2_M1.Hash042.B00.input := by rfl
#print axioms cast042_0
theorem tail042 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash042.tail).map Fin.val=JGf_TX2_M1.Hash042.tail := by rfl
#print axioms tail042
theorem numeric042 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash042.message).map Fin.val=JGf_TX2_M1.Hash042.message := by
  simp only [JGf_TX2_M1.Hash042.message,JGf_TX2_M1.Hash042.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast042_0,tail042]
#print axioms numeric042
theorem hash042 : JFp_SHADigest.digest input042=value042 := by
  unfold input042 JFp_SHADigest.digest
  rw [numeric042,JGf_TX2_M1.Hash042.checked]
  rfl
#print axioms hash042
theorem address042 : BinMerkle32Path.nodeInput (children value030 (JGc_TX2_HashBytes.state [2,179,245,189,108,52,207,91,132,34,120,104,44,35,237,157,117,47,189,147,220,3,126,153,141,11,193,62,160,114,102,191]))=input042 := by rfl
#print axioms address042
def tree042 : Tree := .branch tree030 (.supplied (JGc_TX2_HashBytes.state [2,179,245,189,108,52,207,91,132,34,120,104,44,35,237,157,117,47,189,147,220,3,126,153,141,11,193,62,160,114,102,191]))
theorem root042 : root JFp_SHADigest.digest tree042=value042 := by
  rw [tree042,root,root030]
  exact (congrArg JFp_SHADigest.digest address042).trans hash042
#print axioms root042
theorem shape042 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 149624=tree042 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 149624)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape030 f g inputs siblings]
  rw [unoccupied f g 2 149628 (by decide),siblings 2 (by decide) 149628 (by decide)]
  rfl
#print axioms shape042
def input043 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash043.message
def value043 : State := JFp_SHADigest.output JGf_TX2_M1.Hash043.result
theorem cast043_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash043.B00.input).map Fin.val=JGf_TX2_M1.Hash043.B00.input := by rfl
#print axioms cast043_0
theorem tail043 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash043.tail).map Fin.val=JGf_TX2_M1.Hash043.tail := by rfl
#print axioms tail043
theorem numeric043 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash043.message).map Fin.val=JGf_TX2_M1.Hash043.message := by
  simp only [JGf_TX2_M1.Hash043.message,JGf_TX2_M1.Hash043.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast043_0,tail043]
#print axioms numeric043
theorem hash043 : JFp_SHADigest.digest input043=value043 := by
  unfold input043 JFp_SHADigest.digest
  rw [numeric043,JGf_TX2_M1.Hash043.checked]
  rfl
#print axioms hash043
theorem address043 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [53,114,132,46,186,166,92,88,104,211,173,253,87,181,205,236,11,203,144,188,40,230,240,23,98,232,115,106,226,28,201,184]) value031)=input043 := by rfl
#print axioms address043
def tree043 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [53,114,132,46,186,166,92,88,104,211,173,253,87,181,205,236,11,203,144,188,40,230,240,23,98,232,115,106,226,28,201,184])) tree031
theorem root043 : root JFp_SHADigest.digest tree043=value043 := by
  rw [tree043,root,root031]
  exact (congrArg JFp_SHADigest.digest address043).trans hash043
#print axioms root043
theorem shape043 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 166160=tree043 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 166160)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 166160 (by decide),siblings 2 (by decide) 166160 (by decide)]
  rw [shape031 f g inputs siblings]
  rfl
#print axioms shape043
def input044 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash044.message
def value044 : State := JFp_SHADigest.output JGf_TX2_M1.Hash044.result
theorem cast044_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash044.B00.input).map Fin.val=JGf_TX2_M1.Hash044.B00.input := by rfl
#print axioms cast044_0
theorem tail044 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash044.tail).map Fin.val=JGf_TX2_M1.Hash044.tail := by rfl
#print axioms tail044
theorem numeric044 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash044.message).map Fin.val=JGf_TX2_M1.Hash044.message := by
  simp only [JGf_TX2_M1.Hash044.message,JGf_TX2_M1.Hash044.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast044_0,tail044]
#print axioms numeric044
theorem hash044 : JFp_SHADigest.digest input044=value044 := by
  unfold input044 JFp_SHADigest.digest
  rw [numeric044,JGf_TX2_M1.Hash044.checked]
  rfl
#print axioms hash044
theorem address044 : BinMerkle32Path.nodeInput (children value032 (JGc_TX2_HashBytes.state [113,112,35,231,139,214,179,119,132,123,176,214,78,91,93,17,20,254,88,184,85,103,68,48,232,61,247,103,196,246,43,235]))=input044 := by rfl
#print axioms address044
def tree044 : Tree := .branch tree032 (.supplied (JGc_TX2_HashBytes.state [113,112,35,231,139,214,179,119,132,123,176,214,78,91,93,17,20,254,88,184,85,103,68,48,232,61,247,103,196,246,43,235]))
theorem root044 : root JFp_SHADigest.digest tree044=value044 := by
  rw [tree044,root,root032]
  exact (congrArg JFp_SHADigest.digest address044).trans hash044
#print axioms root044
theorem shape044 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 178080=tree044 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 178080)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape032 f g inputs siblings]
  rw [unoccupied f g 2 178084 (by decide),siblings 2 (by decide) 178084 (by decide)]
  rfl
#print axioms shape044
def input045 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash045.message
def value045 : State := JFp_SHADigest.output JGf_TX2_M1.Hash045.result
theorem cast045_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash045.B00.input).map Fin.val=JGf_TX2_M1.Hash045.B00.input := by rfl
#print axioms cast045_0
theorem tail045 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash045.tail).map Fin.val=JGf_TX2_M1.Hash045.tail := by rfl
#print axioms tail045
theorem numeric045 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash045.message).map Fin.val=JGf_TX2_M1.Hash045.message := by
  simp only [JGf_TX2_M1.Hash045.message,JGf_TX2_M1.Hash045.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast045_0,tail045]
#print axioms numeric045
theorem hash045 : JFp_SHADigest.digest input045=value045 := by
  unfold input045 JFp_SHADigest.digest
  rw [numeric045,JGf_TX2_M1.Hash045.checked]
  rfl
#print axioms hash045
theorem address045 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [129,72,67,82,242,126,71,182,192,27,62,249,25,188,16,252,234,20,43,168,77,243,60,144,123,206,201,85,74,108,95,91]) value033)=input045 := by rfl
#print axioms address045
def tree045 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [129,72,67,82,242,126,71,182,192,27,62,249,25,188,16,252,234,20,43,168,77,243,60,144,123,206,201,85,74,108,95,91])) tree033
theorem root045 : root JFp_SHADigest.digest tree045=value045 := by
  rw [tree045,root,root033]
  exact (congrArg JFp_SHADigest.digest address045).trans hash045
#print axioms root045
theorem shape045 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 179616=tree045 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 179616)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 179616 (by decide),siblings 2 (by decide) 179616 (by decide)]
  rw [shape033 f g inputs siblings]
  rfl
#print axioms shape045
def input046 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash046.message
def value046 : State := JFp_SHADigest.output JGh_TX2_M1.Hash046.result
theorem cast046_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash046.B00.input).map Fin.val=JGh_TX2_M1.Hash046.B00.input := by rfl
#print axioms cast046_0
theorem tail046 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash046.tail).map Fin.val=JGh_TX2_M1.Hash046.tail := by rfl
#print axioms tail046
theorem numeric046 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash046.message).map Fin.val=JGh_TX2_M1.Hash046.message := by
  simp only [JGh_TX2_M1.Hash046.message,JGh_TX2_M1.Hash046.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast046_0,tail046]
#print axioms numeric046
theorem hash046 : JFp_SHADigest.digest input046=value046 := by
  unfold input046 JFp_SHADigest.digest
  rw [numeric046,JGh_TX2_M1.Hash046.checked]
  rfl
#print axioms hash046
theorem address046 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [6,37,171,139,92,51,101,71,160,15,26,2,216,90,109,219,223,194,156,101,196,87,158,89,191,69,44,129,248,130,247,70]) value034)=input046 := by rfl
#print axioms address046
def tree046 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [6,37,171,139,92,51,101,71,160,15,26,2,216,90,109,219,223,194,156,101,196,87,158,89,191,69,44,129,248,130,247,70])) tree034
theorem root046 : root JFp_SHADigest.digest tree046=value046 := by
  rw [tree046,root,root034]
  exact (congrArg JFp_SHADigest.digest address046).trans hash046
#print axioms root046
theorem shape046 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 185632=tree046 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 185632)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 185632 (by decide),siblings 2 (by decide) 185632 (by decide)]
  rw [shape034 f g inputs siblings]
  rfl
#print axioms shape046
def input047 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash047.message
def value047 : State := JFp_SHADigest.output JGh_TX2_M1.Hash047.result
theorem cast047_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash047.B00.input).map Fin.val=JGh_TX2_M1.Hash047.B00.input := by rfl
#print axioms cast047_0
theorem tail047 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash047.tail).map Fin.val=JGh_TX2_M1.Hash047.tail := by rfl
#print axioms tail047
theorem numeric047 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash047.message).map Fin.val=JGh_TX2_M1.Hash047.message := by
  simp only [JGh_TX2_M1.Hash047.message,JGh_TX2_M1.Hash047.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast047_0,tail047]
#print axioms numeric047
theorem hash047 : JFp_SHADigest.digest input047=value047 := by
  unfold input047 JFp_SHADigest.digest
  rw [numeric047,JGh_TX2_M1.Hash047.checked]
  rfl
#print axioms hash047
theorem address047 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [68,157,45,113,195,182,5,150,228,230,64,164,162,241,47,246,114,48,101,22,44,185,35,111,36,40,34,61,67,79,45,201]) value035)=input047 := by rfl
#print axioms address047
def tree047 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [68,157,45,113,195,182,5,150,228,230,64,164,162,241,47,246,114,48,101,22,44,185,35,111,36,40,34,61,67,79,45,201])) tree035
theorem root047 : root JFp_SHADigest.digest tree047=value047 := by
  rw [tree047,root,root035]
  exact (congrArg JFp_SHADigest.digest address047).trans hash047
#print axioms root047
theorem shape047 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 218088=tree047 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 218088)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 218088 (by decide),siblings 2 (by decide) 218088 (by decide)]
  rw [shape035 f g inputs siblings]
  rfl
#print axioms shape047
end AspisR1.JGh_TX2_M1Roots
end
