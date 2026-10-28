import NDO_JGf_TX2_M0Level01
import NDO_JGf_TX2_M0W019
import NDO_JGf_TX2_M0W020
import NDO_JGf_TX2_M0W021
import NDO_JGf_TX2_M0W022
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGf_TX2_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input036 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash036.message
def value036 : State := JFp_SHADigest.output JGf_TX2_M0.Hash036.result
theorem cast036_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash036.B00.input).map Fin.val=JGf_TX2_M0.Hash036.B00.input := by rfl
#print axioms cast036_0
theorem tail036 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash036.tail).map Fin.val=JGf_TX2_M0.Hash036.tail := by rfl
#print axioms tail036
theorem numeric036 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash036.message).map Fin.val=JGf_TX2_M0.Hash036.message := by
  simp only [JGf_TX2_M0.Hash036.message,JGf_TX2_M0.Hash036.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast036_0,tail036]
#print axioms numeric036
theorem hash036 : JFp_SHADigest.digest input036=value036 := by
  unfold input036 JFp_SHADigest.digest
  rw [numeric036,JGf_TX2_M0.Hash036.checked]
  rfl
#print axioms hash036
theorem address036 : BinMerkle32Path.nodeInput (children value024 (JGc_TX2_HashBytes.state [218,241,71,167,112,184,166,159,90,38,254,127,148,227,188,18,72,222,135,94,140,205,13,74,63,49,112,59,163,239,80,108]))=input036 := by rfl
#print axioms address036
def tree036 : Tree := .branch tree024 (.supplied (JGc_TX2_HashBytes.state [218,241,71,167,112,184,166,159,90,38,254,127,148,227,188,18,72,222,135,94,140,205,13,74,63,49,112,59,163,239,80,108]))
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
def input037 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash037.message
def value037 : State := JFp_SHADigest.output JGf_TX2_M0.Hash037.result
theorem cast037_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash037.B00.input).map Fin.val=JGf_TX2_M0.Hash037.B00.input := by rfl
#print axioms cast037_0
theorem tail037 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash037.tail).map Fin.val=JGf_TX2_M0.Hash037.tail := by rfl
#print axioms tail037
theorem numeric037 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash037.message).map Fin.val=JGf_TX2_M0.Hash037.message := by
  simp only [JGf_TX2_M0.Hash037.message,JGf_TX2_M0.Hash037.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast037_0,tail037]
#print axioms numeric037
theorem hash037 : JFp_SHADigest.digest input037=value037 := by
  unfold input037 JFp_SHADigest.digest
  rw [numeric037,JGf_TX2_M0.Hash037.checked]
  rfl
#print axioms hash037
theorem address037 : BinMerkle32Path.nodeInput (children value025 (JGc_TX2_HashBytes.state [35,28,94,13,174,102,114,164,65,132,8,114,78,147,234,48,22,242,10,142,152,19,18,49,208,241,96,253,98,1,109,113]))=input037 := by rfl
#print axioms address037
def tree037 : Tree := .branch tree025 (.supplied (JGc_TX2_HashBytes.state [35,28,94,13,174,102,114,164,65,132,8,114,78,147,234,48,22,242,10,142,152,19,18,49,208,241,96,253,98,1,109,113]))
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
def input038 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash038.message
def value038 : State := JFp_SHADigest.output JGf_TX2_M0.Hash038.result
theorem cast038_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash038.B00.input).map Fin.val=JGf_TX2_M0.Hash038.B00.input := by rfl
#print axioms cast038_0
theorem tail038 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash038.tail).map Fin.val=JGf_TX2_M0.Hash038.tail := by rfl
#print axioms tail038
theorem numeric038 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash038.message).map Fin.val=JGf_TX2_M0.Hash038.message := by
  simp only [JGf_TX2_M0.Hash038.message,JGf_TX2_M0.Hash038.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast038_0,tail038]
#print axioms numeric038
theorem hash038 : JFp_SHADigest.digest input038=value038 := by
  unfold input038 JFp_SHADigest.digest
  rw [numeric038,JGf_TX2_M0.Hash038.checked]
  rfl
#print axioms hash038
theorem address038 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [123,25,254,56,232,254,156,156,34,39,220,61,186,229,1,73,35,32,233,198,199,163,114,114,70,88,235,224,222,81,177,123]) value026)=input038 := by rfl
#print axioms address038
def tree038 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [123,25,254,56,232,254,156,156,34,39,220,61,186,229,1,73,35,32,233,198,199,163,114,114,70,88,235,224,222,81,177,123])) tree026
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
def input039 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash039.message
def value039 : State := JFp_SHADigest.output JGf_TX2_M0.Hash039.result
theorem cast039_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash039.B00.input).map Fin.val=JGf_TX2_M0.Hash039.B00.input := by rfl
#print axioms cast039_0
theorem tail039 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash039.tail).map Fin.val=JGf_TX2_M0.Hash039.tail := by rfl
#print axioms tail039
theorem numeric039 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash039.message).map Fin.val=JGf_TX2_M0.Hash039.message := by
  simp only [JGf_TX2_M0.Hash039.message,JGf_TX2_M0.Hash039.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast039_0,tail039]
#print axioms numeric039
theorem hash039 : JFp_SHADigest.digest input039=value039 := by
  unfold input039 JFp_SHADigest.digest
  rw [numeric039,JGf_TX2_M0.Hash039.checked]
  rfl
#print axioms hash039
theorem address039 : BinMerkle32Path.nodeInput (children value027 (JGc_TX2_HashBytes.state [98,28,243,32,42,146,158,33,35,203,211,150,155,85,120,235,218,134,104,31,12,49,198,107,34,181,251,205,53,120,141,155]))=input039 := by rfl
#print axioms address039
def tree039 : Tree := .branch tree027 (.supplied (JGc_TX2_HashBytes.state [98,28,243,32,42,146,158,33,35,203,211,150,155,85,120,235,218,134,104,31,12,49,198,107,34,181,251,205,53,120,141,155]))
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
def input040 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash040.message
def value040 : State := JFp_SHADigest.output JGf_TX2_M0.Hash040.result
theorem cast040_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash040.B00.input).map Fin.val=JGf_TX2_M0.Hash040.B00.input := by rfl
#print axioms cast040_0
theorem tail040 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash040.tail).map Fin.val=JGf_TX2_M0.Hash040.tail := by rfl
#print axioms tail040
theorem numeric040 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash040.message).map Fin.val=JGf_TX2_M0.Hash040.message := by
  simp only [JGf_TX2_M0.Hash040.message,JGf_TX2_M0.Hash040.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast040_0,tail040]
#print axioms numeric040
theorem hash040 : JFp_SHADigest.digest input040=value040 := by
  unfold input040 JFp_SHADigest.digest
  rw [numeric040,JGf_TX2_M0.Hash040.checked]
  rfl
#print axioms hash040
theorem address040 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [91,184,231,32,192,241,228,66,226,123,52,241,125,153,190,95,249,96,122,192,39,201,254,73,242,2,77,89,77,132,113,174]) value028)=input040 := by rfl
#print axioms address040
def tree040 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [91,184,231,32,192,241,228,66,226,123,52,241,125,153,190,95,249,96,122,192,39,201,254,73,242,2,77,89,77,132,113,174])) tree028
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
def input041 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash041.message
def value041 : State := JFp_SHADigest.output JGf_TX2_M0.Hash041.result
theorem cast041_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash041.B00.input).map Fin.val=JGf_TX2_M0.Hash041.B00.input := by rfl
#print axioms cast041_0
theorem tail041 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash041.tail).map Fin.val=JGf_TX2_M0.Hash041.tail := by rfl
#print axioms tail041
theorem numeric041 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash041.message).map Fin.val=JGf_TX2_M0.Hash041.message := by
  simp only [JGf_TX2_M0.Hash041.message,JGf_TX2_M0.Hash041.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast041_0,tail041]
#print axioms numeric041
theorem hash041 : JFp_SHADigest.digest input041=value041 := by
  unfold input041 JFp_SHADigest.digest
  rw [numeric041,JGf_TX2_M0.Hash041.checked]
  rfl
#print axioms hash041
theorem address041 : BinMerkle32Path.nodeInput (children value029 (JGc_TX2_HashBytes.state [113,19,207,23,187,57,157,141,192,16,55,18,175,27,245,209,242,6,206,117,212,152,244,92,103,150,73,155,45,118,20,147]))=input041 := by rfl
#print axioms address041
def tree041 : Tree := .branch tree029 (.supplied (JGc_TX2_HashBytes.state [113,19,207,23,187,57,157,141,192,16,55,18,175,27,245,209,242,6,206,117,212,152,244,92,103,150,73,155,45,118,20,147]))
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
def input042 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash042.message
def value042 : State := JFp_SHADigest.output JGf_TX2_M0.Hash042.result
theorem cast042_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash042.B00.input).map Fin.val=JGf_TX2_M0.Hash042.B00.input := by rfl
#print axioms cast042_0
theorem tail042 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash042.tail).map Fin.val=JGf_TX2_M0.Hash042.tail := by rfl
#print axioms tail042
theorem numeric042 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash042.message).map Fin.val=JGf_TX2_M0.Hash042.message := by
  simp only [JGf_TX2_M0.Hash042.message,JGf_TX2_M0.Hash042.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast042_0,tail042]
#print axioms numeric042
theorem hash042 : JFp_SHADigest.digest input042=value042 := by
  unfold input042 JFp_SHADigest.digest
  rw [numeric042,JGf_TX2_M0.Hash042.checked]
  rfl
#print axioms hash042
theorem address042 : BinMerkle32Path.nodeInput (children value030 (JGc_TX2_HashBytes.state [106,92,61,225,225,124,106,145,184,75,252,83,44,17,78,28,64,239,34,232,109,221,76,65,131,68,75,180,189,56,128,39]))=input042 := by rfl
#print axioms address042
def tree042 : Tree := .branch tree030 (.supplied (JGc_TX2_HashBytes.state [106,92,61,225,225,124,106,145,184,75,252,83,44,17,78,28,64,239,34,232,109,221,76,65,131,68,75,180,189,56,128,39]))
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
def input043 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash043.message
def value043 : State := JFp_SHADigest.output JGf_TX2_M0.Hash043.result
theorem cast043_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash043.B00.input).map Fin.val=JGf_TX2_M0.Hash043.B00.input := by rfl
#print axioms cast043_0
theorem tail043 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash043.tail).map Fin.val=JGf_TX2_M0.Hash043.tail := by rfl
#print axioms tail043
theorem numeric043 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash043.message).map Fin.val=JGf_TX2_M0.Hash043.message := by
  simp only [JGf_TX2_M0.Hash043.message,JGf_TX2_M0.Hash043.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast043_0,tail043]
#print axioms numeric043
theorem hash043 : JFp_SHADigest.digest input043=value043 := by
  unfold input043 JFp_SHADigest.digest
  rw [numeric043,JGf_TX2_M0.Hash043.checked]
  rfl
#print axioms hash043
theorem address043 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [245,162,16,17,84,139,11,109,253,83,166,41,105,71,34,199,135,207,108,197,154,9,47,40,168,137,76,244,246,215,50,245]) value031)=input043 := by rfl
#print axioms address043
def tree043 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [245,162,16,17,84,139,11,109,253,83,166,41,105,71,34,199,135,207,108,197,154,9,47,40,168,137,76,244,246,215,50,245])) tree031
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
def input044 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash044.message
def value044 : State := JFp_SHADigest.output JGf_TX2_M0.Hash044.result
theorem cast044_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash044.B00.input).map Fin.val=JGf_TX2_M0.Hash044.B00.input := by rfl
#print axioms cast044_0
theorem tail044 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash044.tail).map Fin.val=JGf_TX2_M0.Hash044.tail := by rfl
#print axioms tail044
theorem numeric044 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash044.message).map Fin.val=JGf_TX2_M0.Hash044.message := by
  simp only [JGf_TX2_M0.Hash044.message,JGf_TX2_M0.Hash044.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast044_0,tail044]
#print axioms numeric044
theorem hash044 : JFp_SHADigest.digest input044=value044 := by
  unfold input044 JFp_SHADigest.digest
  rw [numeric044,JGf_TX2_M0.Hash044.checked]
  rfl
#print axioms hash044
theorem address044 : BinMerkle32Path.nodeInput (children value032 (JGc_TX2_HashBytes.state [126,116,91,219,142,133,90,40,89,117,50,252,160,190,170,101,178,197,82,124,103,50,182,123,133,194,91,142,245,125,91,60]))=input044 := by rfl
#print axioms address044
def tree044 : Tree := .branch tree032 (.supplied (JGc_TX2_HashBytes.state [126,116,91,219,142,133,90,40,89,117,50,252,160,190,170,101,178,197,82,124,103,50,182,123,133,194,91,142,245,125,91,60]))
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
def input045 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash045.message
def value045 : State := JFp_SHADigest.output JGf_TX2_M0.Hash045.result
theorem cast045_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash045.B00.input).map Fin.val=JGf_TX2_M0.Hash045.B00.input := by rfl
#print axioms cast045_0
theorem tail045 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash045.tail).map Fin.val=JGf_TX2_M0.Hash045.tail := by rfl
#print axioms tail045
theorem numeric045 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash045.message).map Fin.val=JGf_TX2_M0.Hash045.message := by
  simp only [JGf_TX2_M0.Hash045.message,JGf_TX2_M0.Hash045.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast045_0,tail045]
#print axioms numeric045
theorem hash045 : JFp_SHADigest.digest input045=value045 := by
  unfold input045 JFp_SHADigest.digest
  rw [numeric045,JGf_TX2_M0.Hash045.checked]
  rfl
#print axioms hash045
theorem address045 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [182,229,41,39,46,204,168,62,95,92,247,168,194,9,16,110,234,4,197,2,90,60,8,31,232,63,41,48,97,30,137,157]) value033)=input045 := by rfl
#print axioms address045
def tree045 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [182,229,41,39,46,204,168,62,95,92,247,168,194,9,16,110,234,4,197,2,90,60,8,31,232,63,41,48,97,30,137,157])) tree033
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
def input046 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash046.message
def value046 : State := JFp_SHADigest.output JGf_TX2_M0.Hash046.result
theorem cast046_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash046.B00.input).map Fin.val=JGf_TX2_M0.Hash046.B00.input := by rfl
#print axioms cast046_0
theorem tail046 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash046.tail).map Fin.val=JGf_TX2_M0.Hash046.tail := by rfl
#print axioms tail046
theorem numeric046 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash046.message).map Fin.val=JGf_TX2_M0.Hash046.message := by
  simp only [JGf_TX2_M0.Hash046.message,JGf_TX2_M0.Hash046.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast046_0,tail046]
#print axioms numeric046
theorem hash046 : JFp_SHADigest.digest input046=value046 := by
  unfold input046 JFp_SHADigest.digest
  rw [numeric046,JGf_TX2_M0.Hash046.checked]
  rfl
#print axioms hash046
theorem address046 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [2,247,162,206,126,146,165,190,108,5,251,239,19,221,0,181,37,250,224,170,160,183,195,67,94,129,163,84,98,80,52,84]) value034)=input046 := by rfl
#print axioms address046
def tree046 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [2,247,162,206,126,146,165,190,108,5,251,239,19,221,0,181,37,250,224,170,160,183,195,67,94,129,163,84,98,80,52,84])) tree034
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
def input047 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash047.message
def value047 : State := JFp_SHADigest.output JGf_TX2_M0.Hash047.result
theorem cast047_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash047.B00.input).map Fin.val=JGf_TX2_M0.Hash047.B00.input := by rfl
#print axioms cast047_0
theorem tail047 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash047.tail).map Fin.val=JGf_TX2_M0.Hash047.tail := by rfl
#print axioms tail047
theorem numeric047 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash047.message).map Fin.val=JGf_TX2_M0.Hash047.message := by
  simp only [JGf_TX2_M0.Hash047.message,JGf_TX2_M0.Hash047.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast047_0,tail047]
#print axioms numeric047
theorem hash047 : JFp_SHADigest.digest input047=value047 := by
  unfold input047 JFp_SHADigest.digest
  rw [numeric047,JGf_TX2_M0.Hash047.checked]
  rfl
#print axioms hash047
theorem address047 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [231,104,216,222,33,19,211,49,190,76,10,221,20,55,139,248,54,127,6,25,181,58,13,7,228,136,132,156,115,168,111,104]) value035)=input047 := by rfl
#print axioms address047
def tree047 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [231,104,216,222,33,19,211,49,190,76,10,221,20,55,139,248,54,127,6,25,181,58,13,7,228,136,132,156,115,168,111,104])) tree035
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
end AspisR1.JGf_TX2_M0Roots
end
