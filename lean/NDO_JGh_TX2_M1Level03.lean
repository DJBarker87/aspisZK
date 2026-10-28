import NDO_JGh_TX2_M1Level02
import NDO_JGh_TX2_M1W013
import NDO_JGh_TX2_M1W014
import NDO_JGh_TX2_M1W015
import NDO_JGh_TX2_M1W016
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input048 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash048.message
def value048 : State := JFp_SHADigest.output JGh_TX2_M1.Hash048.result
theorem cast048_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash048.B00.input).map Fin.val=JGh_TX2_M1.Hash048.B00.input := by rfl
#print axioms cast048_0
theorem tail048 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash048.tail).map Fin.val=JGh_TX2_M1.Hash048.tail := by rfl
#print axioms tail048
theorem numeric048 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash048.message).map Fin.val=JGh_TX2_M1.Hash048.message := by
  simp only [JGh_TX2_M1.Hash048.message,JGh_TX2_M1.Hash048.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast048_0,tail048]
#print axioms numeric048
theorem hash048 : JFp_SHADigest.digest input048=value048 := by
  unfold input048 JFp_SHADigest.digest
  rw [numeric048,JGh_TX2_M1.Hash048.checked]
  rfl
#print axioms hash048
theorem address048 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [95,112,58,71,93,88,125,240,170,137,227,56,101,123,134,113,255,6,225,244,251,198,92,231,174,141,56,10,11,165,123,139]) value036)=input048 := by rfl
#print axioms address048
def tree048 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [95,112,58,71,93,88,125,240,170,137,227,56,101,123,134,113,255,6,225,244,251,198,92,231,174,141,56,10,11,165,123,139])) tree036
theorem root048 : root JFp_SHADigest.digest tree048=value048 := by
  rw [tree048,root,root036]
  exact (congrArg JFp_SHADigest.digest address048).trans hash048
#print axioms root048
theorem shape048 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 14288=tree048 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 14288)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 14288 (by decide),siblings 3 (by decide) 14288 (by decide)]
  rw [shape036 f g inputs siblings]
  rfl
#print axioms shape048
def input049 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash049.message
def value049 : State := JFp_SHADigest.output JGh_TX2_M1.Hash049.result
theorem cast049_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash049.B00.input).map Fin.val=JGh_TX2_M1.Hash049.B00.input := by rfl
#print axioms cast049_0
theorem tail049 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash049.tail).map Fin.val=JGh_TX2_M1.Hash049.tail := by rfl
#print axioms tail049
theorem numeric049 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash049.message).map Fin.val=JGh_TX2_M1.Hash049.message := by
  simp only [JGh_TX2_M1.Hash049.message,JGh_TX2_M1.Hash049.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast049_0,tail049]
#print axioms numeric049
theorem hash049 : JFp_SHADigest.digest input049=value049 := by
  unfold input049 JFp_SHADigest.digest
  rw [numeric049,JGh_TX2_M1.Hash049.checked]
  rfl
#print axioms hash049
theorem address049 : BinMerkle32Path.nodeInput (children value037 (JGc_TX2_HashBytes.state [58,4,247,132,130,229,131,24,92,198,44,177,234,99,135,67,26,244,113,252,208,248,214,148,174,205,214,74,188,170,27,195]))=input049 := by rfl
#print axioms address049
def tree049 : Tree := .branch tree037 (.supplied (JGc_TX2_HashBytes.state [58,4,247,132,130,229,131,24,92,198,44,177,234,99,135,67,26,244,113,252,208,248,214,148,174,205,214,74,188,170,27,195]))
theorem root049 : root JFp_SHADigest.digest tree049=value049 := by
  rw [tree049,root,root037]
  exact (congrArg JFp_SHADigest.digest address049).trans hash049
#print axioms root049
theorem shape049 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 21248=tree049 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 21248)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape037 f g inputs siblings]
  rw [unoccupied f g 3 21256 (by decide),siblings 3 (by decide) 21256 (by decide)]
  rfl
#print axioms shape049
def input050 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash050.message
def value050 : State := JFp_SHADigest.output JGh_TX2_M1.Hash050.result
theorem cast050_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash050.B00.input).map Fin.val=JGh_TX2_M1.Hash050.B00.input := by rfl
#print axioms cast050_0
theorem tail050 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash050.tail).map Fin.val=JGh_TX2_M1.Hash050.tail := by rfl
#print axioms tail050
theorem numeric050 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash050.message).map Fin.val=JGh_TX2_M1.Hash050.message := by
  simp only [JGh_TX2_M1.Hash050.message,JGh_TX2_M1.Hash050.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast050_0,tail050]
#print axioms numeric050
theorem hash050 : JFp_SHADigest.digest input050=value050 := by
  unfold input050 JFp_SHADigest.digest
  rw [numeric050,JGh_TX2_M1.Hash050.checked]
  rfl
#print axioms hash050
theorem address050 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [0,120,208,60,235,45,37,35,176,63,191,234,3,10,87,94,213,75,190,23,105,76,185,25,136,55,233,134,186,180,205,200]) value038)=input050 := by rfl
#print axioms address050
def tree050 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [0,120,208,60,235,45,37,35,176,63,191,234,3,10,87,94,213,75,190,23,105,76,185,25,136,55,233,134,186,180,205,200])) tree038
theorem root050 : root JFp_SHADigest.digest tree050=value050 := by
  rw [tree050,root,root038]
  exact (congrArg JFp_SHADigest.digest address050).trans hash050
#print axioms root050
theorem shape050 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 42144=tree050 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 42144)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 42144 (by decide),siblings 3 (by decide) 42144 (by decide)]
  rw [shape038 f g inputs siblings]
  rfl
#print axioms shape050
def input051 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash051.message
def value051 : State := JFp_SHADigest.output JGh_TX2_M1.Hash051.result
theorem cast051_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash051.B00.input).map Fin.val=JGh_TX2_M1.Hash051.B00.input := by rfl
#print axioms cast051_0
theorem tail051 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash051.tail).map Fin.val=JGh_TX2_M1.Hash051.tail := by rfl
#print axioms tail051
theorem numeric051 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash051.message).map Fin.val=JGh_TX2_M1.Hash051.message := by
  simp only [JGh_TX2_M1.Hash051.message,JGh_TX2_M1.Hash051.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast051_0,tail051]
#print axioms numeric051
theorem hash051 : JFp_SHADigest.digest input051=value051 := by
  unfold input051 JFp_SHADigest.digest
  rw [numeric051,JGh_TX2_M1.Hash051.checked]
  rfl
#print axioms hash051
theorem address051 : BinMerkle32Path.nodeInput (children value039 (JGc_TX2_HashBytes.state [235,146,137,239,114,9,74,180,253,134,12,59,180,148,144,129,96,30,255,141,127,159,144,59,253,107,189,65,75,154,28,189]))=input051 := by rfl
#print axioms address051
def tree051 : Tree := .branch tree039 (.supplied (JGc_TX2_HashBytes.state [235,146,137,239,114,9,74,180,253,134,12,59,180,148,144,129,96,30,255,141,127,159,144,59,253,107,189,65,75,154,28,189]))
theorem root051 : root JFp_SHADigest.digest tree051=value051 := by
  rw [tree051,root,root039]
  exact (congrArg JFp_SHADigest.digest address051).trans hash051
#print axioms root051
theorem shape051 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 55376=tree051 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 55376)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape039 f g inputs siblings]
  rw [unoccupied f g 3 55384 (by decide),siblings 3 (by decide) 55384 (by decide)]
  rfl
#print axioms shape051
def input052 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash052.message
def value052 : State := JFp_SHADigest.output JGh_TX2_M1.Hash052.result
theorem cast052_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash052.B00.input).map Fin.val=JGh_TX2_M1.Hash052.B00.input := by rfl
#print axioms cast052_0
theorem tail052 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash052.tail).map Fin.val=JGh_TX2_M1.Hash052.tail := by rfl
#print axioms tail052
theorem numeric052 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash052.message).map Fin.val=JGh_TX2_M1.Hash052.message := by
  simp only [JGh_TX2_M1.Hash052.message,JGh_TX2_M1.Hash052.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast052_0,tail052]
#print axioms numeric052
theorem hash052 : JFp_SHADigest.digest input052=value052 := by
  unfold input052 JFp_SHADigest.digest
  rw [numeric052,JGh_TX2_M1.Hash052.checked]
  rfl
#print axioms hash052
theorem address052 : BinMerkle32Path.nodeInput (children value040 (JGc_TX2_HashBytes.state [169,111,69,169,26,211,162,115,15,217,201,74,82,62,66,178,97,193,204,151,148,29,204,99,127,25,12,104,233,192,4,89]))=input052 := by rfl
#print axioms address052
def tree052 : Tree := .branch tree040 (.supplied (JGc_TX2_HashBytes.state [169,111,69,169,26,211,162,115,15,217,201,74,82,62,66,178,97,193,204,151,148,29,204,99,127,25,12,104,233,192,4,89]))
theorem root052 : root JFp_SHADigest.digest tree052=value052 := by
  rw [tree052,root,root040]
  exact (congrArg JFp_SHADigest.digest address052).trans hash052
#print axioms root052
theorem shape052 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 63856=tree052 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 63856)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape040 f g inputs siblings]
  rw [unoccupied f g 3 63864 (by decide),siblings 3 (by decide) 63864 (by decide)]
  rfl
#print axioms shape052
def input053 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash053.message
def value053 : State := JFp_SHADigest.output JGh_TX2_M1.Hash053.result
theorem cast053_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash053.B00.input).map Fin.val=JGh_TX2_M1.Hash053.B00.input := by rfl
#print axioms cast053_0
theorem tail053 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash053.tail).map Fin.val=JGh_TX2_M1.Hash053.tail := by rfl
#print axioms tail053
theorem numeric053 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash053.message).map Fin.val=JGh_TX2_M1.Hash053.message := by
  simp only [JGh_TX2_M1.Hash053.message,JGh_TX2_M1.Hash053.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast053_0,tail053]
#print axioms numeric053
theorem hash053 : JFp_SHADigest.digest input053=value053 := by
  unfold input053 JFp_SHADigest.digest
  rw [numeric053,JGh_TX2_M1.Hash053.checked]
  rfl
#print axioms hash053
theorem address053 : BinMerkle32Path.nodeInput (children value041 (JGc_TX2_HashBytes.state [29,185,194,216,179,1,247,11,172,171,19,55,212,131,32,115,68,44,21,12,219,69,52,197,56,96,77,242,92,83,170,197]))=input053 := by rfl
#print axioms address053
def tree053 : Tree := .branch tree041 (.supplied (JGc_TX2_HashBytes.state [29,185,194,216,179,1,247,11,172,171,19,55,212,131,32,115,68,44,21,12,219,69,52,197,56,96,77,242,92,83,170,197]))
theorem root053 : root JFp_SHADigest.digest tree053=value053 := by
  rw [tree053,root,root041]
  exact (congrArg JFp_SHADigest.digest address053).trans hash053
#print axioms root053
theorem shape053 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 132352=tree053 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 132352)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape041 f g inputs siblings]
  rw [unoccupied f g 3 132360 (by decide),siblings 3 (by decide) 132360 (by decide)]
  rfl
#print axioms shape053
def input054 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash054.message
def value054 : State := JFp_SHADigest.output JGh_TX2_M1.Hash054.result
theorem cast054_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash054.B00.input).map Fin.val=JGh_TX2_M1.Hash054.B00.input := by rfl
#print axioms cast054_0
theorem tail054 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash054.tail).map Fin.val=JGh_TX2_M1.Hash054.tail := by rfl
#print axioms tail054
theorem numeric054 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash054.message).map Fin.val=JGh_TX2_M1.Hash054.message := by
  simp only [JGh_TX2_M1.Hash054.message,JGh_TX2_M1.Hash054.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast054_0,tail054]
#print axioms numeric054
theorem hash054 : JFp_SHADigest.digest input054=value054 := by
  unfold input054 JFp_SHADigest.digest
  rw [numeric054,JGh_TX2_M1.Hash054.checked]
  rfl
#print axioms hash054
theorem address054 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [114,13,219,219,217,41,30,52,44,8,66,231,56,144,53,239,114,224,242,236,187,253,218,88,104,60,23,190,61,21,185,131]) value042)=input054 := by rfl
#print axioms address054
def tree054 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [114,13,219,219,217,41,30,52,44,8,66,231,56,144,53,239,114,224,242,236,187,253,218,88,104,60,23,190,61,21,185,131])) tree042
theorem root054 : root JFp_SHADigest.digest tree054=value054 := by
  rw [tree054,root,root042]
  exact (congrArg JFp_SHADigest.digest address054).trans hash054
#print axioms root054
theorem shape054 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 149616=tree054 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 149616)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 149616 (by decide),siblings 3 (by decide) 149616 (by decide)]
  rw [shape042 f g inputs siblings]
  rfl
#print axioms shape054
def input055 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash055.message
def value055 : State := JFp_SHADigest.output JGh_TX2_M1.Hash055.result
theorem cast055_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash055.B00.input).map Fin.val=JGh_TX2_M1.Hash055.B00.input := by rfl
#print axioms cast055_0
theorem tail055 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash055.tail).map Fin.val=JGh_TX2_M1.Hash055.tail := by rfl
#print axioms tail055
theorem numeric055 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash055.message).map Fin.val=JGh_TX2_M1.Hash055.message := by
  simp only [JGh_TX2_M1.Hash055.message,JGh_TX2_M1.Hash055.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast055_0,tail055]
#print axioms numeric055
theorem hash055 : JFp_SHADigest.digest input055=value055 := by
  unfold input055 JFp_SHADigest.digest
  rw [numeric055,JGh_TX2_M1.Hash055.checked]
  rfl
#print axioms hash055
theorem address055 : BinMerkle32Path.nodeInput (children value043 (JGc_TX2_HashBytes.state [240,122,191,34,114,30,58,112,147,135,65,101,141,66,107,30,194,52,193,28,24,107,197,207,126,13,95,174,16,162,166,215]))=input055 := by rfl
#print axioms address055
def tree055 : Tree := .branch tree043 (.supplied (JGc_TX2_HashBytes.state [240,122,191,34,114,30,58,112,147,135,65,101,141,66,107,30,194,52,193,28,24,107,197,207,126,13,95,174,16,162,166,215]))
theorem root055 : root JFp_SHADigest.digest tree055=value055 := by
  rw [tree055,root,root043]
  exact (congrArg JFp_SHADigest.digest address055).trans hash055
#print axioms root055
theorem shape055 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 166160=tree055 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 166160)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape043 f g inputs siblings]
  rw [unoccupied f g 3 166168 (by decide),siblings 3 (by decide) 166168 (by decide)]
  rfl
#print axioms shape055
def input056 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash056.message
def value056 : State := JFp_SHADigest.output JGh_TX2_M1.Hash056.result
theorem cast056_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash056.B00.input).map Fin.val=JGh_TX2_M1.Hash056.B00.input := by rfl
#print axioms cast056_0
theorem tail056 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash056.tail).map Fin.val=JGh_TX2_M1.Hash056.tail := by rfl
#print axioms tail056
theorem numeric056 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash056.message).map Fin.val=JGh_TX2_M1.Hash056.message := by
  simp only [JGh_TX2_M1.Hash056.message,JGh_TX2_M1.Hash056.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast056_0,tail056]
#print axioms numeric056
theorem hash056 : JFp_SHADigest.digest input056=value056 := by
  unfold input056 JFp_SHADigest.digest
  rw [numeric056,JGh_TX2_M1.Hash056.checked]
  rfl
#print axioms hash056
theorem address056 : BinMerkle32Path.nodeInput (children value044 (JGc_TX2_HashBytes.state [110,199,41,76,80,253,154,105,34,251,142,152,94,165,80,126,112,246,197,172,144,227,31,251,4,217,88,219,23,237,201,160]))=input056 := by rfl
#print axioms address056
def tree056 : Tree := .branch tree044 (.supplied (JGc_TX2_HashBytes.state [110,199,41,76,80,253,154,105,34,251,142,152,94,165,80,126,112,246,197,172,144,227,31,251,4,217,88,219,23,237,201,160]))
theorem root056 : root JFp_SHADigest.digest tree056=value056 := by
  rw [tree056,root,root044]
  exact (congrArg JFp_SHADigest.digest address056).trans hash056
#print axioms root056
theorem shape056 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 178080=tree056 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 178080)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape044 f g inputs siblings]
  rw [unoccupied f g 3 178088 (by decide),siblings 3 (by decide) 178088 (by decide)]
  rfl
#print axioms shape056
def input057 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash057.message
def value057 : State := JFp_SHADigest.output JGh_TX2_M1.Hash057.result
theorem cast057_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash057.B00.input).map Fin.val=JGh_TX2_M1.Hash057.B00.input := by rfl
#print axioms cast057_0
theorem tail057 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash057.tail).map Fin.val=JGh_TX2_M1.Hash057.tail := by rfl
#print axioms tail057
theorem numeric057 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash057.message).map Fin.val=JGh_TX2_M1.Hash057.message := by
  simp only [JGh_TX2_M1.Hash057.message,JGh_TX2_M1.Hash057.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast057_0,tail057]
#print axioms numeric057
theorem hash057 : JFp_SHADigest.digest input057=value057 := by
  unfold input057 JFp_SHADigest.digest
  rw [numeric057,JGh_TX2_M1.Hash057.checked]
  rfl
#print axioms hash057
theorem address057 : BinMerkle32Path.nodeInput (children value045 (JGc_TX2_HashBytes.state [247,163,118,0,246,147,113,68,130,176,157,112,153,88,113,153,219,157,212,173,2,86,74,103,252,248,50,69,161,51,86,188]))=input057 := by rfl
#print axioms address057
def tree057 : Tree := .branch tree045 (.supplied (JGc_TX2_HashBytes.state [247,163,118,0,246,147,113,68,130,176,157,112,153,88,113,153,219,157,212,173,2,86,74,103,252,248,50,69,161,51,86,188]))
theorem root057 : root JFp_SHADigest.digest tree057=value057 := by
  rw [tree057,root,root045]
  exact (congrArg JFp_SHADigest.digest address057).trans hash057
#print axioms root057
theorem shape057 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 179616=tree057 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 179616)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape045 f g inputs siblings]
  rw [unoccupied f g 3 179624 (by decide),siblings 3 (by decide) 179624 (by decide)]
  rfl
#print axioms shape057
def input058 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash058.message
def value058 : State := JFp_SHADigest.output JGh_TX2_M1.Hash058.result
theorem cast058_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash058.B00.input).map Fin.val=JGh_TX2_M1.Hash058.B00.input := by rfl
#print axioms cast058_0
theorem tail058 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash058.tail).map Fin.val=JGh_TX2_M1.Hash058.tail := by rfl
#print axioms tail058
theorem numeric058 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash058.message).map Fin.val=JGh_TX2_M1.Hash058.message := by
  simp only [JGh_TX2_M1.Hash058.message,JGh_TX2_M1.Hash058.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast058_0,tail058]
#print axioms numeric058
theorem hash058 : JFp_SHADigest.digest input058=value058 := by
  unfold input058 JFp_SHADigest.digest
  rw [numeric058,JGh_TX2_M1.Hash058.checked]
  rfl
#print axioms hash058
theorem address058 : BinMerkle32Path.nodeInput (children value046 (JGc_TX2_HashBytes.state [52,211,196,240,9,89,152,243,158,210,224,156,42,153,78,220,211,106,118,137,235,6,220,144,243,156,199,95,200,95,194,93]))=input058 := by rfl
#print axioms address058
def tree058 : Tree := .branch tree046 (.supplied (JGc_TX2_HashBytes.state [52,211,196,240,9,89,152,243,158,210,224,156,42,153,78,220,211,106,118,137,235,6,220,144,243,156,199,95,200,95,194,93]))
theorem root058 : root JFp_SHADigest.digest tree058=value058 := by
  rw [tree058,root,root046]
  exact (congrArg JFp_SHADigest.digest address058).trans hash058
#print axioms root058
theorem shape058 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 185632=tree058 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 185632)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape046 f g inputs siblings]
  rw [unoccupied f g 3 185640 (by decide),siblings 3 (by decide) 185640 (by decide)]
  rfl
#print axioms shape058
def input059 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash059.message
def value059 : State := JFp_SHADigest.output JGh_TX2_M1.Hash059.result
theorem cast059_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash059.B00.input).map Fin.val=JGh_TX2_M1.Hash059.B00.input := by rfl
#print axioms cast059_0
theorem tail059 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash059.tail).map Fin.val=JGh_TX2_M1.Hash059.tail := by rfl
#print axioms tail059
theorem numeric059 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash059.message).map Fin.val=JGh_TX2_M1.Hash059.message := by
  simp only [JGh_TX2_M1.Hash059.message,JGh_TX2_M1.Hash059.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast059_0,tail059]
#print axioms numeric059
theorem hash059 : JFp_SHADigest.digest input059=value059 := by
  unfold input059 JFp_SHADigest.digest
  rw [numeric059,JGh_TX2_M1.Hash059.checked]
  rfl
#print axioms hash059
theorem address059 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [16,42,190,16,201,18,111,225,89,177,137,139,232,23,237,29,155,118,42,57,203,192,229,217,192,251,116,91,3,194,172,187]) value047)=input059 := by rfl
#print axioms address059
def tree059 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [16,42,190,16,201,18,111,225,89,177,137,139,232,23,237,29,155,118,42,57,203,192,229,217,192,251,116,91,3,194,172,187])) tree047
theorem root059 : root JFp_SHADigest.digest tree059=value059 := by
  rw [tree059,root,root047]
  exact (congrArg JFp_SHADigest.digest address059).trans hash059
#print axioms root059
theorem shape059 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 218080=tree059 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 218080)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 218080 (by decide),siblings 3 (by decide) 218080 (by decide)]
  rw [shape047 f g inputs siblings]
  rfl
#print axioms shape059
end AspisR1.JGh_TX2_M1Roots
end
