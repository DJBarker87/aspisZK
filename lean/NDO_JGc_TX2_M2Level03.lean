import NDO_JGc_TX2_M2Level02
import NDO_JGc_TX2_M2H048
import NDO_JGc_TX2_M2H052
import NDO_JGc_TX2_M2H056
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input048 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash048.message
def value048 : State := JFp_SHADigest.output JGc_TX2_M2.Hash048.result
theorem cast048_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash048.B00.input).map Fin.val=JGc_TX2_M2.Hash048.B00.input := by rfl
#print axioms cast048_0
theorem tail048 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash048.tail).map Fin.val=JGc_TX2_M2.Hash048.tail := by rfl
#print axioms tail048
theorem numeric048 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash048.message).map Fin.val=JGc_TX2_M2.Hash048.message := by
  simp only [JGc_TX2_M2.Hash048.message,JGc_TX2_M2.Hash048.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast048_0,tail048]
#print axioms numeric048
theorem hash048 : JFp_SHADigest.digest input048=value048 := by
  unfold input048 JFp_SHADigest.digest
  rw [numeric048,JGc_TX2_M2.Hash048.checked]
  rfl
#print axioms hash048
theorem address048 : BinMerkle32Path.nodeInput (children value036 (JGc_TX2_HashBytes.state [153,18,190,77,145,143,202,56,13,238,158,20,241,137,194,105,241,140,40,56,220,162,192,164,222,205,183,83,148,187,18,197]))=input048 := by rfl
#print axioms address048
def tree048 : Tree := .branch tree036 (.supplied (JGc_TX2_HashBytes.state [153,18,190,77,145,143,202,56,13,238,158,20,241,137,194,105,241,140,40,56,220,162,192,164,222,205,183,83,148,187,18,197]))
theorem root048 : root JFp_SHADigest.digest tree048=value048 := by
  rw [tree048,root,root036]
  exact (congrArg JFp_SHADigest.digest address048).trans hash048
#print axioms root048
theorem shape048 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 3568=tree048 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 3568)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape036 f g inputs siblings]
  rw [unoccupied f g 3 3576 (by decide),siblings 3 (by decide) 3576 (by decide)]
  rfl
#print axioms shape048
def input049 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash049.message
def value049 : State := JFp_SHADigest.output JGc_TX2_M2.Hash049.result
theorem cast049_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash049.B00.input).map Fin.val=JGc_TX2_M2.Hash049.B00.input := by rfl
#print axioms cast049_0
theorem tail049 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash049.tail).map Fin.val=JGc_TX2_M2.Hash049.tail := by rfl
#print axioms tail049
theorem numeric049 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash049.message).map Fin.val=JGc_TX2_M2.Hash049.message := by
  simp only [JGc_TX2_M2.Hash049.message,JGc_TX2_M2.Hash049.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast049_0,tail049]
#print axioms numeric049
theorem hash049 : JFp_SHADigest.digest input049=value049 := by
  unfold input049 JFp_SHADigest.digest
  rw [numeric049,JGc_TX2_M2.Hash049.checked]
  rfl
#print axioms hash049
theorem address049 : BinMerkle32Path.nodeInput (children value037 (JGc_TX2_HashBytes.state [213,245,8,247,231,181,35,252,50,178,5,228,156,194,151,152,184,81,92,203,37,205,32,36,251,28,0,197,252,230,207,24]))=input049 := by rfl
#print axioms address049
def tree049 : Tree := .branch tree037 (.supplied (JGc_TX2_HashBytes.state [213,245,8,247,231,181,35,252,50,178,5,228,156,194,151,152,184,81,92,203,37,205,32,36,251,28,0,197,252,230,207,24]))
theorem root049 : root JFp_SHADigest.digest tree049=value049 := by
  rw [tree049,root,root037]
  exact (congrArg JFp_SHADigest.digest address049).trans hash049
#print axioms root049
theorem shape049 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 5312=tree049 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 5312)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape037 f g inputs siblings]
  rw [unoccupied f g 3 5320 (by decide),siblings 3 (by decide) 5320 (by decide)]
  rfl
#print axioms shape049
def input050 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash050.message
def value050 : State := JFp_SHADigest.output JGc_TX2_M2.Hash050.result
theorem cast050_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash050.B00.input).map Fin.val=JGc_TX2_M2.Hash050.B00.input := by rfl
#print axioms cast050_0
theorem tail050 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash050.tail).map Fin.val=JGc_TX2_M2.Hash050.tail := by rfl
#print axioms tail050
theorem numeric050 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash050.message).map Fin.val=JGc_TX2_M2.Hash050.message := by
  simp only [JGc_TX2_M2.Hash050.message,JGc_TX2_M2.Hash050.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast050_0,tail050]
#print axioms numeric050
theorem hash050 : JFp_SHADigest.digest input050=value050 := by
  unfold input050 JFp_SHADigest.digest
  rw [numeric050,JGc_TX2_M2.Hash050.checked]
  rfl
#print axioms hash050
theorem address050 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [4,130,79,6,75,2,137,40,130,222,69,104,104,150,19,31,98,91,103,192,227,74,251,60,251,236,235,160,128,241,114,59]) value038)=input050 := by rfl
#print axioms address050
def tree050 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [4,130,79,6,75,2,137,40,130,222,69,104,104,150,19,31,98,91,103,192,227,74,251,60,251,236,235,160,128,241,114,59])) tree038
theorem root050 : root JFp_SHADigest.digest tree050=value050 := by
  rw [tree050,root,root038]
  exact (congrArg JFp_SHADigest.digest address050).trans hash050
#print axioms root050
theorem shape050 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 10528=tree050 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 10528)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 10528 (by decide),siblings 3 (by decide) 10528 (by decide)]
  rw [shape038 f g inputs siblings]
  rfl
#print axioms shape050
def input051 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash051.message
def value051 : State := JFp_SHADigest.output JGc_TX2_M2.Hash051.result
theorem cast051_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash051.B00.input).map Fin.val=JGc_TX2_M2.Hash051.B00.input := by rfl
#print axioms cast051_0
theorem tail051 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash051.tail).map Fin.val=JGc_TX2_M2.Hash051.tail := by rfl
#print axioms tail051
theorem numeric051 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash051.message).map Fin.val=JGc_TX2_M2.Hash051.message := by
  simp only [JGc_TX2_M2.Hash051.message,JGc_TX2_M2.Hash051.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast051_0,tail051]
#print axioms numeric051
theorem hash051 : JFp_SHADigest.digest input051=value051 := by
  unfold input051 JFp_SHADigest.digest
  rw [numeric051,JGc_TX2_M2.Hash051.checked]
  rfl
#print axioms hash051
theorem address051 : BinMerkle32Path.nodeInput (children value039 (JGc_TX2_HashBytes.state [21,228,223,46,28,6,250,15,214,233,213,168,75,149,127,85,38,9,121,138,234,89,250,142,43,123,162,42,51,14,20,39]))=input051 := by rfl
#print axioms address051
def tree051 : Tree := .branch tree039 (.supplied (JGc_TX2_HashBytes.state [21,228,223,46,28,6,250,15,214,233,213,168,75,149,127,85,38,9,121,138,234,89,250,142,43,123,162,42,51,14,20,39]))
theorem root051 : root JFp_SHADigest.digest tree051=value051 := by
  rw [tree051,root,root039]
  exact (congrArg JFp_SHADigest.digest address051).trans hash051
#print axioms root051
theorem shape051 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 13840=tree051 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 13840)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape039 f g inputs siblings]
  rw [unoccupied f g 3 13848 (by decide),siblings 3 (by decide) 13848 (by decide)]
  rfl
#print axioms shape051
def input052 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash052.message
def value052 : State := JFp_SHADigest.output JGc_TX2_M2.Hash052.result
theorem cast052_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash052.B00.input).map Fin.val=JGc_TX2_M2.Hash052.B00.input := by rfl
#print axioms cast052_0
theorem tail052 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash052.tail).map Fin.val=JGc_TX2_M2.Hash052.tail := by rfl
#print axioms tail052
theorem numeric052 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash052.message).map Fin.val=JGc_TX2_M2.Hash052.message := by
  simp only [JGc_TX2_M2.Hash052.message,JGc_TX2_M2.Hash052.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast052_0,tail052]
#print axioms numeric052
theorem hash052 : JFp_SHADigest.digest input052=value052 := by
  unfold input052 JFp_SHADigest.digest
  rw [numeric052,JGc_TX2_M2.Hash052.checked]
  rfl
#print axioms hash052
theorem address052 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [69,78,117,110,144,181,202,132,1,73,226,239,28,196,199,223,6,220,58,110,201,63,202,78,223,199,143,21,51,219,63,220]) value040)=input052 := by rfl
#print axioms address052
def tree052 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [69,78,117,110,144,181,202,132,1,73,226,239,28,196,199,223,6,220,58,110,201,63,202,78,223,199,143,21,51,219,63,220])) tree040
theorem root052 : root JFp_SHADigest.digest tree052=value052 := by
  rw [tree052,root,root040]
  exact (congrArg JFp_SHADigest.digest address052).trans hash052
#print axioms root052
theorem shape052 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 15952=tree052 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 15952)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 15952 (by decide),siblings 3 (by decide) 15952 (by decide)]
  rw [shape040 f g inputs siblings]
  rfl
#print axioms shape052
def input053 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash053.message
def value053 : State := JFp_SHADigest.output JGc_TX2_M2.Hash053.result
theorem cast053_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash053.B00.input).map Fin.val=JGc_TX2_M2.Hash053.B00.input := by rfl
#print axioms cast053_0
theorem tail053 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash053.tail).map Fin.val=JGc_TX2_M2.Hash053.tail := by rfl
#print axioms tail053
theorem numeric053 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash053.message).map Fin.val=JGc_TX2_M2.Hash053.message := by
  simp only [JGc_TX2_M2.Hash053.message,JGc_TX2_M2.Hash053.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast053_0,tail053]
#print axioms numeric053
theorem hash053 : JFp_SHADigest.digest input053=value053 := by
  unfold input053 JFp_SHADigest.digest
  rw [numeric053,JGc_TX2_M2.Hash053.checked]
  rfl
#print axioms hash053
theorem address053 : BinMerkle32Path.nodeInput (children value041 (JGc_TX2_HashBytes.state [96,222,149,37,25,233,180,225,215,59,149,95,73,25,105,38,197,222,188,231,173,43,103,26,202,162,145,55,216,18,102,190]))=input053 := by rfl
#print axioms address053
def tree053 : Tree := .branch tree041 (.supplied (JGc_TX2_HashBytes.state [96,222,149,37,25,233,180,225,215,59,149,95,73,25,105,38,197,222,188,231,173,43,103,26,202,162,145,55,216,18,102,190]))
theorem root053 : root JFp_SHADigest.digest tree053=value053 := by
  rw [tree053,root,root041]
  exact (congrArg JFp_SHADigest.digest address053).trans hash053
#print axioms root053
theorem shape053 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 33088=tree053 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 33088)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape041 f g inputs siblings]
  rw [unoccupied f g 3 33096 (by decide),siblings 3 (by decide) 33096 (by decide)]
  rfl
#print axioms shape053
def input054 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash054.message
def value054 : State := JFp_SHADigest.output JGc_TX2_M2.Hash054.result
theorem cast054_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash054.B00.input).map Fin.val=JGc_TX2_M2.Hash054.B00.input := by rfl
#print axioms cast054_0
theorem tail054 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash054.tail).map Fin.val=JGc_TX2_M2.Hash054.tail := by rfl
#print axioms tail054
theorem numeric054 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash054.message).map Fin.val=JGc_TX2_M2.Hash054.message := by
  simp only [JGc_TX2_M2.Hash054.message,JGc_TX2_M2.Hash054.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast054_0,tail054]
#print axioms numeric054
theorem hash054 : JFp_SHADigest.digest input054=value054 := by
  unfold input054 JFp_SHADigest.digest
  rw [numeric054,JGc_TX2_M2.Hash054.checked]
  rfl
#print axioms hash054
theorem address054 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [182,31,194,5,179,183,206,112,193,70,98,172,225,80,183,61,105,36,25,46,133,113,99,55,179,24,117,111,15,225,210,191]) value042)=input054 := by rfl
#print axioms address054
def tree054 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [182,31,194,5,179,183,206,112,193,70,98,172,225,80,183,61,105,36,25,46,133,113,99,55,179,24,117,111,15,225,210,191])) tree042
theorem root054 : root JFp_SHADigest.digest tree054=value054 := by
  rw [tree054,root,root042]
  exact (congrArg JFp_SHADigest.digest address054).trans hash054
#print axioms root054
theorem shape054 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 37392=tree054 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 37392)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 37392 (by decide),siblings 3 (by decide) 37392 (by decide)]
  rw [shape042 f g inputs siblings]
  rfl
#print axioms shape054
def input055 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash055.message
def value055 : State := JFp_SHADigest.output JGc_TX2_M2.Hash055.result
theorem cast055_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash055.B00.input).map Fin.val=JGc_TX2_M2.Hash055.B00.input := by rfl
#print axioms cast055_0
theorem tail055 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash055.tail).map Fin.val=JGc_TX2_M2.Hash055.tail := by rfl
#print axioms tail055
theorem numeric055 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash055.message).map Fin.val=JGc_TX2_M2.Hash055.message := by
  simp only [JGc_TX2_M2.Hash055.message,JGc_TX2_M2.Hash055.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast055_0,tail055]
#print axioms numeric055
theorem hash055 : JFp_SHADigest.digest input055=value055 := by
  unfold input055 JFp_SHADigest.digest
  rw [numeric055,JGc_TX2_M2.Hash055.checked]
  rfl
#print axioms hash055
theorem address055 : BinMerkle32Path.nodeInput (children value043 (JGc_TX2_HashBytes.state [242,174,53,98,236,119,86,230,109,140,232,241,212,38,245,247,14,118,30,251,108,244,69,208,7,159,60,242,211,147,9,58]))=input055 := by rfl
#print axioms address055
def tree055 : Tree := .branch tree043 (.supplied (JGc_TX2_HashBytes.state [242,174,53,98,236,119,86,230,109,140,232,241,212,38,245,247,14,118,30,251,108,244,69,208,7,159,60,242,211,147,9,58]))
theorem root055 : root JFp_SHADigest.digest tree055=value055 := by
  rw [tree055,root,root043]
  exact (congrArg JFp_SHADigest.digest address055).trans hash055
#print axioms root055
theorem shape055 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 41536=tree055 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 41536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape043 f g inputs siblings]
  rw [unoccupied f g 3 41544 (by decide),siblings 3 (by decide) 41544 (by decide)]
  rfl
#print axioms shape055
def input056 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash056.message
def value056 : State := JFp_SHADigest.output JGc_TX2_M2.Hash056.result
theorem cast056_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash056.B00.input).map Fin.val=JGc_TX2_M2.Hash056.B00.input := by rfl
#print axioms cast056_0
theorem tail056 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash056.tail).map Fin.val=JGc_TX2_M2.Hash056.tail := by rfl
#print axioms tail056
theorem numeric056 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash056.message).map Fin.val=JGc_TX2_M2.Hash056.message := by
  simp only [JGc_TX2_M2.Hash056.message,JGc_TX2_M2.Hash056.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast056_0,tail056]
#print axioms numeric056
theorem hash056 : JFp_SHADigest.digest input056=value056 := by
  unfold input056 JFp_SHADigest.digest
  rw [numeric056,JGc_TX2_M2.Hash056.checked]
  rfl
#print axioms hash056
theorem address056 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [181,24,58,96,21,114,189,242,3,224,218,153,109,192,148,74,161,44,221,86,62,67,59,156,85,76,168,18,92,88,73,139]) value044)=input056 := by rfl
#print axioms address056
def tree056 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [181,24,58,96,21,114,189,242,3,224,218,153,109,192,148,74,161,44,221,86,62,67,59,156,85,76,168,18,92,88,73,139])) tree044
theorem root056 : root JFp_SHADigest.digest tree056=value056 := by
  rw [tree056,root,root044]
  exact (congrArg JFp_SHADigest.digest address056).trans hash056
#print axioms root056
theorem shape056 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 44512=tree056 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 44512)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 44512 (by decide),siblings 3 (by decide) 44512 (by decide)]
  rw [shape044 f g inputs siblings]
  rfl
#print axioms shape056
def input057 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash057.message
def value057 : State := JFp_SHADigest.output JGc_TX2_M2.Hash057.result
theorem cast057_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash057.B00.input).map Fin.val=JGc_TX2_M2.Hash057.B00.input := by rfl
#print axioms cast057_0
theorem tail057 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash057.tail).map Fin.val=JGc_TX2_M2.Hash057.tail := by rfl
#print axioms tail057
theorem numeric057 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash057.message).map Fin.val=JGc_TX2_M2.Hash057.message := by
  simp only [JGc_TX2_M2.Hash057.message,JGc_TX2_M2.Hash057.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast057_0,tail057]
#print axioms numeric057
theorem hash057 : JFp_SHADigest.digest input057=value057 := by
  unfold input057 JFp_SHADigest.digest
  rw [numeric057,JGc_TX2_M2.Hash057.checked]
  rfl
#print axioms hash057
theorem address057 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [208,1,212,22,67,71,24,33,10,48,177,72,179,173,12,119,211,126,91,87,29,41,125,54,223,127,0,153,28,47,233,206]) value045)=input057 := by rfl
#print axioms address057
def tree057 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [208,1,212,22,67,71,24,33,10,48,177,72,179,173,12,119,211,126,91,87,29,41,125,54,223,127,0,153,28,47,233,206])) tree045
theorem root057 : root JFp_SHADigest.digest tree057=value057 := by
  rw [tree057,root,root045]
  exact (congrArg JFp_SHADigest.digest address057).trans hash057
#print axioms root057
theorem shape057 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 44896=tree057 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 44896)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 44896 (by decide),siblings 3 (by decide) 44896 (by decide)]
  rw [shape045 f g inputs siblings]
  rfl
#print axioms shape057
def input058 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash058.message
def value058 : State := JFp_SHADigest.output JGc_TX2_M2.Hash058.result
theorem cast058_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash058.B00.input).map Fin.val=JGc_TX2_M2.Hash058.B00.input := by rfl
#print axioms cast058_0
theorem tail058 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash058.tail).map Fin.val=JGc_TX2_M2.Hash058.tail := by rfl
#print axioms tail058
theorem numeric058 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash058.message).map Fin.val=JGc_TX2_M2.Hash058.message := by
  simp only [JGc_TX2_M2.Hash058.message,JGc_TX2_M2.Hash058.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast058_0,tail058]
#print axioms numeric058
theorem hash058 : JFp_SHADigest.digest input058=value058 := by
  unfold input058 JFp_SHADigest.digest
  rw [numeric058,JGc_TX2_M2.Hash058.checked]
  rfl
#print axioms hash058
theorem address058 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [213,53,234,214,226,75,68,216,43,160,149,188,176,221,26,193,190,193,41,72,191,124,178,88,244,39,51,140,184,208,13,212]) value046)=input058 := by rfl
#print axioms address058
def tree058 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [213,53,234,214,226,75,68,216,43,160,149,188,176,221,26,193,190,193,41,72,191,124,178,88,244,39,51,140,184,208,13,212])) tree046
theorem root058 : root JFp_SHADigest.digest tree058=value058 := by
  rw [tree058,root,root046]
  exact (congrArg JFp_SHADigest.digest address058).trans hash058
#print axioms root058
theorem shape058 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 46400=tree058 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 46400)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 46400 (by decide),siblings 3 (by decide) 46400 (by decide)]
  rw [shape046 f g inputs siblings]
  rfl
#print axioms shape058
def input059 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash059.message
def value059 : State := JFp_SHADigest.output JGc_TX2_M2.Hash059.result
theorem cast059_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash059.B00.input).map Fin.val=JGc_TX2_M2.Hash059.B00.input := by rfl
#print axioms cast059_0
theorem tail059 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash059.tail).map Fin.val=JGc_TX2_M2.Hash059.tail := by rfl
#print axioms tail059
theorem numeric059 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash059.message).map Fin.val=JGc_TX2_M2.Hash059.message := by
  simp only [JGc_TX2_M2.Hash059.message,JGc_TX2_M2.Hash059.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast059_0,tail059]
#print axioms numeric059
theorem hash059 : JFp_SHADigest.digest input059=value059 := by
  unfold input059 JFp_SHADigest.digest
  rw [numeric059,JGc_TX2_M2.Hash059.checked]
  rfl
#print axioms hash059
theorem address059 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [167,37,76,229,79,74,103,216,118,47,142,90,252,35,167,62,177,237,14,107,80,22,103,190,64,199,180,188,0,68,33,33]) value047)=input059 := by rfl
#print axioms address059
def tree059 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [167,37,76,229,79,74,103,216,118,47,142,90,252,35,167,62,177,237,14,107,80,22,103,190,64,199,180,188,0,68,33,33])) tree047
theorem root059 : root JFp_SHADigest.digest tree059=value059 := by
  rw [tree059,root,root047]
  exact (congrArg JFp_SHADigest.digest address059).trans hash059
#print axioms root059
theorem shape059 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 54512=tree059 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 54512)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 54512 (by decide),siblings 3 (by decide) 54512 (by decide)]
  rw [shape047 f g inputs siblings]
  rfl
#print axioms shape059
end AspisR1.JGc_TX2_M2Roots
end
