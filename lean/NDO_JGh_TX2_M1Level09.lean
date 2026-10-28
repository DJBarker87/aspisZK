import NDO_JGh_TX2_M1Level08
import NDO_JGh_TX2_M1W031
import NDO_JGh_TX2_M1W032
import NDO_JGh_TX2_M1W033
import NDO_JGh_TX2_M1W034
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input120 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash120.message
def value120 : State := JFp_SHADigest.output JGh_TX2_M1.Hash120.result
theorem cast120_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash120.B00.input).map Fin.val=JGh_TX2_M1.Hash120.B00.input := by rfl
#print axioms cast120_0
theorem tail120 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash120.tail).map Fin.val=JGh_TX2_M1.Hash120.tail := by rfl
#print axioms tail120
theorem numeric120 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash120.message).map Fin.val=JGh_TX2_M1.Hash120.message := by
  simp only [JGh_TX2_M1.Hash120.message,JGh_TX2_M1.Hash120.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast120_0,tail120]
#print axioms numeric120
theorem hash120 : JFp_SHADigest.digest input120=value120 := by
  unfold input120 JFp_SHADigest.digest
  rw [numeric120,JGh_TX2_M1.Hash120.checked]
  rfl
#print axioms hash120
theorem address120 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [130,185,98,202,72,96,135,175,172,212,75,206,162,236,165,9,112,161,131,225,150,170,148,143,233,168,44,69,105,19,106,230]) value108)=input120 := by rfl
#print axioms address120
def tree120 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [130,185,98,202,72,96,135,175,172,212,75,206,162,236,165,9,112,161,131,225,150,170,148,143,233,168,44,69,105,19,106,230])) tree108
theorem root120 : root JFp_SHADigest.digest tree120=value120 := by
  rw [tree120,root,root108]
  exact (congrArg JFp_SHADigest.digest address120).trans hash120
#print axioms root120
theorem shape120 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 13312=tree120 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 13312)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 9 13312 (by decide),siblings 9 (by decide) 13312 (by decide)]
  rw [shape108 f g inputs siblings]
  rfl
#print axioms shape120
def input121 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash121.message
def value121 : State := JFp_SHADigest.output JGh_TX2_M1.Hash121.result
theorem cast121_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash121.B00.input).map Fin.val=JGh_TX2_M1.Hash121.B00.input := by rfl
#print axioms cast121_0
theorem tail121 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash121.tail).map Fin.val=JGh_TX2_M1.Hash121.tail := by rfl
#print axioms tail121
theorem numeric121 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash121.message).map Fin.val=JGh_TX2_M1.Hash121.message := by
  simp only [JGh_TX2_M1.Hash121.message,JGh_TX2_M1.Hash121.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast121_0,tail121]
#print axioms numeric121
theorem hash121 : JFp_SHADigest.digest input121=value121 := by
  unfold input121 JFp_SHADigest.digest
  rw [numeric121,JGh_TX2_M1.Hash121.checked]
  rfl
#print axioms hash121
theorem address121 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [104,238,251,221,129,233,105,49,254,18,192,35,164,102,96,216,214,220,116,64,96,176,13,99,130,187,100,30,144,92,13,169]) value109)=input121 := by rfl
#print axioms address121
def tree121 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [104,238,251,221,129,233,105,49,254,18,192,35,164,102,96,216,214,220,116,64,96,176,13,99,130,187,100,30,144,92,13,169])) tree109
theorem root121 : root JFp_SHADigest.digest tree121=value121 := by
  rw [tree121,root,root109]
  exact (congrArg JFp_SHADigest.digest address121).trans hash121
#print axioms root121
theorem shape121 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 20480=tree121 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 20480)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 9 20480 (by decide),siblings 9 (by decide) 20480 (by decide)]
  rw [shape109 f g inputs siblings]
  rfl
#print axioms shape121
def input122 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash122.message
def value122 : State := JFp_SHADigest.output JGh_TX2_M1.Hash122.result
theorem cast122_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash122.B00.input).map Fin.val=JGh_TX2_M1.Hash122.B00.input := by rfl
#print axioms cast122_0
theorem tail122 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash122.tail).map Fin.val=JGh_TX2_M1.Hash122.tail := by rfl
#print axioms tail122
theorem numeric122 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash122.message).map Fin.val=JGh_TX2_M1.Hash122.message := by
  simp only [JGh_TX2_M1.Hash122.message,JGh_TX2_M1.Hash122.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast122_0,tail122]
#print axioms numeric122
theorem hash122 : JFp_SHADigest.digest input122=value122 := by
  unfold input122 JFp_SHADigest.digest
  rw [numeric122,JGh_TX2_M1.Hash122.checked]
  rfl
#print axioms hash122
theorem address122 : BinMerkle32Path.nodeInput (children value110 (JGc_TX2_HashBytes.state [232,189,182,68,8,202,206,143,149,215,17,79,232,75,101,220,18,251,81,183,48,154,194,72,155,199,103,177,156,134,182,242]))=input122 := by rfl
#print axioms address122
def tree122 : Tree := .branch tree110 (.supplied (JGc_TX2_HashBytes.state [232,189,182,68,8,202,206,143,149,215,17,79,232,75,101,220,18,251,81,183,48,154,194,72,155,199,103,177,156,134,182,242]))
theorem root122 : root JFp_SHADigest.digest tree122=value122 := by
  rw [tree122,root,root110]
  exact (congrArg JFp_SHADigest.digest address122).trans hash122
#print axioms root122
theorem shape122 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 41984=tree122 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 41984)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape110 f g inputs siblings]
  rw [unoccupied f g 9 42496 (by decide),siblings 9 (by decide) 42496 (by decide)]
  rfl
#print axioms shape122
def input123 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash123.message
def value123 : State := JFp_SHADigest.output JGh_TX2_M1.Hash123.result
theorem cast123_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash123.B00.input).map Fin.val=JGh_TX2_M1.Hash123.B00.input := by rfl
#print axioms cast123_0
theorem tail123 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash123.tail).map Fin.val=JGh_TX2_M1.Hash123.tail := by rfl
#print axioms tail123
theorem numeric123 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash123.message).map Fin.val=JGh_TX2_M1.Hash123.message := by
  simp only [JGh_TX2_M1.Hash123.message,JGh_TX2_M1.Hash123.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast123_0,tail123]
#print axioms numeric123
theorem hash123 : JFp_SHADigest.digest input123=value123 := by
  unfold input123 JFp_SHADigest.digest
  rw [numeric123,JGh_TX2_M1.Hash123.checked]
  rfl
#print axioms hash123
theorem address123 : BinMerkle32Path.nodeInput (children value111 (JGc_TX2_HashBytes.state [19,100,208,181,251,91,42,146,145,254,5,88,89,79,90,4,96,242,146,207,7,163,45,119,27,181,28,2,143,138,26,102]))=input123 := by rfl
#print axioms address123
def tree123 : Tree := .branch tree111 (.supplied (JGc_TX2_HashBytes.state [19,100,208,181,251,91,42,146,145,254,5,88,89,79,90,4,96,242,146,207,7,163,45,119,27,181,28,2,143,138,26,102]))
theorem root123 : root JFp_SHADigest.digest tree123=value123 := by
  rw [tree123,root,root111]
  exact (congrArg JFp_SHADigest.digest address123).trans hash123
#print axioms root123
theorem shape123 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 55296=tree123 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 55296)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape111 f g inputs siblings]
  rw [unoccupied f g 9 55808 (by decide),siblings 9 (by decide) 55808 (by decide)]
  rfl
#print axioms shape123
def input124 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash124.message
def value124 : State := JFp_SHADigest.output JGh_TX2_M1.Hash124.result
theorem cast124_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash124.B00.input).map Fin.val=JGh_TX2_M1.Hash124.B00.input := by rfl
#print axioms cast124_0
theorem tail124 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash124.tail).map Fin.val=JGh_TX2_M1.Hash124.tail := by rfl
#print axioms tail124
theorem numeric124 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash124.message).map Fin.val=JGh_TX2_M1.Hash124.message := by
  simp only [JGh_TX2_M1.Hash124.message,JGh_TX2_M1.Hash124.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast124_0,tail124]
#print axioms numeric124
theorem hash124 : JFp_SHADigest.digest input124=value124 := by
  unfold input124 JFp_SHADigest.digest
  rw [numeric124,JGh_TX2_M1.Hash124.checked]
  rfl
#print axioms hash124
theorem address124 : BinMerkle32Path.nodeInput (children value112 (JGc_TX2_HashBytes.state [240,66,69,175,98,37,146,100,236,154,130,107,94,23,162,232,163,188,228,31,108,245,119,169,62,66,110,153,125,245,144,148]))=input124 := by rfl
#print axioms address124
def tree124 : Tree := .branch tree112 (.supplied (JGc_TX2_HashBytes.state [240,66,69,175,98,37,146,100,236,154,130,107,94,23,162,232,163,188,228,31,108,245,119,169,62,66,110,153,125,245,144,148]))
theorem root124 : root JFp_SHADigest.digest tree124=value124 := by
  rw [tree124,root,root112]
  exact (congrArg JFp_SHADigest.digest address124).trans hash124
#print axioms root124
theorem shape124 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 63488=tree124 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 63488)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape112 f g inputs siblings]
  rw [unoccupied f g 9 64000 (by decide),siblings 9 (by decide) 64000 (by decide)]
  rfl
#print axioms shape124
def input125 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash125.message
def value125 : State := JFp_SHADigest.output JGh_TX2_M1.Hash125.result
theorem cast125_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash125.B00.input).map Fin.val=JGh_TX2_M1.Hash125.B00.input := by rfl
#print axioms cast125_0
theorem tail125 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash125.tail).map Fin.val=JGh_TX2_M1.Hash125.tail := by rfl
#print axioms tail125
theorem numeric125 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash125.message).map Fin.val=JGh_TX2_M1.Hash125.message := by
  simp only [JGh_TX2_M1.Hash125.message,JGh_TX2_M1.Hash125.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast125_0,tail125]
#print axioms numeric125
theorem hash125 : JFp_SHADigest.digest input125=value125 := by
  unfold input125 JFp_SHADigest.digest
  rw [numeric125,JGh_TX2_M1.Hash125.checked]
  rfl
#print axioms hash125
theorem address125 : BinMerkle32Path.nodeInput (children value113 (JGc_TX2_HashBytes.state [104,144,215,91,40,32,87,253,114,160,44,249,37,104,47,19,238,42,154,43,170,126,241,151,2,73,249,220,25,152,84,147]))=input125 := by rfl
#print axioms address125
def tree125 : Tree := .branch tree113 (.supplied (JGc_TX2_HashBytes.state [104,144,215,91,40,32,87,253,114,160,44,249,37,104,47,19,238,42,154,43,170,126,241,151,2,73,249,220,25,152,84,147]))
theorem root125 : root JFp_SHADigest.digest tree125=value125 := by
  rw [tree125,root,root113]
  exact (congrArg JFp_SHADigest.digest address125).trans hash125
#print axioms root125
theorem shape125 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 132096=tree125 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 132096)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape113 f g inputs siblings]
  rw [unoccupied f g 9 132608 (by decide),siblings 9 (by decide) 132608 (by decide)]
  rfl
#print axioms shape125
def input126 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash126.message
def value126 : State := JFp_SHADigest.output JGh_TX2_M1.Hash126.result
theorem cast126_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash126.B00.input).map Fin.val=JGh_TX2_M1.Hash126.B00.input := by rfl
#print axioms cast126_0
theorem tail126 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash126.tail).map Fin.val=JGh_TX2_M1.Hash126.tail := by rfl
#print axioms tail126
theorem numeric126 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash126.message).map Fin.val=JGh_TX2_M1.Hash126.message := by
  simp only [JGh_TX2_M1.Hash126.message,JGh_TX2_M1.Hash126.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast126_0,tail126]
#print axioms numeric126
theorem hash126 : JFp_SHADigest.digest input126=value126 := by
  unfold input126 JFp_SHADigest.digest
  rw [numeric126,JGh_TX2_M1.Hash126.checked]
  rfl
#print axioms hash126
theorem address126 : BinMerkle32Path.nodeInput (children value114 (JGc_TX2_HashBytes.state [221,240,248,216,67,18,23,141,36,56,224,125,147,219,52,75,177,222,151,2,174,251,125,145,104,146,98,160,185,8,242,225]))=input126 := by rfl
#print axioms address126
def tree126 : Tree := .branch tree114 (.supplied (JGc_TX2_HashBytes.state [221,240,248,216,67,18,23,141,36,56,224,125,147,219,52,75,177,222,151,2,174,251,125,145,104,146,98,160,185,8,242,225]))
theorem root126 : root JFp_SHADigest.digest tree126=value126 := by
  rw [tree126,root,root114]
  exact (congrArg JFp_SHADigest.digest address126).trans hash126
#print axioms root126
theorem shape126 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 149504=tree126 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 149504)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape114 f g inputs siblings]
  rw [unoccupied f g 9 150016 (by decide),siblings 9 (by decide) 150016 (by decide)]
  rfl
#print axioms shape126
def input127 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash127.message
def value127 : State := JFp_SHADigest.output JGh_TX2_M1.Hash127.result
theorem cast127_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash127.B00.input).map Fin.val=JGh_TX2_M1.Hash127.B00.input := by rfl
#print axioms cast127_0
theorem tail127 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash127.tail).map Fin.val=JGh_TX2_M1.Hash127.tail := by rfl
#print axioms tail127
theorem numeric127 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash127.message).map Fin.val=JGh_TX2_M1.Hash127.message := by
  simp only [JGh_TX2_M1.Hash127.message,JGh_TX2_M1.Hash127.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast127_0,tail127]
#print axioms numeric127
theorem hash127 : JFp_SHADigest.digest input127=value127 := by
  unfold input127 JFp_SHADigest.digest
  rw [numeric127,JGh_TX2_M1.Hash127.checked]
  rfl
#print axioms hash127
theorem address127 : BinMerkle32Path.nodeInput (children value115 (JGc_TX2_HashBytes.state [180,243,99,41,168,48,130,40,201,18,159,219,85,3,215,185,53,211,171,105,181,28,76,217,128,225,127,76,39,156,43,141]))=input127 := by rfl
#print axioms address127
def tree127 : Tree := .branch tree115 (.supplied (JGc_TX2_HashBytes.state [180,243,99,41,168,48,130,40,201,18,159,219,85,3,215,185,53,211,171,105,181,28,76,217,128,225,127,76,39,156,43,141]))
theorem root127 : root JFp_SHADigest.digest tree127=value127 := by
  rw [tree127,root,root115]
  exact (congrArg JFp_SHADigest.digest address127).trans hash127
#print axioms root127
theorem shape127 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 165888=tree127 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 165888)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape115 f g inputs siblings]
  rw [unoccupied f g 9 166400 (by decide),siblings 9 (by decide) 166400 (by decide)]
  rfl
#print axioms shape127
def input128 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash128.message
def value128 : State := JFp_SHADigest.output JGh_TX2_M1.Hash128.result
theorem cast128_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash128.B00.input).map Fin.val=JGh_TX2_M1.Hash128.B00.input := by rfl
#print axioms cast128_0
theorem tail128 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash128.tail).map Fin.val=JGh_TX2_M1.Hash128.tail := by rfl
#print axioms tail128
theorem numeric128 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash128.message).map Fin.val=JGh_TX2_M1.Hash128.message := by
  simp only [JGh_TX2_M1.Hash128.message,JGh_TX2_M1.Hash128.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast128_0,tail128]
#print axioms numeric128
theorem hash128 : JFp_SHADigest.digest input128=value128 := by
  unfold input128 JFp_SHADigest.digest
  rw [numeric128,JGh_TX2_M1.Hash128.checked]
  rfl
#print axioms hash128
theorem address128 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [211,232,30,218,156,136,192,200,241,47,143,125,240,121,82,207,114,93,20,54,62,10,220,103,185,87,29,17,248,228,116,151]) value116)=input128 := by rfl
#print axioms address128
def tree128 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [211,232,30,218,156,136,192,200,241,47,143,125,240,121,82,207,114,93,20,54,62,10,220,103,185,87,29,17,248,228,116,151])) tree116
theorem root128 : root JFp_SHADigest.digest tree128=value128 := by
  rw [tree128,root,root116]
  exact (congrArg JFp_SHADigest.digest address128).trans hash128
#print axioms root128
theorem shape128 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 177152=tree128 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 177152)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 9 177152 (by decide),siblings 9 (by decide) 177152 (by decide)]
  rw [shape116 f g inputs siblings]
  rfl
#print axioms shape128
def input129 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash129.message
def value129 : State := JFp_SHADigest.output JGh_TX2_M1.Hash129.result
theorem cast129_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash129.B00.input).map Fin.val=JGh_TX2_M1.Hash129.B00.input := by rfl
#print axioms cast129_0
theorem tail129 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash129.tail).map Fin.val=JGh_TX2_M1.Hash129.tail := by rfl
#print axioms tail129
theorem numeric129 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash129.message).map Fin.val=JGh_TX2_M1.Hash129.message := by
  simp only [JGh_TX2_M1.Hash129.message,JGh_TX2_M1.Hash129.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast129_0,tail129]
#print axioms numeric129
theorem hash129 : JFp_SHADigest.digest input129=value129 := by
  unfold input129 JFp_SHADigest.digest
  rw [numeric129,JGh_TX2_M1.Hash129.checked]
  rfl
#print axioms hash129
theorem address129 : BinMerkle32Path.nodeInput (children value117 (JGc_TX2_HashBytes.state [58,129,244,208,125,246,96,110,135,70,125,72,31,234,51,54,222,237,4,41,181,252,158,199,190,114,248,97,210,170,234,242]))=input129 := by rfl
#print axioms address129
def tree129 : Tree := .branch tree117 (.supplied (JGc_TX2_HashBytes.state [58,129,244,208,125,246,96,110,135,70,125,72,31,234,51,54,222,237,4,41,181,252,158,199,190,114,248,97,210,170,234,242]))
theorem root129 : root JFp_SHADigest.digest tree129=value129 := by
  rw [tree129,root,root117]
  exact (congrArg JFp_SHADigest.digest address129).trans hash129
#print axioms root129
theorem shape129 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 179200=tree129 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 179200)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape117 f g inputs siblings]
  rw [unoccupied f g 9 179712 (by decide),siblings 9 (by decide) 179712 (by decide)]
  rfl
#print axioms shape129
def input130 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash130.message
def value130 : State := JFp_SHADigest.output JGh_TX2_M1.Hash130.result
theorem cast130_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash130.B00.input).map Fin.val=JGh_TX2_M1.Hash130.B00.input := by rfl
#print axioms cast130_0
theorem tail130 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash130.tail).map Fin.val=JGh_TX2_M1.Hash130.tail := by rfl
#print axioms tail130
theorem numeric130 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash130.message).map Fin.val=JGh_TX2_M1.Hash130.message := by
  simp only [JGh_TX2_M1.Hash130.message,JGh_TX2_M1.Hash130.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast130_0,tail130]
#print axioms numeric130
theorem hash130 : JFp_SHADigest.digest input130=value130 := by
  unfold input130 JFp_SHADigest.digest
  rw [numeric130,JGh_TX2_M1.Hash130.checked]
  rfl
#print axioms hash130
theorem address130 : BinMerkle32Path.nodeInput (children value118 (JGc_TX2_HashBytes.state [67,80,197,173,70,32,89,45,183,161,33,155,65,118,192,43,148,72,208,176,194,70,164,189,154,145,214,127,198,29,213,157]))=input130 := by rfl
#print axioms address130
def tree130 : Tree := .branch tree118 (.supplied (JGc_TX2_HashBytes.state [67,80,197,173,70,32,89,45,183,161,33,155,65,118,192,43,148,72,208,176,194,70,164,189,154,145,214,127,198,29,213,157]))
theorem root130 : root JFp_SHADigest.digest tree130=value130 := by
  rw [tree130,root,root118]
  exact (congrArg JFp_SHADigest.digest address130).trans hash130
#print axioms root130
theorem shape130 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 185344=tree130 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 185344)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape118 f g inputs siblings]
  rw [unoccupied f g 9 185856 (by decide),siblings 9 (by decide) 185856 (by decide)]
  rfl
#print axioms shape130
def input131 : Bytes := JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash131.message
def value131 : State := JFp_SHADigest.output JGh_TX2_M1.Hash131.result
theorem cast131_0 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash131.B00.input).map Fin.val=JGh_TX2_M1.Hash131.B00.input := by rfl
#print axioms cast131_0
theorem tail131 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash131.tail).map Fin.val=JGh_TX2_M1.Hash131.tail := by rfl
#print axioms tail131
theorem numeric131 : (JGc_TX2_HashBytes.bytes JGh_TX2_M1.Hash131.message).map Fin.val=JGh_TX2_M1.Hash131.message := by
  simp only [JGh_TX2_M1.Hash131.message,JGh_TX2_M1.Hash131.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast131_0,tail131]
#print axioms numeric131
theorem hash131 : JFp_SHADigest.digest input131=value131 := by
  unfold input131 JFp_SHADigest.digest
  rw [numeric131,JGh_TX2_M1.Hash131.checked]
  rfl
#print axioms hash131
theorem address131 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [177,204,239,161,93,49,187,132,99,218,156,136,202,126,183,178,31,155,221,149,31,142,50,141,22,212,20,241,125,78,220,36]) value119)=input131 := by rfl
#print axioms address131
def tree131 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [177,204,239,161,93,49,187,132,99,218,156,136,202,126,183,178,31,155,221,149,31,142,50,141,22,212,20,241,125,78,220,36])) tree119
theorem root131 : root JFp_SHADigest.digest tree131=value131 := by
  rw [tree131,root,root119]
  exact (congrArg JFp_SHADigest.digest address131).trans hash131
#print axioms root131
theorem shape131 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 217088=tree131 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 217088)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 9 217088 (by decide),siblings 9 (by decide) 217088 (by decide)]
  rw [shape119 f g inputs siblings]
  rfl
#print axioms shape131
end AspisR1.JGh_TX2_M1Roots
end
