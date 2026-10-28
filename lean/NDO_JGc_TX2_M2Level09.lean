import NDO_JGc_TX2_M2Level08
import NDO_JGc_TX2_M2H120
import NDO_JGc_TX2_M2H124
import NDO_JGc_TX2_M2H128
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input120 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash120.message
def value120 : State := JFp_SHADigest.output JGc_TX2_M2.Hash120.result
theorem cast120_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash120.B00.input).map Fin.val=JGc_TX2_M2.Hash120.B00.input := by rfl
#print axioms cast120_0
theorem tail120 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash120.tail).map Fin.val=JGc_TX2_M2.Hash120.tail := by rfl
#print axioms tail120
theorem numeric120 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash120.message).map Fin.val=JGc_TX2_M2.Hash120.message := by
  simp only [JGc_TX2_M2.Hash120.message,JGc_TX2_M2.Hash120.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast120_0,tail120]
#print axioms numeric120
theorem hash120 : JFp_SHADigest.digest input120=value120 := by
  unfold input120 JFp_SHADigest.digest
  rw [numeric120,JGc_TX2_M2.Hash120.checked]
  rfl
#print axioms hash120
theorem address120 : BinMerkle32Path.nodeInput (children value108 (JGc_TX2_HashBytes.state [168,7,249,118,41,85,216,10,25,159,158,171,90,187,183,16,118,37,5,65,104,46,122,46,48,223,68,164,178,237,132,147]))=input120 := by rfl
#print axioms address120
def tree120 : Tree := .branch tree108 (.supplied (JGc_TX2_HashBytes.state [168,7,249,118,41,85,216,10,25,159,158,171,90,187,183,16,118,37,5,65,104,46,122,46,48,223,68,164,178,237,132,147]))
theorem root120 : root JFp_SHADigest.digest tree120=value120 := by
  rw [tree120,root,root108]
  exact (congrArg JFp_SHADigest.digest address120).trans hash120
#print axioms root120
theorem shape120 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 3072=tree120 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 3072)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape108 f g inputs siblings]
  rw [unoccupied f g 9 3584 (by decide),siblings 9 (by decide) 3584 (by decide)]
  rfl
#print axioms shape120
def input121 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash121.message
def value121 : State := JFp_SHADigest.output JGc_TX2_M2.Hash121.result
theorem cast121_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash121.B00.input).map Fin.val=JGc_TX2_M2.Hash121.B00.input := by rfl
#print axioms cast121_0
theorem tail121 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash121.tail).map Fin.val=JGc_TX2_M2.Hash121.tail := by rfl
#print axioms tail121
theorem numeric121 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash121.message).map Fin.val=JGc_TX2_M2.Hash121.message := by
  simp only [JGc_TX2_M2.Hash121.message,JGc_TX2_M2.Hash121.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast121_0,tail121]
#print axioms numeric121
theorem hash121 : JFp_SHADigest.digest input121=value121 := by
  unfold input121 JFp_SHADigest.digest
  rw [numeric121,JGc_TX2_M2.Hash121.checked]
  rfl
#print axioms hash121
theorem address121 : BinMerkle32Path.nodeInput (children value109 (JGc_TX2_HashBytes.state [223,110,19,245,244,227,40,27,81,156,133,231,100,90,222,155,141,223,74,73,201,135,68,137,159,19,105,243,31,9,14,253]))=input121 := by rfl
#print axioms address121
def tree121 : Tree := .branch tree109 (.supplied (JGc_TX2_HashBytes.state [223,110,19,245,244,227,40,27,81,156,133,231,100,90,222,155,141,223,74,73,201,135,68,137,159,19,105,243,31,9,14,253]))
theorem root121 : root JFp_SHADigest.digest tree121=value121 := by
  rw [tree121,root,root109]
  exact (congrArg JFp_SHADigest.digest address121).trans hash121
#print axioms root121
theorem shape121 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 5120=tree121 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 5120)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape109 f g inputs siblings]
  rw [unoccupied f g 9 5632 (by decide),siblings 9 (by decide) 5632 (by decide)]
  rfl
#print axioms shape121
def input122 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash122.message
def value122 : State := JFp_SHADigest.output JGc_TX2_M2.Hash122.result
theorem cast122_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash122.B00.input).map Fin.val=JGc_TX2_M2.Hash122.B00.input := by rfl
#print axioms cast122_0
theorem tail122 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash122.tail).map Fin.val=JGc_TX2_M2.Hash122.tail := by rfl
#print axioms tail122
theorem numeric122 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash122.message).map Fin.val=JGc_TX2_M2.Hash122.message := by
  simp only [JGc_TX2_M2.Hash122.message,JGc_TX2_M2.Hash122.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast122_0,tail122]
#print axioms numeric122
theorem hash122 : JFp_SHADigest.digest input122=value122 := by
  unfold input122 JFp_SHADigest.digest
  rw [numeric122,JGc_TX2_M2.Hash122.checked]
  rfl
#print axioms hash122
theorem address122 : BinMerkle32Path.nodeInput (children value110 (JGc_TX2_HashBytes.state [102,114,57,147,28,89,57,26,132,252,183,78,113,182,85,171,1,134,183,8,61,123,243,13,61,142,238,93,184,41,34,9]))=input122 := by rfl
#print axioms address122
def tree122 : Tree := .branch tree110 (.supplied (JGc_TX2_HashBytes.state [102,114,57,147,28,89,57,26,132,252,183,78,113,182,85,171,1,134,183,8,61,123,243,13,61,142,238,93,184,41,34,9]))
theorem root122 : root JFp_SHADigest.digest tree122=value122 := by
  rw [tree122,root,root110]
  exact (congrArg JFp_SHADigest.digest address122).trans hash122
#print axioms root122
theorem shape122 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 10240=tree122 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 10240)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape110 f g inputs siblings]
  rw [unoccupied f g 9 10752 (by decide),siblings 9 (by decide) 10752 (by decide)]
  rfl
#print axioms shape122
def input123 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash123.message
def value123 : State := JFp_SHADigest.output JGc_TX2_M2.Hash123.result
theorem cast123_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash123.B00.input).map Fin.val=JGc_TX2_M2.Hash123.B00.input := by rfl
#print axioms cast123_0
theorem tail123 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash123.tail).map Fin.val=JGc_TX2_M2.Hash123.tail := by rfl
#print axioms tail123
theorem numeric123 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash123.message).map Fin.val=JGc_TX2_M2.Hash123.message := by
  simp only [JGc_TX2_M2.Hash123.message,JGc_TX2_M2.Hash123.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast123_0,tail123]
#print axioms numeric123
theorem hash123 : JFp_SHADigest.digest input123=value123 := by
  unfold input123 JFp_SHADigest.digest
  rw [numeric123,JGc_TX2_M2.Hash123.checked]
  rfl
#print axioms hash123
theorem address123 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [30,144,71,74,223,163,141,159,44,118,14,152,185,148,50,186,42,1,84,96,23,18,151,25,103,4,194,17,226,166,15,229]) value111)=input123 := by rfl
#print axioms address123
def tree123 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [30,144,71,74,223,163,141,159,44,118,14,152,185,148,50,186,42,1,84,96,23,18,151,25,103,4,194,17,226,166,15,229])) tree111
theorem root123 : root JFp_SHADigest.digest tree123=value123 := by
  rw [tree123,root,root111]
  exact (congrArg JFp_SHADigest.digest address123).trans hash123
#print axioms root123
theorem shape123 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 13312=tree123 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 13312)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 9 13312 (by decide),siblings 9 (by decide) 13312 (by decide)]
  rw [shape111 f g inputs siblings]
  rfl
#print axioms shape123
def input124 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash124.message
def value124 : State := JFp_SHADigest.output JGc_TX2_M2.Hash124.result
theorem cast124_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash124.B00.input).map Fin.val=JGc_TX2_M2.Hash124.B00.input := by rfl
#print axioms cast124_0
theorem tail124 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash124.tail).map Fin.val=JGc_TX2_M2.Hash124.tail := by rfl
#print axioms tail124
theorem numeric124 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash124.message).map Fin.val=JGc_TX2_M2.Hash124.message := by
  simp only [JGc_TX2_M2.Hash124.message,JGc_TX2_M2.Hash124.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast124_0,tail124]
#print axioms numeric124
theorem hash124 : JFp_SHADigest.digest input124=value124 := by
  unfold input124 JFp_SHADigest.digest
  rw [numeric124,JGc_TX2_M2.Hash124.checked]
  rfl
#print axioms hash124
theorem address124 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [168,185,27,215,169,143,230,34,123,226,41,203,176,173,35,86,15,160,129,187,149,85,125,69,74,221,167,0,254,58,246,97]) value112)=input124 := by rfl
#print axioms address124
def tree124 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [168,185,27,215,169,143,230,34,123,226,41,203,176,173,35,86,15,160,129,187,149,85,125,69,74,221,167,0,254,58,246,97])) tree112
theorem root124 : root JFp_SHADigest.digest tree124=value124 := by
  rw [tree124,root,root112]
  exact (congrArg JFp_SHADigest.digest address124).trans hash124
#print axioms root124
theorem shape124 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 15360=tree124 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 15360)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 9 15360 (by decide),siblings 9 (by decide) 15360 (by decide)]
  rw [shape112 f g inputs siblings]
  rfl
#print axioms shape124
def input125 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash125.message
def value125 : State := JFp_SHADigest.output JGc_TX2_M2.Hash125.result
theorem cast125_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash125.B00.input).map Fin.val=JGc_TX2_M2.Hash125.B00.input := by rfl
#print axioms cast125_0
theorem tail125 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash125.tail).map Fin.val=JGc_TX2_M2.Hash125.tail := by rfl
#print axioms tail125
theorem numeric125 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash125.message).map Fin.val=JGc_TX2_M2.Hash125.message := by
  simp only [JGc_TX2_M2.Hash125.message,JGc_TX2_M2.Hash125.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast125_0,tail125]
#print axioms numeric125
theorem hash125 : JFp_SHADigest.digest input125=value125 := by
  unfold input125 JFp_SHADigest.digest
  rw [numeric125,JGc_TX2_M2.Hash125.checked]
  rfl
#print axioms hash125
theorem address125 : BinMerkle32Path.nodeInput (children value113 (JGc_TX2_HashBytes.state [85,52,188,98,167,123,66,214,196,173,57,251,166,199,135,77,137,4,18,137,157,63,245,131,127,145,115,65,11,17,98,86]))=input125 := by rfl
#print axioms address125
def tree125 : Tree := .branch tree113 (.supplied (JGc_TX2_HashBytes.state [85,52,188,98,167,123,66,214,196,173,57,251,166,199,135,77,137,4,18,137,157,63,245,131,127,145,115,65,11,17,98,86]))
theorem root125 : root JFp_SHADigest.digest tree125=value125 := by
  rw [tree125,root,root113]
  exact (congrArg JFp_SHADigest.digest address125).trans hash125
#print axioms root125
theorem shape125 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 32768=tree125 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 32768)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape113 f g inputs siblings]
  rw [unoccupied f g 9 33280 (by decide),siblings 9 (by decide) 33280 (by decide)]
  rfl
#print axioms shape125
def input126 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash126.message
def value126 : State := JFp_SHADigest.output JGc_TX2_M2.Hash126.result
theorem cast126_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash126.B00.input).map Fin.val=JGc_TX2_M2.Hash126.B00.input := by rfl
#print axioms cast126_0
theorem tail126 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash126.tail).map Fin.val=JGc_TX2_M2.Hash126.tail := by rfl
#print axioms tail126
theorem numeric126 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash126.message).map Fin.val=JGc_TX2_M2.Hash126.message := by
  simp only [JGc_TX2_M2.Hash126.message,JGc_TX2_M2.Hash126.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast126_0,tail126]
#print axioms numeric126
theorem hash126 : JFp_SHADigest.digest input126=value126 := by
  unfold input126 JFp_SHADigest.digest
  rw [numeric126,JGc_TX2_M2.Hash126.checked]
  rfl
#print axioms hash126
theorem address126 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [3,169,173,149,56,183,16,65,144,251,102,110,90,130,50,162,198,79,206,71,140,144,205,72,79,12,148,87,5,250,183,64]) value114)=input126 := by rfl
#print axioms address126
def tree126 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [3,169,173,149,56,183,16,65,144,251,102,110,90,130,50,162,198,79,206,71,140,144,205,72,79,12,148,87,5,250,183,64])) tree114
theorem root126 : root JFp_SHADigest.digest tree126=value126 := by
  rw [tree126,root,root114]
  exact (congrArg JFp_SHADigest.digest address126).trans hash126
#print axioms root126
theorem shape126 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 36864=tree126 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 36864)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 9 36864 (by decide),siblings 9 (by decide) 36864 (by decide)]
  rw [shape114 f g inputs siblings]
  rfl
#print axioms shape126
def input127 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash127.message
def value127 : State := JFp_SHADigest.output JGc_TX2_M2.Hash127.result
theorem cast127_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash127.B00.input).map Fin.val=JGc_TX2_M2.Hash127.B00.input := by rfl
#print axioms cast127_0
theorem tail127 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash127.tail).map Fin.val=JGc_TX2_M2.Hash127.tail := by rfl
#print axioms tail127
theorem numeric127 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash127.message).map Fin.val=JGc_TX2_M2.Hash127.message := by
  simp only [JGc_TX2_M2.Hash127.message,JGc_TX2_M2.Hash127.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast127_0,tail127]
#print axioms numeric127
theorem hash127 : JFp_SHADigest.digest input127=value127 := by
  unfold input127 JFp_SHADigest.digest
  rw [numeric127,JGc_TX2_M2.Hash127.checked]
  rfl
#print axioms hash127
theorem address127 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [68,142,32,219,36,14,61,147,63,76,253,213,15,49,48,199,103,187,177,232,161,155,25,243,47,133,3,49,103,196,177,80]) value115)=input127 := by rfl
#print axioms address127
def tree127 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [68,142,32,219,36,14,61,147,63,76,253,213,15,49,48,199,103,187,177,232,161,155,25,243,47,133,3,49,103,196,177,80])) tree115
theorem root127 : root JFp_SHADigest.digest tree127=value127 := by
  rw [tree127,root,root115]
  exact (congrArg JFp_SHADigest.digest address127).trans hash127
#print axioms root127
theorem shape127 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 40960=tree127 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 40960)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 9 40960 (by decide),siblings 9 (by decide) 40960 (by decide)]
  rw [shape115 f g inputs siblings]
  rfl
#print axioms shape127
def input128 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash128.message
def value128 : State := JFp_SHADigest.output JGc_TX2_M2.Hash128.result
theorem cast128_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash128.B00.input).map Fin.val=JGc_TX2_M2.Hash128.B00.input := by rfl
#print axioms cast128_0
theorem tail128 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash128.tail).map Fin.val=JGc_TX2_M2.Hash128.tail := by rfl
#print axioms tail128
theorem numeric128 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash128.message).map Fin.val=JGc_TX2_M2.Hash128.message := by
  simp only [JGc_TX2_M2.Hash128.message,JGc_TX2_M2.Hash128.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast128_0,tail128]
#print axioms numeric128
theorem hash128 : JFp_SHADigest.digest input128=value128 := by
  unfold input128 JFp_SHADigest.digest
  rw [numeric128,JGc_TX2_M2.Hash128.checked]
  rfl
#print axioms hash128
theorem address128 : BinMerkle32Path.nodeInput (children value116 value117)=input128 := by rfl
#print axioms address128
def tree128 : Tree := .branch tree116 tree117
theorem root128 : root JFp_SHADigest.digest tree128=value128 := by
  rw [tree128,root,root116,root117]
  exact (congrArg JFp_SHADigest.digest address128).trans hash128
#print axioms root128
theorem shape128 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 44032=tree128 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 44032)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape116 f g inputs siblings]
  rw [shape117 f g inputs siblings]
  rfl
#print axioms shape128
def input129 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash129.message
def value129 : State := JFp_SHADigest.output JGc_TX2_M2.Hash129.result
theorem cast129_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash129.B00.input).map Fin.val=JGc_TX2_M2.Hash129.B00.input := by rfl
#print axioms cast129_0
theorem tail129 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash129.tail).map Fin.val=JGc_TX2_M2.Hash129.tail := by rfl
#print axioms tail129
theorem numeric129 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash129.message).map Fin.val=JGc_TX2_M2.Hash129.message := by
  simp only [JGc_TX2_M2.Hash129.message,JGc_TX2_M2.Hash129.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast129_0,tail129]
#print axioms numeric129
theorem hash129 : JFp_SHADigest.digest input129=value129 := by
  unfold input129 JFp_SHADigest.digest
  rw [numeric129,JGc_TX2_M2.Hash129.checked]
  rfl
#print axioms hash129
theorem address129 : BinMerkle32Path.nodeInput (children value118 (JGc_TX2_HashBytes.state [234,157,205,160,100,45,156,15,124,40,37,125,157,253,108,73,107,187,203,131,100,153,6,19,58,141,158,46,248,238,239,168]))=input129 := by rfl
#print axioms address129
def tree129 : Tree := .branch tree118 (.supplied (JGc_TX2_HashBytes.state [234,157,205,160,100,45,156,15,124,40,37,125,157,253,108,73,107,187,203,131,100,153,6,19,58,141,158,46,248,238,239,168]))
theorem root129 : root JFp_SHADigest.digest tree129=value129 := by
  rw [tree129,root,root118]
  exact (congrArg JFp_SHADigest.digest address129).trans hash129
#print axioms root129
theorem shape129 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 46080=tree129 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 46080)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape118 f g inputs siblings]
  rw [unoccupied f g 9 46592 (by decide),siblings 9 (by decide) 46592 (by decide)]
  rfl
#print axioms shape129
def input130 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash130.message
def value130 : State := JFp_SHADigest.output JGc_TX2_M2.Hash130.result
theorem cast130_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash130.B00.input).map Fin.val=JGc_TX2_M2.Hash130.B00.input := by rfl
#print axioms cast130_0
theorem tail130 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash130.tail).map Fin.val=JGc_TX2_M2.Hash130.tail := by rfl
#print axioms tail130
theorem numeric130 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash130.message).map Fin.val=JGc_TX2_M2.Hash130.message := by
  simp only [JGc_TX2_M2.Hash130.message,JGc_TX2_M2.Hash130.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast130_0,tail130]
#print axioms numeric130
theorem hash130 : JFp_SHADigest.digest input130=value130 := by
  unfold input130 JFp_SHADigest.digest
  rw [numeric130,JGc_TX2_M2.Hash130.checked]
  rfl
#print axioms hash130
theorem address130 : BinMerkle32Path.nodeInput (children value119 (JGc_TX2_HashBytes.state [236,197,164,41,198,181,226,108,46,53,158,12,123,51,246,145,217,190,204,61,35,251,196,98,163,57,138,148,20,238,77,232]))=input130 := by rfl
#print axioms address130
def tree130 : Tree := .branch tree119 (.supplied (JGc_TX2_HashBytes.state [236,197,164,41,198,181,226,108,46,53,158,12,123,51,246,145,217,190,204,61,35,251,196,98,163,57,138,148,20,238,77,232]))
theorem root130 : root JFp_SHADigest.digest tree130=value130 := by
  rw [tree130,root,root119]
  exact (congrArg JFp_SHADigest.digest address130).trans hash130
#print axioms root130
theorem shape130 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 10 54272=tree130 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 10 54272)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape119 f g inputs siblings]
  rw [unoccupied f g 9 54784 (by decide),siblings 9 (by decide) 54784 (by decide)]
  rfl
#print axioms shape130
end AspisR1.JGc_TX2_M2Roots
end
