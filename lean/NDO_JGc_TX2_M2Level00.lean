import NDO_JGc_TX2_M2Leaves
import NDO_JGc_TX2_M2H012
import NDO_JGc_TX2_M2H016
import NDO_JGc_TX2_M2H020
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input012 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash012.message
def value012 : State := JFp_SHADigest.output JGc_TX2_M2.Hash012.result
theorem cast012_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash012.B00.input).map Fin.val=JGc_TX2_M2.Hash012.B00.input := by rfl
#print axioms cast012_0
theorem tail012 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash012.tail).map Fin.val=JGc_TX2_M2.Hash012.tail := by rfl
#print axioms tail012
theorem numeric012 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash012.message).map Fin.val=JGc_TX2_M2.Hash012.message := by
  simp only [JGc_TX2_M2.Hash012.message,JGc_TX2_M2.Hash012.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast012_0,tail012]
#print axioms numeric012
theorem hash012 : JFp_SHADigest.digest input012=value012 := by
  unfold input012 JFp_SHADigest.digest
  rw [numeric012,JGc_TX2_M2.Hash012.checked]
  rfl
#print axioms hash012
theorem address012 : BinMerkle32Path.nodeInput (children value011 (JGc_TX2_HashBytes.state [180,21,97,221,206,42,157,228,161,6,8,8,60,127,63,122,65,180,144,0,136,151,89,138,223,113,167,80,73,114,235,138]))=input012 := by rfl
#print axioms address012
def tree012 : Tree := .branch tree011 (.supplied (JGc_TX2_HashBytes.state [180,21,97,221,206,42,157,228,161,6,8,8,60,127,63,122,65,180,144,0,136,151,89,138,223,113,167,80,73,114,235,138]))
theorem root012 : root JFp_SHADigest.digest tree012=value012 := by
  rw [tree012,root,root011]
  exact (congrArg JFp_SHADigest.digest address012).trans hash012
#print axioms root012
theorem shape012 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 3574=tree012 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 3574)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape011 f g inputs siblings]
  rw [unoccupied f g 0 3575 (by decide),siblings 0 (by decide) 3575 (by decide)]
  rfl
#print axioms shape012
def input013 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash013.message
def value013 : State := JFp_SHADigest.output JGc_TX2_M2.Hash013.result
theorem cast013_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash013.B00.input).map Fin.val=JGc_TX2_M2.Hash013.B00.input := by rfl
#print axioms cast013_0
theorem tail013 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash013.tail).map Fin.val=JGc_TX2_M2.Hash013.tail := by rfl
#print axioms tail013
theorem numeric013 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash013.message).map Fin.val=JGc_TX2_M2.Hash013.message := by
  simp only [JGc_TX2_M2.Hash013.message,JGc_TX2_M2.Hash013.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast013_0,tail013]
#print axioms numeric013
theorem hash013 : JFp_SHADigest.digest input013=value013 := by
  unfold input013 JFp_SHADigest.digest
  rw [numeric013,JGc_TX2_M2.Hash013.checked]
  rfl
#print axioms hash013
theorem address013 : BinMerkle32Path.nodeInput (children value007 (JGc_TX2_HashBytes.state [226,20,98,179,100,227,91,157,76,105,102,98,250,170,190,167,196,79,11,158,99,109,168,55,185,28,41,188,127,120,116,178]))=input013 := by rfl
#print axioms address013
def tree013 : Tree := .branch tree007 (.supplied (JGc_TX2_HashBytes.state [226,20,98,179,100,227,91,157,76,105,102,98,250,170,190,167,196,79,11,158,99,109,168,55,185,28,41,188,127,120,116,178]))
theorem root013 : root JFp_SHADigest.digest tree013=value013 := by
  rw [tree013,root,root007]
  exact (congrArg JFp_SHADigest.digest address013).trans hash013
#print axioms root013
theorem shape013 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 5312=tree013 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 5312)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape007 f g inputs siblings]
  rw [unoccupied f g 0 5313 (by decide),siblings 0 (by decide) 5313 (by decide)]
  rfl
#print axioms shape013
def input014 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash014.message
def value014 : State := JFp_SHADigest.output JGc_TX2_M2.Hash014.result
theorem cast014_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash014.B00.input).map Fin.val=JGc_TX2_M2.Hash014.B00.input := by rfl
#print axioms cast014_0
theorem tail014 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash014.tail).map Fin.val=JGc_TX2_M2.Hash014.tail := by rfl
#print axioms tail014
theorem numeric014 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash014.message).map Fin.val=JGc_TX2_M2.Hash014.message := by
  simp only [JGc_TX2_M2.Hash014.message,JGc_TX2_M2.Hash014.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast014_0,tail014]
#print axioms numeric014
theorem hash014 : JFp_SHADigest.digest input014=value014 := by
  unfold input014 JFp_SHADigest.digest
  rw [numeric014,JGc_TX2_M2.Hash014.checked]
  rfl
#print axioms hash014
theorem address014 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [30,234,97,8,0,194,43,152,243,12,102,85,108,58,198,168,55,163,44,21,26,161,228,212,123,68,134,47,251,122,63,214]) value005)=input014 := by rfl
#print axioms address014
def tree014 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [30,234,97,8,0,194,43,152,243,12,102,85,108,58,198,168,55,163,44,21,26,161,228,212,123,68,134,47,251,122,63,214])) tree005
theorem root014 : root JFp_SHADigest.digest tree014=value014 := by
  rw [tree014,root,root005]
  exact (congrArg JFp_SHADigest.digest address014).trans hash014
#print axioms root014
theorem shape014 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 10538=tree014 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 10538)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 10538 (by decide),siblings 0 (by decide) 10538 (by decide)]
  rw [shape005 f g inputs siblings]
  rfl
#print axioms shape014
def input015 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash015.message
def value015 : State := JFp_SHADigest.output JGc_TX2_M2.Hash015.result
theorem cast015_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash015.B00.input).map Fin.val=JGc_TX2_M2.Hash015.B00.input := by rfl
#print axioms cast015_0
theorem tail015 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash015.tail).map Fin.val=JGc_TX2_M2.Hash015.tail := by rfl
#print axioms tail015
theorem numeric015 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash015.message).map Fin.val=JGc_TX2_M2.Hash015.message := by
  simp only [JGc_TX2_M2.Hash015.message,JGc_TX2_M2.Hash015.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast015_0,tail015]
#print axioms numeric015
theorem hash015 : JFp_SHADigest.digest input015=value015 := by
  unfold input015 JFp_SHADigest.digest
  rw [numeric015,JGc_TX2_M2.Hash015.checked]
  rfl
#print axioms hash015
theorem address015 : BinMerkle32Path.nodeInput (children value009 (JGc_TX2_HashBytes.state [254,150,219,44,164,7,195,14,50,108,74,204,72,133,227,82,82,227,116,250,29,114,234,201,64,148,6,227,119,183,40,30]))=input015 := by rfl
#print axioms address015
def tree015 : Tree := .branch tree009 (.supplied (JGc_TX2_HashBytes.state [254,150,219,44,164,7,195,14,50,108,74,204,72,133,227,82,82,227,116,250,29,114,234,201,64,148,6,227,119,183,40,30]))
theorem root015 : root JFp_SHADigest.digest tree015=value015 := by
  rw [tree015,root,root009]
  exact (congrArg JFp_SHADigest.digest address015).trans hash015
#print axioms root015
theorem shape015 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 13844=tree015 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 13844)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape009 f g inputs siblings]
  rw [unoccupied f g 0 13845 (by decide),siblings 0 (by decide) 13845 (by decide)]
  rfl
#print axioms shape015
def input016 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash016.message
def value016 : State := JFp_SHADigest.output JGc_TX2_M2.Hash016.result
theorem cast016_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash016.B00.input).map Fin.val=JGc_TX2_M2.Hash016.B00.input := by rfl
#print axioms cast016_0
theorem tail016 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash016.tail).map Fin.val=JGc_TX2_M2.Hash016.tail := by rfl
#print axioms tail016
theorem numeric016 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash016.message).map Fin.val=JGc_TX2_M2.Hash016.message := by
  simp only [JGc_TX2_M2.Hash016.message,JGc_TX2_M2.Hash016.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast016_0,tail016]
#print axioms numeric016
theorem hash016 : JFp_SHADigest.digest input016=value016 := by
  unfold input016 JFp_SHADigest.digest
  rw [numeric016,JGc_TX2_M2.Hash016.checked]
  rfl
#print axioms hash016
theorem address016 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [236,100,137,161,98,93,113,107,30,53,251,16,18,175,194,3,50,216,196,187,48,153,170,10,234,14,102,83,245,126,82,132]) value008)=input016 := by rfl
#print axioms address016
def tree016 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [236,100,137,161,98,93,113,107,30,53,251,16,18,175,194,3,50,216,196,187,48,153,170,10,234,14,102,83,245,126,82,132])) tree008
theorem root016 : root JFp_SHADigest.digest tree016=value016 := by
  rw [tree016,root,root008]
  exact (congrArg JFp_SHADigest.digest address016).trans hash016
#print axioms root016
theorem shape016 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 15964=tree016 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 15964)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 15964 (by decide),siblings 0 (by decide) 15964 (by decide)]
  rw [shape008 f g inputs siblings]
  rfl
#print axioms shape016
def input017 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash017.message
def value017 : State := JFp_SHADigest.output JGc_TX2_M2.Hash017.result
theorem cast017_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash017.B00.input).map Fin.val=JGc_TX2_M2.Hash017.B00.input := by rfl
#print axioms cast017_0
theorem tail017 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash017.tail).map Fin.val=JGc_TX2_M2.Hash017.tail := by rfl
#print axioms tail017
theorem numeric017 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash017.message).map Fin.val=JGc_TX2_M2.Hash017.message := by
  simp only [JGc_TX2_M2.Hash017.message,JGc_TX2_M2.Hash017.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast017_0,tail017]
#print axioms numeric017
theorem hash017 : JFp_SHADigest.digest input017=value017 := by
  unfold input017 JFp_SHADigest.digest
  rw [numeric017,JGc_TX2_M2.Hash017.checked]
  rfl
#print axioms hash017
theorem address017 : BinMerkle32Path.nodeInput (children value000 (JGc_TX2_HashBytes.state [164,177,87,252,210,83,191,200,131,137,158,225,18,215,79,68,188,32,11,147,75,186,253,50,44,22,219,48,173,103,186,23]))=input017 := by rfl
#print axioms address017
def tree017 : Tree := .branch tree000 (.supplied (JGc_TX2_HashBytes.state [164,177,87,252,210,83,191,200,131,137,158,225,18,215,79,68,188,32,11,147,75,186,253,50,44,22,219,48,173,103,186,23]))
theorem root017 : root JFp_SHADigest.digest tree017=value017 := by
  rw [tree017,root,root000]
  exact (congrArg JFp_SHADigest.digest address017).trans hash017
#print axioms root017
theorem shape017 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 33088=tree017 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 33088)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape000 f g inputs siblings]
  rw [unoccupied f g 0 33089 (by decide),siblings 0 (by decide) 33089 (by decide)]
  rfl
#print axioms shape017
def input018 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash018.message
def value018 : State := JFp_SHADigest.output JGc_TX2_M2.Hash018.result
theorem cast018_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash018.B00.input).map Fin.val=JGc_TX2_M2.Hash018.B00.input := by rfl
#print axioms cast018_0
theorem tail018 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash018.tail).map Fin.val=JGc_TX2_M2.Hash018.tail := by rfl
#print axioms tail018
theorem numeric018 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash018.message).map Fin.val=JGc_TX2_M2.Hash018.message := by
  simp only [JGc_TX2_M2.Hash018.message,JGc_TX2_M2.Hash018.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast018_0,tail018]
#print axioms numeric018
theorem hash018 : JFp_SHADigest.digest input018=value018 := by
  unfold input018 JFp_SHADigest.digest
  rw [numeric018,JGc_TX2_M2.Hash018.checked]
  rfl
#print axioms hash018
theorem address018 : BinMerkle32Path.nodeInput (children value003 (JGc_TX2_HashBytes.state [38,240,77,77,158,151,198,249,159,74,207,189,184,175,230,236,148,167,177,249,211,18,254,145,86,1,85,69,178,6,229,99]))=input018 := by rfl
#print axioms address018
def tree018 : Tree := .branch tree003 (.supplied (JGc_TX2_HashBytes.state [38,240,77,77,158,151,198,249,159,74,207,189,184,175,230,236,148,167,177,249,211,18,254,145,86,1,85,69,178,6,229,99]))
theorem root018 : root JFp_SHADigest.digest tree018=value018 := by
  rw [tree018,root,root003]
  exact (congrArg JFp_SHADigest.digest address018).trans hash018
#print axioms root018
theorem shape018 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 37406=tree018 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 37406)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape003 f g inputs siblings]
  rw [unoccupied f g 0 37407 (by decide),siblings 0 (by decide) 37407 (by decide)]
  rfl
#print axioms shape018
def input019 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash019.message
def value019 : State := JFp_SHADigest.output JGc_TX2_M2.Hash019.result
theorem cast019_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash019.B00.input).map Fin.val=JGc_TX2_M2.Hash019.B00.input := by rfl
#print axioms cast019_0
theorem tail019 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash019.tail).map Fin.val=JGc_TX2_M2.Hash019.tail := by rfl
#print axioms tail019
theorem numeric019 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash019.message).map Fin.val=JGc_TX2_M2.Hash019.message := by
  simp only [JGc_TX2_M2.Hash019.message,JGc_TX2_M2.Hash019.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast019_0,tail019]
#print axioms numeric019
theorem hash019 : JFp_SHADigest.digest input019=value019 := by
  unfold input019 JFp_SHADigest.digest
  rw [numeric019,JGc_TX2_M2.Hash019.checked]
  rfl
#print axioms hash019
theorem address019 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [18,151,11,110,209,105,237,214,187,87,247,199,135,210,26,179,112,132,19,99,52,161,115,181,139,240,169,177,168,9,129,136]) value004)=input019 := by rfl
#print axioms address019
def tree019 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [18,151,11,110,209,105,237,214,187,87,247,199,135,210,26,179,112,132,19,99,52,161,115,181,139,240,169,177,168,9,129,136])) tree004
theorem root019 : root JFp_SHADigest.digest tree019=value019 := by
  rw [tree019,root,root004]
  exact (congrArg JFp_SHADigest.digest address019).trans hash019
#print axioms root019
theorem shape019 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 41540=tree019 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 41540)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 41540 (by decide),siblings 0 (by decide) 41540 (by decide)]
  rw [shape004 f g inputs siblings]
  rfl
#print axioms shape019
def input020 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash020.message
def value020 : State := JFp_SHADigest.output JGc_TX2_M2.Hash020.result
theorem cast020_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash020.B00.input).map Fin.val=JGc_TX2_M2.Hash020.B00.input := by rfl
#print axioms cast020_0
theorem tail020 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash020.tail).map Fin.val=JGc_TX2_M2.Hash020.tail := by rfl
#print axioms tail020
theorem numeric020 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash020.message).map Fin.val=JGc_TX2_M2.Hash020.message := by
  simp only [JGc_TX2_M2.Hash020.message,JGc_TX2_M2.Hash020.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast020_0,tail020]
#print axioms numeric020
theorem hash020 : JFp_SHADigest.digest input020=value020 := by
  unfold input020 JFp_SHADigest.digest
  rw [numeric020,JGc_TX2_M2.Hash020.checked]
  rfl
#print axioms hash020
theorem address020 : BinMerkle32Path.nodeInput (children value002 (JGc_TX2_HashBytes.state [28,229,74,68,36,36,95,126,209,115,58,28,208,51,184,79,202,7,192,163,105,36,148,171,148,54,57,124,25,47,67,97]))=input020 := by rfl
#print axioms address020
def tree020 : Tree := .branch tree002 (.supplied (JGc_TX2_HashBytes.state [28,229,74,68,36,36,95,126,209,115,58,28,208,51,184,79,202,7,192,163,105,36,148,171,148,54,57,124,25,47,67,97]))
theorem root020 : root JFp_SHADigest.digest tree020=value020 := by
  rw [tree020,root,root002]
  exact (congrArg JFp_SHADigest.digest address020).trans hash020
#print axioms root020
theorem shape020 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 44520=tree020 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 44520)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape002 f g inputs siblings]
  rw [unoccupied f g 0 44521 (by decide),siblings 0 (by decide) 44521 (by decide)]
  rfl
#print axioms shape020
def input021 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash021.message
def value021 : State := JFp_SHADigest.output JGc_TX2_M2.Hash021.result
theorem cast021_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash021.B00.input).map Fin.val=JGc_TX2_M2.Hash021.B00.input := by rfl
#print axioms cast021_0
theorem tail021 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash021.tail).map Fin.val=JGc_TX2_M2.Hash021.tail := by rfl
#print axioms tail021
theorem numeric021 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash021.message).map Fin.val=JGc_TX2_M2.Hash021.message := by
  simp only [JGc_TX2_M2.Hash021.message,JGc_TX2_M2.Hash021.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast021_0,tail021]
#print axioms numeric021
theorem hash021 : JFp_SHADigest.digest input021=value021 := by
  unfold input021 JFp_SHADigest.digest
  rw [numeric021,JGc_TX2_M2.Hash021.checked]
  rfl
#print axioms hash021
theorem address021 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [207,200,114,194,162,182,132,95,139,30,146,76,248,10,99,254,120,31,186,252,216,6,248,218,164,72,140,229,225,96,197,172]) value006)=input021 := by rfl
#print axioms address021
def tree021 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [207,200,114,194,162,182,132,95,139,30,146,76,248,10,99,254,120,31,186,252,216,6,248,218,164,72,140,229,225,96,197,172])) tree006
theorem root021 : root JFp_SHADigest.digest tree021=value021 := by
  rw [tree021,root,root006]
  exact (congrArg JFp_SHADigest.digest address021).trans hash021
#print axioms root021
theorem shape021 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 44904=tree021 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 44904)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 44904 (by decide),siblings 0 (by decide) 44904 (by decide)]
  rw [shape006 f g inputs siblings]
  rfl
#print axioms shape021
def input022 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash022.message
def value022 : State := JFp_SHADigest.output JGc_TX2_M2.Hash022.result
theorem cast022_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash022.B00.input).map Fin.val=JGc_TX2_M2.Hash022.B00.input := by rfl
#print axioms cast022_0
theorem tail022 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash022.tail).map Fin.val=JGc_TX2_M2.Hash022.tail := by rfl
#print axioms tail022
theorem numeric022 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash022.message).map Fin.val=JGc_TX2_M2.Hash022.message := by
  simp only [JGc_TX2_M2.Hash022.message,JGc_TX2_M2.Hash022.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast022_0,tail022]
#print axioms numeric022
theorem hash022 : JFp_SHADigest.digest input022=value022 := by
  unfold input022 JFp_SHADigest.digest
  rw [numeric022,JGc_TX2_M2.Hash022.checked]
  rfl
#print axioms hash022
theorem address022 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [137,99,107,18,169,45,222,24,73,144,225,85,91,158,85,207,72,231,75,12,43,227,13,154,148,173,9,148,72,91,118,2]) value010)=input022 := by rfl
#print axioms address022
def tree022 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [137,99,107,18,169,45,222,24,73,144,225,85,91,158,85,207,72,231,75,12,43,227,13,154,148,173,9,148,72,91,118,2])) tree010
theorem root022 : root JFp_SHADigest.digest tree022=value022 := by
  rw [tree022,root,root010]
  exact (congrArg JFp_SHADigest.digest address022).trans hash022
#print axioms root022
theorem shape022 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 46408=tree022 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 46408)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 46408 (by decide),siblings 0 (by decide) 46408 (by decide)]
  rw [shape010 f g inputs siblings]
  rfl
#print axioms shape022
def input023 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash023.message
def value023 : State := JFp_SHADigest.output JGc_TX2_M2.Hash023.result
theorem cast023_0 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash023.B00.input).map Fin.val=JGc_TX2_M2.Hash023.B00.input := by rfl
#print axioms cast023_0
theorem tail023 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash023.tail).map Fin.val=JGc_TX2_M2.Hash023.tail := by rfl
#print axioms tail023
theorem numeric023 : (JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash023.message).map Fin.val=JGc_TX2_M2.Hash023.message := by
  simp only [JGc_TX2_M2.Hash023.message,JGc_TX2_M2.Hash023.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast023_0,tail023]
#print axioms numeric023
theorem hash023 : JFp_SHADigest.digest input023=value023 := by
  unfold input023 JFp_SHADigest.digest
  rw [numeric023,JGc_TX2_M2.Hash023.checked]
  rfl
#print axioms hash023
theorem address023 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [124,137,204,195,124,113,235,235,140,242,116,138,230,76,164,180,59,56,147,87,155,122,8,52,130,60,115,106,208,65,41,180]) value001)=input023 := by rfl
#print axioms address023
def tree023 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [124,137,204,195,124,113,235,235,140,242,116,138,230,76,164,180,59,56,147,87,155,122,8,52,130,60,115,106,208,65,41,180])) tree001
theorem root023 : root JFp_SHADigest.digest tree023=value023 := by
  rw [tree023,root,root001]
  exact (congrArg JFp_SHADigest.digest address023).trans hash023
#print axioms root023
theorem shape023 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 54522=tree023 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 54522)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 54522 (by decide),siblings 0 (by decide) 54522 (by decide)]
  rw [shape001 f g inputs siblings]
  rfl
#print axioms shape023
end AspisR1.JGc_TX2_M2Roots
end
