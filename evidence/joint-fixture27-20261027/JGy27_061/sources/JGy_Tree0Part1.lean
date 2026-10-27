import JGy_Tree0Part0
import JGy_Certs0_03
import JGy_Certs0_04
import JGy_Certs0_05
import JGy_Certs0_06
import JGy_Certs0_07
import JGy_Certs0_08
import JGy_Certs0_09
import JGy_Certs0_10
import JGy_Certs0_11
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input010 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash010.message
def value010 : State := JFp_SHADigest.output JGy_Gr_M0.Hash010.result
theorem cast010_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash010.B00.input).map Fin.val=JGy_Gr_M0.Hash010.B00.input := by rfl
#print axioms cast010_0
theorem tail010 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash010.tail).map Fin.val=JGy_Gr_M0.Hash010.tail := by rfl
#print axioms tail010
theorem numeric010 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash010.message).map Fin.val=JGy_Gr_M0.Hash010.message := by
  simp only [JGy_Gr_M0.Hash010.message,JGy_Gr_M0.Hash010.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast010_0,tail010]
#print axioms numeric010
theorem hash010 : JFp_SHADigest.digest input010=value010 := by
  unfold input010 JFp_SHADigest.digest
  rw [numeric010,JGy_Gr_M0.Hash010.checked]
  rfl
#print axioms hash010
theorem address010 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [138,12,78,4,29,195,175,124,49,12,183,253,137,178,1,172,57,105,147,139,13,27,199,21,103,254,125,5,89,218,213,42]) value006)=input010 := by rfl
#print axioms address010
def tree010 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [138,12,78,4,29,195,175,124,49,12,183,253,137,178,1,172,57,105,147,139,13,27,199,21,103,254,125,5,89,218,213,42])) tree006
theorem root010 : root JFp_SHADigest.digest tree010=value010 := by
  rw [tree010,root,root006]
  exact (congrArg JFp_SHADigest.digest address010).trans hash010
#print axioms root010
theorem shape010 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 65592=tree010 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 65592)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 65592 (by decide),siblings 0 (by decide) 65592 (by decide)]
  rw [shape006 f g inputs siblings]
  rfl
#print axioms shape010
def input011 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash011.message
def value011 : State := JFp_SHADigest.output JGy_Gr_M0.Hash011.result
theorem cast011_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash011.B00.input).map Fin.val=JGy_Gr_M0.Hash011.B00.input := by rfl
#print axioms cast011_0
theorem tail011 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash011.tail).map Fin.val=JGy_Gr_M0.Hash011.tail := by rfl
#print axioms tail011
theorem numeric011 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash011.message).map Fin.val=JGy_Gr_M0.Hash011.message := by
  simp only [JGy_Gr_M0.Hash011.message,JGy_Gr_M0.Hash011.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast011_0,tail011]
#print axioms numeric011
theorem hash011 : JFp_SHADigest.digest input011=value011 := by
  unfold input011 JFp_SHADigest.digest
  rw [numeric011,JGy_Gr_M0.Hash011.checked]
  rfl
#print axioms hash011
theorem address011 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [0,155,210,135,10,10,36,139,250,61,153,156,199,68,178,96,3,25,83,60,150,7,110,64,212,120,34,32,128,70,85,4]) value000)=input011 := by rfl
#print axioms address011
def tree011 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [0,155,210,135,10,10,36,139,250,61,153,156,199,68,178,96,3,25,83,60,150,7,110,64,212,120,34,32,128,70,85,4])) tree000
theorem root011 : root JFp_SHADigest.digest tree011=value011 := by
  rw [tree011,root,root000]
  exact (congrArg JFp_SHADigest.digest address011).trans hash011
#print axioms root011
theorem shape011 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 93498=tree011 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 93498)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 93498 (by decide),siblings 0 (by decide) 93498 (by decide)]
  rw [shape000 f g inputs siblings]
  rfl
#print axioms shape011
def input012 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash012.message
def value012 : State := JFp_SHADigest.output JGy_Gr_M0.Hash012.result
theorem cast012_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash012.B00.input).map Fin.val=JGy_Gr_M0.Hash012.B00.input := by rfl
#print axioms cast012_0
theorem tail012 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash012.tail).map Fin.val=JGy_Gr_M0.Hash012.tail := by rfl
#print axioms tail012
theorem numeric012 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash012.message).map Fin.val=JGy_Gr_M0.Hash012.message := by
  simp only [JGy_Gr_M0.Hash012.message,JGy_Gr_M0.Hash012.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast012_0,tail012]
#print axioms numeric012
theorem hash012 : JFp_SHADigest.digest input012=value012 := by
  unfold input012 JFp_SHADigest.digest
  rw [numeric012,JGy_Gr_M0.Hash012.checked]
  rfl
#print axioms hash012
theorem address012 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [30,206,97,181,53,81,203,161,54,188,202,14,118,67,232,27,234,26,123,152,61,193,146,253,243,71,30,207,164,232,190,24]) value001)=input012 := by rfl
#print axioms address012
def tree012 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [30,206,97,181,53,81,203,161,54,188,202,14,118,67,232,27,234,26,123,152,61,193,146,253,243,71,30,207,164,232,190,24])) tree001
theorem root012 : root JFp_SHADigest.digest tree012=value012 := by
  rw [tree012,root,root001]
  exact (congrArg JFp_SHADigest.digest address012).trans hash012
#print axioms root012
theorem shape012 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 147528=tree012 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 147528)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 147528 (by decide),siblings 0 (by decide) 147528 (by decide)]
  rw [shape001 f g inputs siblings]
  rfl
#print axioms shape012
def input013 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash013.message
def value013 : State := JFp_SHADigest.output JGy_Gr_M0.Hash013.result
theorem cast013_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash013.B00.input).map Fin.val=JGy_Gr_M0.Hash013.B00.input := by rfl
#print axioms cast013_0
theorem tail013 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash013.tail).map Fin.val=JGy_Gr_M0.Hash013.tail := by rfl
#print axioms tail013
theorem numeric013 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash013.message).map Fin.val=JGy_Gr_M0.Hash013.message := by
  simp only [JGy_Gr_M0.Hash013.message,JGy_Gr_M0.Hash013.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast013_0,tail013]
#print axioms numeric013
theorem hash013 : JFp_SHADigest.digest input013=value013 := by
  unfold input013 JFp_SHADigest.digest
  rw [numeric013,JGy_Gr_M0.Hash013.checked]
  rfl
#print axioms hash013
theorem address013 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [26,195,186,240,93,5,49,188,135,179,131,176,52,102,146,74,221,99,76,219,108,88,144,61,125,193,25,38,125,58,141,31]) value009)=input013 := by rfl
#print axioms address013
def tree013 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [26,195,186,240,93,5,49,188,135,179,131,176,52,102,146,74,221,99,76,219,108,88,144,61,125,193,25,38,125,58,141,31])) tree009
theorem root013 : root JFp_SHADigest.digest tree013=value013 := by
  rw [tree013,root,root009]
  exact (congrArg JFp_SHADigest.digest address013).trans hash013
#print axioms root013
theorem shape013 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 159812=tree013 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 159812)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 159812 (by decide),siblings 0 (by decide) 159812 (by decide)]
  rw [shape009 f g inputs siblings]
  rfl
#print axioms shape013
def input014 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash014.message
def value014 : State := JFp_SHADigest.output JGy_Gr_M0.Hash014.result
theorem cast014_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash014.B00.input).map Fin.val=JGy_Gr_M0.Hash014.B00.input := by rfl
#print axioms cast014_0
theorem tail014 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash014.tail).map Fin.val=JGy_Gr_M0.Hash014.tail := by rfl
#print axioms tail014
theorem numeric014 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash014.message).map Fin.val=JGy_Gr_M0.Hash014.message := by
  simp only [JGy_Gr_M0.Hash014.message,JGy_Gr_M0.Hash014.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast014_0,tail014]
#print axioms numeric014
theorem hash014 : JFp_SHADigest.digest input014=value014 := by
  unfold input014 JFp_SHADigest.digest
  rw [numeric014,JGy_Gr_M0.Hash014.checked]
  rfl
#print axioms hash014
theorem address014 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [40,252,149,36,166,192,162,64,101,20,54,49,63,59,166,85,31,38,36,0,99,178,228,189,116,169,252,141,90,193,181,51]) value007)=input014 := by rfl
#print axioms address014
def tree014 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [40,252,149,36,166,192,162,64,101,20,54,49,63,59,166,85,31,38,36,0,99,178,228,189,116,169,252,141,90,193,181,51])) tree007
theorem root014 : root JFp_SHADigest.digest tree014=value014 := by
  rw [tree014,root,root007]
  exact (congrArg JFp_SHADigest.digest address014).trans hash014
#print axioms root014
theorem shape014 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 183858=tree014 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 183858)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 183858 (by decide),siblings 0 (by decide) 183858 (by decide)]
  rw [shape007 f g inputs siblings]
  rfl
#print axioms shape014
def input015 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash015.message
def value015 : State := JFp_SHADigest.output JGy_Gr_M0.Hash015.result
theorem cast015_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash015.B00.input).map Fin.val=JGy_Gr_M0.Hash015.B00.input := by rfl
#print axioms cast015_0
theorem tail015 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash015.tail).map Fin.val=JGy_Gr_M0.Hash015.tail := by rfl
#print axioms tail015
theorem numeric015 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash015.message).map Fin.val=JGy_Gr_M0.Hash015.message := by
  simp only [JGy_Gr_M0.Hash015.message,JGy_Gr_M0.Hash015.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast015_0,tail015]
#print axioms numeric015
theorem hash015 : JFp_SHADigest.digest input015=value015 := by
  unfold input015 JFp_SHADigest.digest
  rw [numeric015,JGy_Gr_M0.Hash015.checked]
  rfl
#print axioms hash015
theorem address015 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [197,135,76,25,172,180,98,84,70,211,112,237,137,36,20,194,104,104,114,136,240,147,181,141,121,72,73,200,110,2,159,172]) value005)=input015 := by rfl
#print axioms address015
def tree015 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [197,135,76,25,172,180,98,84,70,211,112,237,137,36,20,194,104,104,114,136,240,147,181,141,121,72,73,200,110,2,159,172])) tree005
theorem root015 : root JFp_SHADigest.digest tree015=value015 := by
  rw [tree015,root,root005]
  exact (congrArg JFp_SHADigest.digest address015).trans hash015
#print axioms root015
theorem shape015 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 192316=tree015 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 192316)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 192316 (by decide),siblings 0 (by decide) 192316 (by decide)]
  rw [shape005 f g inputs siblings]
  rfl
#print axioms shape015
def input016 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash016.message
def value016 : State := JFp_SHADigest.output JGy_Gr_M0.Hash016.result
theorem cast016_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash016.B00.input).map Fin.val=JGy_Gr_M0.Hash016.B00.input := by rfl
#print axioms cast016_0
theorem tail016 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash016.tail).map Fin.val=JGy_Gr_M0.Hash016.tail := by rfl
#print axioms tail016
theorem numeric016 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash016.message).map Fin.val=JGy_Gr_M0.Hash016.message := by
  simp only [JGy_Gr_M0.Hash016.message,JGy_Gr_M0.Hash016.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast016_0,tail016]
#print axioms numeric016
theorem hash016 : JFp_SHADigest.digest input016=value016 := by
  unfold input016 JFp_SHADigest.digest
  rw [numeric016,JGy_Gr_M0.Hash016.checked]
  rfl
#print axioms hash016
theorem address016 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [221,112,50,50,72,39,34,4,52,173,152,99,96,65,187,155,71,131,8,35,206,215,205,144,48,160,238,66,13,85,203,152]) value008)=input016 := by rfl
#print axioms address016
def tree016 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [221,112,50,50,72,39,34,4,52,173,152,99,96,65,187,155,71,131,8,35,206,215,205,144,48,160,238,66,13,85,203,152])) tree008
theorem root016 : root JFp_SHADigest.digest tree016=value016 := by
  rw [tree016,root,root008]
  exact (congrArg JFp_SHADigest.digest address016).trans hash016
#print axioms root016
theorem shape016 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 193092=tree016 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 193092)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 193092 (by decide),siblings 0 (by decide) 193092 (by decide)]
  rw [shape008 f g inputs siblings]
  rfl
#print axioms shape016
def input017 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash017.message
def value017 : State := JFp_SHADigest.output JGy_Gr_M0.Hash017.result
theorem cast017_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash017.B00.input).map Fin.val=JGy_Gr_M0.Hash017.B00.input := by rfl
#print axioms cast017_0
theorem tail017 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash017.tail).map Fin.val=JGy_Gr_M0.Hash017.tail := by rfl
#print axioms tail017
theorem numeric017 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash017.message).map Fin.val=JGy_Gr_M0.Hash017.message := by
  simp only [JGy_Gr_M0.Hash017.message,JGy_Gr_M0.Hash017.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast017_0,tail017]
#print axioms numeric017
theorem hash017 : JFp_SHADigest.digest input017=value017 := by
  unfold input017 JFp_SHADigest.digest
  rw [numeric017,JGy_Gr_M0.Hash017.checked]
  rfl
#print axioms hash017
theorem address017 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [98,52,222,92,145,216,45,125,153,221,152,251,15,144,137,56,230,174,11,161,151,249,216,185,201,144,36,136,166,73,211,28]) value004)=input017 := by rfl
#print axioms address017
def tree017 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [98,52,222,92,145,216,45,125,153,221,152,251,15,144,137,56,230,174,11,161,151,249,216,185,201,144,36,136,166,73,211,28])) tree004
theorem root017 : root JFp_SHADigest.digest tree017=value017 := by
  rw [tree017,root,root004]
  exact (congrArg JFp_SHADigest.digest address017).trans hash017
#print axioms root017
theorem shape017 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 209370=tree017 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 209370)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 209370 (by decide),siblings 0 (by decide) 209370 (by decide)]
  rw [shape004 f g inputs siblings]
  rfl
#print axioms shape017
def input018 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash018.message
def value018 : State := JFp_SHADigest.output JGy_Gr_M0.Hash018.result
theorem cast018_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash018.B00.input).map Fin.val=JGy_Gr_M0.Hash018.B00.input := by rfl
#print axioms cast018_0
theorem tail018 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash018.tail).map Fin.val=JGy_Gr_M0.Hash018.tail := by rfl
#print axioms tail018
theorem numeric018 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash018.message).map Fin.val=JGy_Gr_M0.Hash018.message := by
  simp only [JGy_Gr_M0.Hash018.message,JGy_Gr_M0.Hash018.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast018_0,tail018]
#print axioms numeric018
theorem hash018 : JFp_SHADigest.digest input018=value018 := by
  unfold input018 JFp_SHADigest.digest
  rw [numeric018,JGy_Gr_M0.Hash018.checked]
  rfl
#print axioms hash018
theorem address018 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [60,239,18,111,191,102,204,179,135,84,19,39,39,192,93,82,21,159,129,98,135,224,200,173,184,187,89,90,164,245,183,28]) value002)=input018 := by rfl
#print axioms address018
def tree018 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [60,239,18,111,191,102,204,179,135,84,19,39,39,192,93,82,21,159,129,98,135,224,200,173,184,187,89,90,164,245,183,28])) tree002
theorem root018 : root JFp_SHADigest.digest tree018=value018 := by
  rw [tree018,root,root002]
  exact (congrArg JFp_SHADigest.digest address018).trans hash018
#print axioms root018
theorem shape018 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 216822=tree018 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 216822)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 216822 (by decide),siblings 0 (by decide) 216822 (by decide)]
  rw [shape002 f g inputs siblings]
  rfl
#print axioms shape018
def input019 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash019.message
def value019 : State := JFp_SHADigest.output JGy_Gr_M0.Hash019.result
theorem cast019_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash019.B00.input).map Fin.val=JGy_Gr_M0.Hash019.B00.input := by rfl
#print axioms cast019_0
theorem tail019 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash019.tail).map Fin.val=JGy_Gr_M0.Hash019.tail := by rfl
#print axioms tail019
theorem numeric019 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash019.message).map Fin.val=JGy_Gr_M0.Hash019.message := by
  simp only [JGy_Gr_M0.Hash019.message,JGy_Gr_M0.Hash019.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast019_0,tail019]
#print axioms numeric019
theorem hash019 : JFp_SHADigest.digest input019=value019 := by
  unfold input019 JFp_SHADigest.digest
  rw [numeric019,JGy_Gr_M0.Hash019.checked]
  rfl
#print axioms hash019
theorem address019 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [2,236,210,68,67,97,179,9,220,150,3,95,165,1,185,29,159,221,4,51,208,1,32,211,224,128,53,137,65,4,60,189]) value003)=input019 := by rfl
#print axioms address019
def tree019 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [2,236,210,68,67,97,179,9,220,150,3,95,165,1,185,29,159,221,4,51,208,1,32,211,224,128,53,137,65,4,60,189])) tree003
theorem root019 : root JFp_SHADigest.digest tree019=value019 := by
  rw [tree019,root,root003]
  exact (congrArg JFp_SHADigest.digest address019).trans hash019
#print axioms root019
theorem shape019 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 245898=tree019 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 245898)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 245898 (by decide),siblings 0 (by decide) 245898 (by decide)]
  rw [shape003 f g inputs siblings]
  rfl
#print axioms shape019
end AspisR1.JGy_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input020 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash020.message
def value020 : State := JFp_SHADigest.output JGy_Gr_M0.Hash020.result
theorem cast020_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash020.B00.input).map Fin.val=JGy_Gr_M0.Hash020.B00.input := by rfl
#print axioms cast020_0
theorem tail020 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash020.tail).map Fin.val=JGy_Gr_M0.Hash020.tail := by rfl
#print axioms tail020
theorem numeric020 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash020.message).map Fin.val=JGy_Gr_M0.Hash020.message := by
  simp only [JGy_Gr_M0.Hash020.message,JGy_Gr_M0.Hash020.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast020_0,tail020]
#print axioms numeric020
theorem hash020 : JFp_SHADigest.digest input020=value020 := by
  unfold input020 JFp_SHADigest.digest
  rw [numeric020,JGy_Gr_M0.Hash020.checked]
  rfl
#print axioms hash020
theorem address020 : BinMerkle32Path.nodeInput (children value010 (JGc_TX2_HashBytes.state [129,145,123,71,112,75,255,207,218,182,51,10,70,248,80,186,22,215,227,161,95,73,153,136,175,88,40,150,245,11,93,135]))=input020 := by rfl
#print axioms address020
def tree020 : Tree := .branch tree010 (.supplied (JGc_TX2_HashBytes.state [129,145,123,71,112,75,255,207,218,182,51,10,70,248,80,186,22,215,227,161,95,73,153,136,175,88,40,150,245,11,93,135]))
theorem root020 : root JFp_SHADigest.digest tree020=value020 := by
  rw [tree020,root,root010]
  exact (congrArg JFp_SHADigest.digest address020).trans hash020
#print axioms root020
theorem shape020 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 65592=tree020 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 65592)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape010 f g inputs siblings]
  rw [unoccupied f g 1 65594 (by decide),siblings 1 (by decide) 65594 (by decide)]
  rfl
#print axioms shape020
def input021 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash021.message
def value021 : State := JFp_SHADigest.output JGy_Gr_M0.Hash021.result
theorem cast021_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash021.B00.input).map Fin.val=JGy_Gr_M0.Hash021.B00.input := by rfl
#print axioms cast021_0
theorem tail021 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash021.tail).map Fin.val=JGy_Gr_M0.Hash021.tail := by rfl
#print axioms tail021
theorem numeric021 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash021.message).map Fin.val=JGy_Gr_M0.Hash021.message := by
  simp only [JGy_Gr_M0.Hash021.message,JGy_Gr_M0.Hash021.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast021_0,tail021]
#print axioms numeric021
theorem hash021 : JFp_SHADigest.digest input021=value021 := by
  unfold input021 JFp_SHADigest.digest
  rw [numeric021,JGy_Gr_M0.Hash021.checked]
  rfl
#print axioms hash021
theorem address021 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [6,77,240,190,14,215,62,129,49,91,41,245,106,187,182,190,199,41,143,109,39,181,18,239,169,207,77,190,62,185,232,101]) value011)=input021 := by rfl
#print axioms address021
def tree021 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [6,77,240,190,14,215,62,129,49,91,41,245,106,187,182,190,199,41,143,109,39,181,18,239,169,207,77,190,62,185,232,101])) tree011
theorem root021 : root JFp_SHADigest.digest tree021=value021 := by
  rw [tree021,root,root011]
  exact (congrArg JFp_SHADigest.digest address021).trans hash021
#print axioms root021
theorem shape021 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 93496=tree021 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 93496)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 93496 (by decide),siblings 1 (by decide) 93496 (by decide)]
  rw [shape011 f g inputs siblings]
  rfl
#print axioms shape021
def input022 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash022.message
def value022 : State := JFp_SHADigest.output JGy_Gr_M0.Hash022.result
theorem cast022_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash022.B00.input).map Fin.val=JGy_Gr_M0.Hash022.B00.input := by rfl
#print axioms cast022_0
theorem tail022 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash022.tail).map Fin.val=JGy_Gr_M0.Hash022.tail := by rfl
#print axioms tail022
theorem numeric022 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash022.message).map Fin.val=JGy_Gr_M0.Hash022.message := by
  simp only [JGy_Gr_M0.Hash022.message,JGy_Gr_M0.Hash022.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast022_0,tail022]
#print axioms numeric022
theorem hash022 : JFp_SHADigest.digest input022=value022 := by
  unfold input022 JFp_SHADigest.digest
  rw [numeric022,JGy_Gr_M0.Hash022.checked]
  rfl
#print axioms hash022
theorem address022 : BinMerkle32Path.nodeInput (children value012 (JGc_TX2_HashBytes.state [171,86,16,208,136,220,221,143,53,10,68,139,211,174,170,254,152,13,118,166,208,178,197,65,145,118,216,18,233,52,60,82]))=input022 := by rfl
#print axioms address022
def tree022 : Tree := .branch tree012 (.supplied (JGc_TX2_HashBytes.state [171,86,16,208,136,220,221,143,53,10,68,139,211,174,170,254,152,13,118,166,208,178,197,65,145,118,216,18,233,52,60,82]))
theorem root022 : root JFp_SHADigest.digest tree022=value022 := by
  rw [tree022,root,root012]
  exact (congrArg JFp_SHADigest.digest address022).trans hash022
#print axioms root022
theorem shape022 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 147528=tree022 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 147528)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape012 f g inputs siblings]
  rw [unoccupied f g 1 147530 (by decide),siblings 1 (by decide) 147530 (by decide)]
  rfl
#print axioms shape022
def input023 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash023.message
def value023 : State := JFp_SHADigest.output JGy_Gr_M0.Hash023.result
theorem cast023_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash023.B00.input).map Fin.val=JGy_Gr_M0.Hash023.B00.input := by rfl
#print axioms cast023_0
theorem tail023 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash023.tail).map Fin.val=JGy_Gr_M0.Hash023.tail := by rfl
#print axioms tail023
theorem numeric023 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash023.message).map Fin.val=JGy_Gr_M0.Hash023.message := by
  simp only [JGy_Gr_M0.Hash023.message,JGy_Gr_M0.Hash023.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast023_0,tail023]
#print axioms numeric023
theorem hash023 : JFp_SHADigest.digest input023=value023 := by
  unfold input023 JFp_SHADigest.digest
  rw [numeric023,JGy_Gr_M0.Hash023.checked]
  rfl
#print axioms hash023
theorem address023 : BinMerkle32Path.nodeInput (children value013 (JGc_TX2_HashBytes.state [248,126,21,210,211,142,137,180,125,82,222,125,142,123,90,165,35,12,113,99,134,20,208,119,121,59,66,164,58,120,127,115]))=input023 := by rfl
#print axioms address023
def tree023 : Tree := .branch tree013 (.supplied (JGc_TX2_HashBytes.state [248,126,21,210,211,142,137,180,125,82,222,125,142,123,90,165,35,12,113,99,134,20,208,119,121,59,66,164,58,120,127,115]))
theorem root023 : root JFp_SHADigest.digest tree023=value023 := by
  rw [tree023,root,root013]
  exact (congrArg JFp_SHADigest.digest address023).trans hash023
#print axioms root023
theorem shape023 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 159812=tree023 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 159812)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape013 f g inputs siblings]
  rw [unoccupied f g 1 159814 (by decide),siblings 1 (by decide) 159814 (by decide)]
  rfl
#print axioms shape023
def input024 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash024.message
def value024 : State := JFp_SHADigest.output JGy_Gr_M0.Hash024.result
theorem cast024_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash024.B00.input).map Fin.val=JGy_Gr_M0.Hash024.B00.input := by rfl
#print axioms cast024_0
theorem tail024 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash024.tail).map Fin.val=JGy_Gr_M0.Hash024.tail := by rfl
#print axioms tail024
theorem numeric024 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash024.message).map Fin.val=JGy_Gr_M0.Hash024.message := by
  simp only [JGy_Gr_M0.Hash024.message,JGy_Gr_M0.Hash024.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast024_0,tail024]
#print axioms numeric024
theorem hash024 : JFp_SHADigest.digest input024=value024 := by
  unfold input024 JFp_SHADigest.digest
  rw [numeric024,JGy_Gr_M0.Hash024.checked]
  rfl
#print axioms hash024
theorem address024 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [20,10,255,79,9,214,152,90,126,242,155,160,41,116,223,232,3,49,161,115,34,79,44,109,72,141,100,126,207,51,141,176]) value014)=input024 := by rfl
#print axioms address024
def tree024 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [20,10,255,79,9,214,152,90,126,242,155,160,41,116,223,232,3,49,161,115,34,79,44,109,72,141,100,126,207,51,141,176])) tree014
theorem root024 : root JFp_SHADigest.digest tree024=value024 := by
  rw [tree024,root,root014]
  exact (congrArg JFp_SHADigest.digest address024).trans hash024
#print axioms root024
theorem shape024 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 183856=tree024 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 183856)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 183856 (by decide),siblings 1 (by decide) 183856 (by decide)]
  rw [shape014 f g inputs siblings]
  rfl
#print axioms shape024
def input025 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash025.message
def value025 : State := JFp_SHADigest.output JGy_Gr_M0.Hash025.result
theorem cast025_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash025.B00.input).map Fin.val=JGy_Gr_M0.Hash025.B00.input := by rfl
#print axioms cast025_0
theorem tail025 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash025.tail).map Fin.val=JGy_Gr_M0.Hash025.tail := by rfl
#print axioms tail025
theorem numeric025 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash025.message).map Fin.val=JGy_Gr_M0.Hash025.message := by
  simp only [JGy_Gr_M0.Hash025.message,JGy_Gr_M0.Hash025.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast025_0,tail025]
#print axioms numeric025
theorem hash025 : JFp_SHADigest.digest input025=value025 := by
  unfold input025 JFp_SHADigest.digest
  rw [numeric025,JGy_Gr_M0.Hash025.checked]
  rfl
#print axioms hash025
theorem address025 : BinMerkle32Path.nodeInput (children value015 (JGc_TX2_HashBytes.state [6,1,204,64,31,38,61,84,24,165,208,174,223,189,74,4,143,235,84,186,217,122,203,71,143,71,240,110,239,79,13,27]))=input025 := by rfl
#print axioms address025
def tree025 : Tree := .branch tree015 (.supplied (JGc_TX2_HashBytes.state [6,1,204,64,31,38,61,84,24,165,208,174,223,189,74,4,143,235,84,186,217,122,203,71,143,71,240,110,239,79,13,27]))
theorem root025 : root JFp_SHADigest.digest tree025=value025 := by
  rw [tree025,root,root015]
  exact (congrArg JFp_SHADigest.digest address025).trans hash025
#print axioms root025
theorem shape025 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 192316=tree025 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 192316)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape015 f g inputs siblings]
  rw [unoccupied f g 1 192318 (by decide),siblings 1 (by decide) 192318 (by decide)]
  rfl
#print axioms shape025
def input026 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash026.message
def value026 : State := JFp_SHADigest.output JGy_Gr_M0.Hash026.result
theorem cast026_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash026.B00.input).map Fin.val=JGy_Gr_M0.Hash026.B00.input := by rfl
#print axioms cast026_0
theorem tail026 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash026.tail).map Fin.val=JGy_Gr_M0.Hash026.tail := by rfl
#print axioms tail026
theorem numeric026 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash026.message).map Fin.val=JGy_Gr_M0.Hash026.message := by
  simp only [JGy_Gr_M0.Hash026.message,JGy_Gr_M0.Hash026.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast026_0,tail026]
#print axioms numeric026
theorem hash026 : JFp_SHADigest.digest input026=value026 := by
  unfold input026 JFp_SHADigest.digest
  rw [numeric026,JGy_Gr_M0.Hash026.checked]
  rfl
#print axioms hash026
theorem address026 : BinMerkle32Path.nodeInput (children value016 (JGc_TX2_HashBytes.state [111,19,141,1,38,225,65,248,212,38,27,65,9,175,117,232,105,8,170,194,129,33,180,80,1,242,239,11,227,222,81,248]))=input026 := by rfl
#print axioms address026
def tree026 : Tree := .branch tree016 (.supplied (JGc_TX2_HashBytes.state [111,19,141,1,38,225,65,248,212,38,27,65,9,175,117,232,105,8,170,194,129,33,180,80,1,242,239,11,227,222,81,248]))
theorem root026 : root JFp_SHADigest.digest tree026=value026 := by
  rw [tree026,root,root016]
  exact (congrArg JFp_SHADigest.digest address026).trans hash026
#print axioms root026
theorem shape026 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 193092=tree026 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 193092)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape016 f g inputs siblings]
  rw [unoccupied f g 1 193094 (by decide),siblings 1 (by decide) 193094 (by decide)]
  rfl
#print axioms shape026
def input027 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash027.message
def value027 : State := JFp_SHADigest.output JGy_Gr_M0.Hash027.result
theorem cast027_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash027.B00.input).map Fin.val=JGy_Gr_M0.Hash027.B00.input := by rfl
#print axioms cast027_0
theorem tail027 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash027.tail).map Fin.val=JGy_Gr_M0.Hash027.tail := by rfl
#print axioms tail027
theorem numeric027 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash027.message).map Fin.val=JGy_Gr_M0.Hash027.message := by
  simp only [JGy_Gr_M0.Hash027.message,JGy_Gr_M0.Hash027.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast027_0,tail027]
#print axioms numeric027
theorem hash027 : JFp_SHADigest.digest input027=value027 := by
  unfold input027 JFp_SHADigest.digest
  rw [numeric027,JGy_Gr_M0.Hash027.checked]
  rfl
#print axioms hash027
theorem address027 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [17,75,22,191,103,116,8,247,251,193,12,81,68,91,193,167,193,237,72,81,121,112,92,183,215,119,32,4,8,7,113,34]) value017)=input027 := by rfl
#print axioms address027
def tree027 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [17,75,22,191,103,116,8,247,251,193,12,81,68,91,193,167,193,237,72,81,121,112,92,183,215,119,32,4,8,7,113,34])) tree017
theorem root027 : root JFp_SHADigest.digest tree027=value027 := by
  rw [tree027,root,root017]
  exact (congrArg JFp_SHADigest.digest address027).trans hash027
#print axioms root027
theorem shape027 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 209368=tree027 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 209368)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 209368 (by decide),siblings 1 (by decide) 209368 (by decide)]
  rw [shape017 f g inputs siblings]
  rfl
#print axioms shape027
def input028 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash028.message
def value028 : State := JFp_SHADigest.output JGy_Gr_M0.Hash028.result
theorem cast028_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash028.B00.input).map Fin.val=JGy_Gr_M0.Hash028.B00.input := by rfl
#print axioms cast028_0
theorem tail028 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash028.tail).map Fin.val=JGy_Gr_M0.Hash028.tail := by rfl
#print axioms tail028
theorem numeric028 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash028.message).map Fin.val=JGy_Gr_M0.Hash028.message := by
  simp only [JGy_Gr_M0.Hash028.message,JGy_Gr_M0.Hash028.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast028_0,tail028]
#print axioms numeric028
theorem hash028 : JFp_SHADigest.digest input028=value028 := by
  unfold input028 JFp_SHADigest.digest
  rw [numeric028,JGy_Gr_M0.Hash028.checked]
  rfl
#print axioms hash028
theorem address028 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [198,203,234,73,173,119,179,225,134,57,111,62,249,250,244,3,81,81,144,231,109,135,167,231,203,175,0,17,199,209,221,204]) value018)=input028 := by rfl
#print axioms address028
def tree028 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [198,203,234,73,173,119,179,225,134,57,111,62,249,250,244,3,81,81,144,231,109,135,167,231,203,175,0,17,199,209,221,204])) tree018
theorem root028 : root JFp_SHADigest.digest tree028=value028 := by
  rw [tree028,root,root018]
  exact (congrArg JFp_SHADigest.digest address028).trans hash028
#print axioms root028
theorem shape028 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 216820=tree028 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 216820)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 216820 (by decide),siblings 1 (by decide) 216820 (by decide)]
  rw [shape018 f g inputs siblings]
  rfl
#print axioms shape028
def input029 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash029.message
def value029 : State := JFp_SHADigest.output JGy_Gr_M0.Hash029.result
theorem cast029_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash029.B00.input).map Fin.val=JGy_Gr_M0.Hash029.B00.input := by rfl
#print axioms cast029_0
theorem tail029 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash029.tail).map Fin.val=JGy_Gr_M0.Hash029.tail := by rfl
#print axioms tail029
theorem numeric029 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash029.message).map Fin.val=JGy_Gr_M0.Hash029.message := by
  simp only [JGy_Gr_M0.Hash029.message,JGy_Gr_M0.Hash029.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast029_0,tail029]
#print axioms numeric029
theorem hash029 : JFp_SHADigest.digest input029=value029 := by
  unfold input029 JFp_SHADigest.digest
  rw [numeric029,JGy_Gr_M0.Hash029.checked]
  rfl
#print axioms hash029
theorem address029 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [250,169,77,120,228,7,6,220,115,87,209,195,16,51,10,191,223,81,107,87,210,1,161,60,20,21,81,135,25,24,132,100]) value019)=input029 := by rfl
#print axioms address029
def tree029 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [250,169,77,120,228,7,6,220,115,87,209,195,16,51,10,191,223,81,107,87,210,1,161,60,20,21,81,135,25,24,132,100])) tree019
theorem root029 : root JFp_SHADigest.digest tree029=value029 := by
  rw [tree029,root,root019]
  exact (congrArg JFp_SHADigest.digest address029).trans hash029
#print axioms root029
theorem shape029 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 245896=tree029 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 245896)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 245896 (by decide),siblings 1 (by decide) 245896 (by decide)]
  rw [shape019 f g inputs siblings]
  rfl
#print axioms shape029
end AspisR1.JGy_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input030 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash030.message
def value030 : State := JFp_SHADigest.output JGy_Gr_M0.Hash030.result
theorem cast030_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash030.B00.input).map Fin.val=JGy_Gr_M0.Hash030.B00.input := by rfl
#print axioms cast030_0
theorem tail030 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash030.tail).map Fin.val=JGy_Gr_M0.Hash030.tail := by rfl
#print axioms tail030
theorem numeric030 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash030.message).map Fin.val=JGy_Gr_M0.Hash030.message := by
  simp only [JGy_Gr_M0.Hash030.message,JGy_Gr_M0.Hash030.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast030_0,tail030]
#print axioms numeric030
theorem hash030 : JFp_SHADigest.digest input030=value030 := by
  unfold input030 JFp_SHADigest.digest
  rw [numeric030,JGy_Gr_M0.Hash030.checked]
  rfl
#print axioms hash030
theorem address030 : BinMerkle32Path.nodeInput (children value020 (JGc_TX2_HashBytes.state [113,228,45,241,12,21,223,82,189,127,50,66,112,86,41,131,49,39,172,121,205,231,86,254,118,88,129,50,88,205,75,198]))=input030 := by rfl
#print axioms address030
def tree030 : Tree := .branch tree020 (.supplied (JGc_TX2_HashBytes.state [113,228,45,241,12,21,223,82,189,127,50,66,112,86,41,131,49,39,172,121,205,231,86,254,118,88,129,50,88,205,75,198]))
theorem root030 : root JFp_SHADigest.digest tree030=value030 := by
  rw [tree030,root,root020]
  exact (congrArg JFp_SHADigest.digest address030).trans hash030
#print axioms root030
theorem shape030 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 65592=tree030 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 65592)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape020 f g inputs siblings]
  rw [unoccupied f g 2 65596 (by decide),siblings 2 (by decide) 65596 (by decide)]
  rfl
#print axioms shape030
def input031 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash031.message
def value031 : State := JFp_SHADigest.output JGy_Gr_M0.Hash031.result
theorem cast031_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash031.B00.input).map Fin.val=JGy_Gr_M0.Hash031.B00.input := by rfl
#print axioms cast031_0
theorem tail031 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash031.tail).map Fin.val=JGy_Gr_M0.Hash031.tail := by rfl
#print axioms tail031
theorem numeric031 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash031.message).map Fin.val=JGy_Gr_M0.Hash031.message := by
  simp only [JGy_Gr_M0.Hash031.message,JGy_Gr_M0.Hash031.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast031_0,tail031]
#print axioms numeric031
theorem hash031 : JFp_SHADigest.digest input031=value031 := by
  unfold input031 JFp_SHADigest.digest
  rw [numeric031,JGy_Gr_M0.Hash031.checked]
  rfl
#print axioms hash031
theorem address031 : BinMerkle32Path.nodeInput (children value021 (JGc_TX2_HashBytes.state [170,237,127,75,233,122,51,70,203,215,35,59,216,223,49,175,17,58,145,50,79,33,120,37,250,117,78,166,106,96,202,40]))=input031 := by rfl
#print axioms address031
def tree031 : Tree := .branch tree021 (.supplied (JGc_TX2_HashBytes.state [170,237,127,75,233,122,51,70,203,215,35,59,216,223,49,175,17,58,145,50,79,33,120,37,250,117,78,166,106,96,202,40]))
theorem root031 : root JFp_SHADigest.digest tree031=value031 := by
  rw [tree031,root,root021]
  exact (congrArg JFp_SHADigest.digest address031).trans hash031
#print axioms root031
theorem shape031 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 93496=tree031 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 93496)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape021 f g inputs siblings]
  rw [unoccupied f g 2 93500 (by decide),siblings 2 (by decide) 93500 (by decide)]
  rfl
#print axioms shape031
def input032 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash032.message
def value032 : State := JFp_SHADigest.output JGy_Gr_M0.Hash032.result
theorem cast032_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash032.B00.input).map Fin.val=JGy_Gr_M0.Hash032.B00.input := by rfl
#print axioms cast032_0
theorem tail032 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash032.tail).map Fin.val=JGy_Gr_M0.Hash032.tail := by rfl
#print axioms tail032
theorem numeric032 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash032.message).map Fin.val=JGy_Gr_M0.Hash032.message := by
  simp only [JGy_Gr_M0.Hash032.message,JGy_Gr_M0.Hash032.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast032_0,tail032]
#print axioms numeric032
theorem hash032 : JFp_SHADigest.digest input032=value032 := by
  unfold input032 JFp_SHADigest.digest
  rw [numeric032,JGy_Gr_M0.Hash032.checked]
  rfl
#print axioms hash032
theorem address032 : BinMerkle32Path.nodeInput (children value022 (JGc_TX2_HashBytes.state [90,223,103,38,163,10,29,51,156,251,237,216,23,111,164,147,90,200,6,231,84,70,65,96,193,254,203,58,211,238,139,7]))=input032 := by rfl
#print axioms address032
def tree032 : Tree := .branch tree022 (.supplied (JGc_TX2_HashBytes.state [90,223,103,38,163,10,29,51,156,251,237,216,23,111,164,147,90,200,6,231,84,70,65,96,193,254,203,58,211,238,139,7]))
theorem root032 : root JFp_SHADigest.digest tree032=value032 := by
  rw [tree032,root,root022]
  exact (congrArg JFp_SHADigest.digest address032).trans hash032
#print axioms root032
theorem shape032 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 147528=tree032 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 147528)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape022 f g inputs siblings]
  rw [unoccupied f g 2 147532 (by decide),siblings 2 (by decide) 147532 (by decide)]
  rfl
#print axioms shape032
def input033 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash033.message
def value033 : State := JFp_SHADigest.output JGy_Gr_M0.Hash033.result
theorem cast033_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash033.B00.input).map Fin.val=JGy_Gr_M0.Hash033.B00.input := by rfl
#print axioms cast033_0
theorem tail033 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash033.tail).map Fin.val=JGy_Gr_M0.Hash033.tail := by rfl
#print axioms tail033
theorem numeric033 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash033.message).map Fin.val=JGy_Gr_M0.Hash033.message := by
  simp only [JGy_Gr_M0.Hash033.message,JGy_Gr_M0.Hash033.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast033_0,tail033]
#print axioms numeric033
theorem hash033 : JFp_SHADigest.digest input033=value033 := by
  unfold input033 JFp_SHADigest.digest
  rw [numeric033,JGy_Gr_M0.Hash033.checked]
  rfl
#print axioms hash033
theorem address033 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [164,239,132,46,197,102,247,125,165,37,99,49,87,147,68,162,92,105,189,105,44,74,146,27,210,103,23,0,30,154,233,18]) value023)=input033 := by rfl
#print axioms address033
def tree033 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [164,239,132,46,197,102,247,125,165,37,99,49,87,147,68,162,92,105,189,105,44,74,146,27,210,103,23,0,30,154,233,18])) tree023
theorem root033 : root JFp_SHADigest.digest tree033=value033 := by
  rw [tree033,root,root023]
  exact (congrArg JFp_SHADigest.digest address033).trans hash033
#print axioms root033
theorem shape033 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 159808=tree033 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 159808)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 159808 (by decide),siblings 2 (by decide) 159808 (by decide)]
  rw [shape023 f g inputs siblings]
  rfl
#print axioms shape033
def input034 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash034.message
def value034 : State := JFp_SHADigest.output JGy_Gr_M0.Hash034.result
theorem cast034_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash034.B00.input).map Fin.val=JGy_Gr_M0.Hash034.B00.input := by rfl
#print axioms cast034_0
theorem tail034 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash034.tail).map Fin.val=JGy_Gr_M0.Hash034.tail := by rfl
#print axioms tail034
theorem numeric034 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash034.message).map Fin.val=JGy_Gr_M0.Hash034.message := by
  simp only [JGy_Gr_M0.Hash034.message,JGy_Gr_M0.Hash034.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast034_0,tail034]
#print axioms numeric034
theorem hash034 : JFp_SHADigest.digest input034=value034 := by
  unfold input034 JFp_SHADigest.digest
  rw [numeric034,JGy_Gr_M0.Hash034.checked]
  rfl
#print axioms hash034
theorem address034 : BinMerkle32Path.nodeInput (children value024 (JGc_TX2_HashBytes.state [113,219,88,1,248,185,66,167,21,201,234,44,1,193,119,242,149,64,217,87,214,0,169,200,148,84,216,185,197,164,151,244]))=input034 := by rfl
#print axioms address034
def tree034 : Tree := .branch tree024 (.supplied (JGc_TX2_HashBytes.state [113,219,88,1,248,185,66,167,21,201,234,44,1,193,119,242,149,64,217,87,214,0,169,200,148,84,216,185,197,164,151,244]))
theorem root034 : root JFp_SHADigest.digest tree034=value034 := by
  rw [tree034,root,root024]
  exact (congrArg JFp_SHADigest.digest address034).trans hash034
#print axioms root034
theorem shape034 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 183856=tree034 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 183856)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape024 f g inputs siblings]
  rw [unoccupied f g 2 183860 (by decide),siblings 2 (by decide) 183860 (by decide)]
  rfl
#print axioms shape034
def input035 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash035.message
def value035 : State := JFp_SHADigest.output JGy_Gr_M0.Hash035.result
theorem cast035_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash035.B00.input).map Fin.val=JGy_Gr_M0.Hash035.B00.input := by rfl
#print axioms cast035_0
theorem tail035 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash035.tail).map Fin.val=JGy_Gr_M0.Hash035.tail := by rfl
#print axioms tail035
theorem numeric035 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash035.message).map Fin.val=JGy_Gr_M0.Hash035.message := by
  simp only [JGy_Gr_M0.Hash035.message,JGy_Gr_M0.Hash035.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast035_0,tail035]
#print axioms numeric035
theorem hash035 : JFp_SHADigest.digest input035=value035 := by
  unfold input035 JFp_SHADigest.digest
  rw [numeric035,JGy_Gr_M0.Hash035.checked]
  rfl
#print axioms hash035
theorem address035 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [131,150,20,119,138,171,247,50,130,133,151,200,22,17,142,182,50,103,254,31,237,67,123,106,214,235,120,126,203,58,12,15]) value025)=input035 := by rfl
#print axioms address035
def tree035 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [131,150,20,119,138,171,247,50,130,133,151,200,22,17,142,182,50,103,254,31,237,67,123,106,214,235,120,126,203,58,12,15])) tree025
theorem root035 : root JFp_SHADigest.digest tree035=value035 := by
  rw [tree035,root,root025]
  exact (congrArg JFp_SHADigest.digest address035).trans hash035
#print axioms root035
theorem shape035 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 192312=tree035 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 192312)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 192312 (by decide),siblings 2 (by decide) 192312 (by decide)]
  rw [shape025 f g inputs siblings]
  rfl
#print axioms shape035
def input036 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash036.message
def value036 : State := JFp_SHADigest.output JGy_Gr_M0.Hash036.result
theorem cast036_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash036.B00.input).map Fin.val=JGy_Gr_M0.Hash036.B00.input := by rfl
#print axioms cast036_0
theorem tail036 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash036.tail).map Fin.val=JGy_Gr_M0.Hash036.tail := by rfl
#print axioms tail036
theorem numeric036 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash036.message).map Fin.val=JGy_Gr_M0.Hash036.message := by
  simp only [JGy_Gr_M0.Hash036.message,JGy_Gr_M0.Hash036.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast036_0,tail036]
#print axioms numeric036
theorem hash036 : JFp_SHADigest.digest input036=value036 := by
  unfold input036 JFp_SHADigest.digest
  rw [numeric036,JGy_Gr_M0.Hash036.checked]
  rfl
#print axioms hash036
theorem address036 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [153,129,24,20,176,39,22,236,211,202,212,187,140,77,94,63,250,21,206,77,77,113,181,24,141,109,242,160,198,227,5,196]) value026)=input036 := by rfl
#print axioms address036
def tree036 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [153,129,24,20,176,39,22,236,211,202,212,187,140,77,94,63,250,21,206,77,77,113,181,24,141,109,242,160,198,227,5,196])) tree026
theorem root036 : root JFp_SHADigest.digest tree036=value036 := by
  rw [tree036,root,root026]
  exact (congrArg JFp_SHADigest.digest address036).trans hash036
#print axioms root036
theorem shape036 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 193088=tree036 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 193088)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 193088 (by decide),siblings 2 (by decide) 193088 (by decide)]
  rw [shape026 f g inputs siblings]
  rfl
#print axioms shape036
def input037 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash037.message
def value037 : State := JFp_SHADigest.output JGy_Gr_M0.Hash037.result
theorem cast037_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash037.B00.input).map Fin.val=JGy_Gr_M0.Hash037.B00.input := by rfl
#print axioms cast037_0
theorem tail037 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash037.tail).map Fin.val=JGy_Gr_M0.Hash037.tail := by rfl
#print axioms tail037
theorem numeric037 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash037.message).map Fin.val=JGy_Gr_M0.Hash037.message := by
  simp only [JGy_Gr_M0.Hash037.message,JGy_Gr_M0.Hash037.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast037_0,tail037]
#print axioms numeric037
theorem hash037 : JFp_SHADigest.digest input037=value037 := by
  unfold input037 JFp_SHADigest.digest
  rw [numeric037,JGy_Gr_M0.Hash037.checked]
  rfl
#print axioms hash037
theorem address037 : BinMerkle32Path.nodeInput (children value027 (JGc_TX2_HashBytes.state [101,139,27,149,235,32,119,159,21,175,34,168,214,38,192,112,138,28,226,156,191,27,122,66,141,229,44,205,255,101,185,86]))=input037 := by rfl
#print axioms address037
def tree037 : Tree := .branch tree027 (.supplied (JGc_TX2_HashBytes.state [101,139,27,149,235,32,119,159,21,175,34,168,214,38,192,112,138,28,226,156,191,27,122,66,141,229,44,205,255,101,185,86]))
theorem root037 : root JFp_SHADigest.digest tree037=value037 := by
  rw [tree037,root,root027]
  exact (congrArg JFp_SHADigest.digest address037).trans hash037
#print axioms root037
theorem shape037 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 209368=tree037 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 209368)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape027 f g inputs siblings]
  rw [unoccupied f g 2 209372 (by decide),siblings 2 (by decide) 209372 (by decide)]
  rfl
#print axioms shape037
def input038 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash038.message
def value038 : State := JFp_SHADigest.output JGy_Gr_M0.Hash038.result
theorem cast038_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash038.B00.input).map Fin.val=JGy_Gr_M0.Hash038.B00.input := by rfl
#print axioms cast038_0
theorem tail038 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash038.tail).map Fin.val=JGy_Gr_M0.Hash038.tail := by rfl
#print axioms tail038
theorem numeric038 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash038.message).map Fin.val=JGy_Gr_M0.Hash038.message := by
  simp only [JGy_Gr_M0.Hash038.message,JGy_Gr_M0.Hash038.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast038_0,tail038]
#print axioms numeric038
theorem hash038 : JFp_SHADigest.digest input038=value038 := by
  unfold input038 JFp_SHADigest.digest
  rw [numeric038,JGy_Gr_M0.Hash038.checked]
  rfl
#print axioms hash038
theorem address038 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [97,100,140,122,23,30,20,241,117,108,230,40,3,90,18,209,195,137,51,245,94,157,2,13,40,206,120,166,203,53,10,70]) value028)=input038 := by rfl
#print axioms address038
def tree038 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [97,100,140,122,23,30,20,241,117,108,230,40,3,90,18,209,195,137,51,245,94,157,2,13,40,206,120,166,203,53,10,70])) tree028
theorem root038 : root JFp_SHADigest.digest tree038=value038 := by
  rw [tree038,root,root028]
  exact (congrArg JFp_SHADigest.digest address038).trans hash038
#print axioms root038
theorem shape038 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 216816=tree038 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 216816)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 216816 (by decide),siblings 2 (by decide) 216816 (by decide)]
  rw [shape028 f g inputs siblings]
  rfl
#print axioms shape038
def input039 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash039.message
def value039 : State := JFp_SHADigest.output JGy_Gr_M0.Hash039.result
theorem cast039_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash039.B00.input).map Fin.val=JGy_Gr_M0.Hash039.B00.input := by rfl
#print axioms cast039_0
theorem tail039 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash039.tail).map Fin.val=JGy_Gr_M0.Hash039.tail := by rfl
#print axioms tail039
theorem numeric039 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash039.message).map Fin.val=JGy_Gr_M0.Hash039.message := by
  simp only [JGy_Gr_M0.Hash039.message,JGy_Gr_M0.Hash039.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast039_0,tail039]
#print axioms numeric039
theorem hash039 : JFp_SHADigest.digest input039=value039 := by
  unfold input039 JFp_SHADigest.digest
  rw [numeric039,JGy_Gr_M0.Hash039.checked]
  rfl
#print axioms hash039
theorem address039 : BinMerkle32Path.nodeInput (children value029 (JGc_TX2_HashBytes.state [14,156,11,58,98,11,10,23,106,162,4,80,205,20,195,48,179,221,204,9,0,83,249,174,34,4,190,244,166,20,144,192]))=input039 := by rfl
#print axioms address039
def tree039 : Tree := .branch tree029 (.supplied (JGc_TX2_HashBytes.state [14,156,11,58,98,11,10,23,106,162,4,80,205,20,195,48,179,221,204,9,0,83,249,174,34,4,190,244,166,20,144,192]))
theorem root039 : root JFp_SHADigest.digest tree039=value039 := by
  rw [tree039,root,root029]
  exact (congrArg JFp_SHADigest.digest address039).trans hash039
#print axioms root039
theorem shape039 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 245896=tree039 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 245896)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape029 f g inputs siblings]
  rw [unoccupied f g 2 245900 (by decide),siblings 2 (by decide) 245900 (by decide)]
  rfl
#print axioms shape039
end AspisR1.JGy_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input040 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash040.message
def value040 : State := JFp_SHADigest.output JGy_Gr_M0.Hash040.result
theorem cast040_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash040.B00.input).map Fin.val=JGy_Gr_M0.Hash040.B00.input := by rfl
#print axioms cast040_0
theorem tail040 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash040.tail).map Fin.val=JGy_Gr_M0.Hash040.tail := by rfl
#print axioms tail040
theorem numeric040 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash040.message).map Fin.val=JGy_Gr_M0.Hash040.message := by
  simp only [JGy_Gr_M0.Hash040.message,JGy_Gr_M0.Hash040.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast040_0,tail040]
#print axioms numeric040
theorem hash040 : JFp_SHADigest.digest input040=value040 := by
  unfold input040 JFp_SHADigest.digest
  rw [numeric040,JGy_Gr_M0.Hash040.checked]
  rfl
#print axioms hash040
theorem address040 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [237,101,153,156,115,150,6,23,215,162,34,228,173,42,146,106,223,172,140,115,117,138,77,161,26,92,89,55,88,255,0,59]) value030)=input040 := by rfl
#print axioms address040
def tree040 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [237,101,153,156,115,150,6,23,215,162,34,228,173,42,146,106,223,172,140,115,117,138,77,161,26,92,89,55,88,255,0,59])) tree030
theorem root040 : root JFp_SHADigest.digest tree040=value040 := by
  rw [tree040,root,root030]
  exact (congrArg JFp_SHADigest.digest address040).trans hash040
#print axioms root040
theorem shape040 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 65584=tree040 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 65584)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 65584 (by decide),siblings 3 (by decide) 65584 (by decide)]
  rw [shape030 f g inputs siblings]
  rfl
#print axioms shape040
def input041 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash041.message
def value041 : State := JFp_SHADigest.output JGy_Gr_M0.Hash041.result
theorem cast041_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash041.B00.input).map Fin.val=JGy_Gr_M0.Hash041.B00.input := by rfl
#print axioms cast041_0
theorem tail041 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash041.tail).map Fin.val=JGy_Gr_M0.Hash041.tail := by rfl
#print axioms tail041
theorem numeric041 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash041.message).map Fin.val=JGy_Gr_M0.Hash041.message := by
  simp only [JGy_Gr_M0.Hash041.message,JGy_Gr_M0.Hash041.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast041_0,tail041]
#print axioms numeric041
theorem hash041 : JFp_SHADigest.digest input041=value041 := by
  unfold input041 JFp_SHADigest.digest
  rw [numeric041,JGy_Gr_M0.Hash041.checked]
  rfl
#print axioms hash041
theorem address041 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [37,244,135,117,26,54,233,244,102,147,224,254,200,10,248,244,195,200,20,185,169,184,56,177,168,169,22,254,134,167,69,172]) value031)=input041 := by rfl
#print axioms address041
def tree041 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [37,244,135,117,26,54,233,244,102,147,224,254,200,10,248,244,195,200,20,185,169,184,56,177,168,169,22,254,134,167,69,172])) tree031
theorem root041 : root JFp_SHADigest.digest tree041=value041 := by
  rw [tree041,root,root031]
  exact (congrArg JFp_SHADigest.digest address041).trans hash041
#print axioms root041
theorem shape041 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 93488=tree041 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 93488)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 93488 (by decide),siblings 3 (by decide) 93488 (by decide)]
  rw [shape031 f g inputs siblings]
  rfl
#print axioms shape041
def input042 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash042.message
def value042 : State := JFp_SHADigest.output JGy_Gr_M0.Hash042.result
theorem cast042_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash042.B00.input).map Fin.val=JGy_Gr_M0.Hash042.B00.input := by rfl
#print axioms cast042_0
theorem tail042 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash042.tail).map Fin.val=JGy_Gr_M0.Hash042.tail := by rfl
#print axioms tail042
theorem numeric042 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash042.message).map Fin.val=JGy_Gr_M0.Hash042.message := by
  simp only [JGy_Gr_M0.Hash042.message,JGy_Gr_M0.Hash042.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast042_0,tail042]
#print axioms numeric042
theorem hash042 : JFp_SHADigest.digest input042=value042 := by
  unfold input042 JFp_SHADigest.digest
  rw [numeric042,JGy_Gr_M0.Hash042.checked]
  rfl
#print axioms hash042
theorem address042 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [159,155,131,105,178,86,59,104,185,104,3,52,240,166,65,12,166,115,194,190,140,181,58,92,75,125,4,58,182,78,182,117]) value032)=input042 := by rfl
#print axioms address042
def tree042 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [159,155,131,105,178,86,59,104,185,104,3,52,240,166,65,12,166,115,194,190,140,181,58,92,75,125,4,58,182,78,182,117])) tree032
theorem root042 : root JFp_SHADigest.digest tree042=value042 := by
  rw [tree042,root,root032]
  exact (congrArg JFp_SHADigest.digest address042).trans hash042
#print axioms root042
theorem shape042 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 147520=tree042 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 147520)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 147520 (by decide),siblings 3 (by decide) 147520 (by decide)]
  rw [shape032 f g inputs siblings]
  rfl
#print axioms shape042
def input043 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash043.message
def value043 : State := JFp_SHADigest.output JGy_Gr_M0.Hash043.result
theorem cast043_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash043.B00.input).map Fin.val=JGy_Gr_M0.Hash043.B00.input := by rfl
#print axioms cast043_0
theorem tail043 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash043.tail).map Fin.val=JGy_Gr_M0.Hash043.tail := by rfl
#print axioms tail043
theorem numeric043 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash043.message).map Fin.val=JGy_Gr_M0.Hash043.message := by
  simp only [JGy_Gr_M0.Hash043.message,JGy_Gr_M0.Hash043.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast043_0,tail043]
#print axioms numeric043
theorem hash043 : JFp_SHADigest.digest input043=value043 := by
  unfold input043 JFp_SHADigest.digest
  rw [numeric043,JGy_Gr_M0.Hash043.checked]
  rfl
#print axioms hash043
theorem address043 : BinMerkle32Path.nodeInput (children value033 (JGc_TX2_HashBytes.state [184,1,99,242,168,187,235,249,27,44,146,36,138,238,109,46,110,208,60,198,44,245,5,255,142,243,124,75,122,28,81,44]))=input043 := by rfl
#print axioms address043
def tree043 : Tree := .branch tree033 (.supplied (JGc_TX2_HashBytes.state [184,1,99,242,168,187,235,249,27,44,146,36,138,238,109,46,110,208,60,198,44,245,5,255,142,243,124,75,122,28,81,44]))
theorem root043 : root JFp_SHADigest.digest tree043=value043 := by
  rw [tree043,root,root033]
  exact (congrArg JFp_SHADigest.digest address043).trans hash043
#print axioms root043
theorem shape043 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 159808=tree043 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 159808)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape033 f g inputs siblings]
  rw [unoccupied f g 3 159816 (by decide),siblings 3 (by decide) 159816 (by decide)]
  rfl
#print axioms shape043
def input044 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash044.message
def value044 : State := JFp_SHADigest.output JGy_Gr_M0.Hash044.result
theorem cast044_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash044.B00.input).map Fin.val=JGy_Gr_M0.Hash044.B00.input := by rfl
#print axioms cast044_0
theorem tail044 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash044.tail).map Fin.val=JGy_Gr_M0.Hash044.tail := by rfl
#print axioms tail044
theorem numeric044 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash044.message).map Fin.val=JGy_Gr_M0.Hash044.message := by
  simp only [JGy_Gr_M0.Hash044.message,JGy_Gr_M0.Hash044.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast044_0,tail044]
#print axioms numeric044
theorem hash044 : JFp_SHADigest.digest input044=value044 := by
  unfold input044 JFp_SHADigest.digest
  rw [numeric044,JGy_Gr_M0.Hash044.checked]
  rfl
#print axioms hash044
theorem address044 : BinMerkle32Path.nodeInput (children value034 (JGc_TX2_HashBytes.state [249,155,11,53,79,5,46,47,174,40,100,160,232,197,150,206,57,65,60,151,77,221,228,49,146,47,224,242,31,205,112,53]))=input044 := by rfl
#print axioms address044
def tree044 : Tree := .branch tree034 (.supplied (JGc_TX2_HashBytes.state [249,155,11,53,79,5,46,47,174,40,100,160,232,197,150,206,57,65,60,151,77,221,228,49,146,47,224,242,31,205,112,53]))
theorem root044 : root JFp_SHADigest.digest tree044=value044 := by
  rw [tree044,root,root034]
  exact (congrArg JFp_SHADigest.digest address044).trans hash044
#print axioms root044
theorem shape044 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 183856=tree044 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 183856)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape034 f g inputs siblings]
  rw [unoccupied f g 3 183864 (by decide),siblings 3 (by decide) 183864 (by decide)]
  rfl
#print axioms shape044
def input045 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash045.message
def value045 : State := JFp_SHADigest.output JGy_Gr_M0.Hash045.result
theorem cast045_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash045.B00.input).map Fin.val=JGy_Gr_M0.Hash045.B00.input := by rfl
#print axioms cast045_0
theorem tail045 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash045.tail).map Fin.val=JGy_Gr_M0.Hash045.tail := by rfl
#print axioms tail045
theorem numeric045 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash045.message).map Fin.val=JGy_Gr_M0.Hash045.message := by
  simp only [JGy_Gr_M0.Hash045.message,JGy_Gr_M0.Hash045.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast045_0,tail045]
#print axioms numeric045
theorem hash045 : JFp_SHADigest.digest input045=value045 := by
  unfold input045 JFp_SHADigest.digest
  rw [numeric045,JGy_Gr_M0.Hash045.checked]
  rfl
#print axioms hash045
theorem address045 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [238,230,76,71,245,181,227,67,63,205,182,151,40,139,104,248,128,252,163,105,140,161,180,90,61,195,7,172,203,134,85,243]) value035)=input045 := by rfl
#print axioms address045
def tree045 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [238,230,76,71,245,181,227,67,63,205,182,151,40,139,104,248,128,252,163,105,140,161,180,90,61,195,7,172,203,134,85,243])) tree035
theorem root045 : root JFp_SHADigest.digest tree045=value045 := by
  rw [tree045,root,root035]
  exact (congrArg JFp_SHADigest.digest address045).trans hash045
#print axioms root045
theorem shape045 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 192304=tree045 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 192304)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 192304 (by decide),siblings 3 (by decide) 192304 (by decide)]
  rw [shape035 f g inputs siblings]
  rfl
#print axioms shape045
def input046 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash046.message
def value046 : State := JFp_SHADigest.output JGy_Gr_M0.Hash046.result
theorem cast046_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash046.B00.input).map Fin.val=JGy_Gr_M0.Hash046.B00.input := by rfl
#print axioms cast046_0
theorem tail046 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash046.tail).map Fin.val=JGy_Gr_M0.Hash046.tail := by rfl
#print axioms tail046
theorem numeric046 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash046.message).map Fin.val=JGy_Gr_M0.Hash046.message := by
  simp only [JGy_Gr_M0.Hash046.message,JGy_Gr_M0.Hash046.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast046_0,tail046]
#print axioms numeric046
theorem hash046 : JFp_SHADigest.digest input046=value046 := by
  unfold input046 JFp_SHADigest.digest
  rw [numeric046,JGy_Gr_M0.Hash046.checked]
  rfl
#print axioms hash046
theorem address046 : BinMerkle32Path.nodeInput (children value036 (JGc_TX2_HashBytes.state [236,70,66,207,227,98,249,31,237,39,77,55,123,239,84,213,237,51,12,241,116,71,72,165,63,45,61,196,132,73,13,35]))=input046 := by rfl
#print axioms address046
def tree046 : Tree := .branch tree036 (.supplied (JGc_TX2_HashBytes.state [236,70,66,207,227,98,249,31,237,39,77,55,123,239,84,213,237,51,12,241,116,71,72,165,63,45,61,196,132,73,13,35]))
theorem root046 : root JFp_SHADigest.digest tree046=value046 := by
  rw [tree046,root,root036]
  exact (congrArg JFp_SHADigest.digest address046).trans hash046
#print axioms root046
theorem shape046 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 193088=tree046 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 193088)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape036 f g inputs siblings]
  rw [unoccupied f g 3 193096 (by decide),siblings 3 (by decide) 193096 (by decide)]
  rfl
#print axioms shape046
def input047 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash047.message
def value047 : State := JFp_SHADigest.output JGy_Gr_M0.Hash047.result
theorem cast047_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash047.B00.input).map Fin.val=JGy_Gr_M0.Hash047.B00.input := by rfl
#print axioms cast047_0
theorem tail047 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash047.tail).map Fin.val=JGy_Gr_M0.Hash047.tail := by rfl
#print axioms tail047
theorem numeric047 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash047.message).map Fin.val=JGy_Gr_M0.Hash047.message := by
  simp only [JGy_Gr_M0.Hash047.message,JGy_Gr_M0.Hash047.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast047_0,tail047]
#print axioms numeric047
theorem hash047 : JFp_SHADigest.digest input047=value047 := by
  unfold input047 JFp_SHADigest.digest
  rw [numeric047,JGy_Gr_M0.Hash047.checked]
  rfl
#print axioms hash047
theorem address047 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [91,225,147,229,114,51,191,240,38,62,23,3,232,35,207,56,1,62,142,130,179,3,146,218,181,241,176,104,168,124,104,231]) value037)=input047 := by rfl
#print axioms address047
def tree047 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [91,225,147,229,114,51,191,240,38,62,23,3,232,35,207,56,1,62,142,130,179,3,146,218,181,241,176,104,168,124,104,231])) tree037
theorem root047 : root JFp_SHADigest.digest tree047=value047 := by
  rw [tree047,root,root037]
  exact (congrArg JFp_SHADigest.digest address047).trans hash047
#print axioms root047
theorem shape047 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 209360=tree047 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 209360)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 209360 (by decide),siblings 3 (by decide) 209360 (by decide)]
  rw [shape037 f g inputs siblings]
  rfl
#print axioms shape047
def input048 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash048.message
def value048 : State := JFp_SHADigest.output JGy_Gr_M0.Hash048.result
theorem cast048_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash048.B00.input).map Fin.val=JGy_Gr_M0.Hash048.B00.input := by rfl
#print axioms cast048_0
theorem tail048 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash048.tail).map Fin.val=JGy_Gr_M0.Hash048.tail := by rfl
#print axioms tail048
theorem numeric048 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash048.message).map Fin.val=JGy_Gr_M0.Hash048.message := by
  simp only [JGy_Gr_M0.Hash048.message,JGy_Gr_M0.Hash048.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast048_0,tail048]
#print axioms numeric048
theorem hash048 : JFp_SHADigest.digest input048=value048 := by
  unfold input048 JFp_SHADigest.digest
  rw [numeric048,JGy_Gr_M0.Hash048.checked]
  rfl
#print axioms hash048
theorem address048 : BinMerkle32Path.nodeInput (children value038 (JGc_TX2_HashBytes.state [145,243,79,135,184,204,125,182,43,245,47,168,35,84,132,21,100,19,63,164,130,24,235,181,69,88,56,166,229,252,70,120]))=input048 := by rfl
#print axioms address048
def tree048 : Tree := .branch tree038 (.supplied (JGc_TX2_HashBytes.state [145,243,79,135,184,204,125,182,43,245,47,168,35,84,132,21,100,19,63,164,130,24,235,181,69,88,56,166,229,252,70,120]))
theorem root048 : root JFp_SHADigest.digest tree048=value048 := by
  rw [tree048,root,root038]
  exact (congrArg JFp_SHADigest.digest address048).trans hash048
#print axioms root048
theorem shape048 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 216816=tree048 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 216816)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape038 f g inputs siblings]
  rw [unoccupied f g 3 216824 (by decide),siblings 3 (by decide) 216824 (by decide)]
  rfl
#print axioms shape048
def input049 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash049.message
def value049 : State := JFp_SHADigest.output JGy_Gr_M0.Hash049.result
theorem cast049_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash049.B00.input).map Fin.val=JGy_Gr_M0.Hash049.B00.input := by rfl
#print axioms cast049_0
theorem tail049 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash049.tail).map Fin.val=JGy_Gr_M0.Hash049.tail := by rfl
#print axioms tail049
theorem numeric049 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash049.message).map Fin.val=JGy_Gr_M0.Hash049.message := by
  simp only [JGy_Gr_M0.Hash049.message,JGy_Gr_M0.Hash049.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast049_0,tail049]
#print axioms numeric049
theorem hash049 : JFp_SHADigest.digest input049=value049 := by
  unfold input049 JFp_SHADigest.digest
  rw [numeric049,JGy_Gr_M0.Hash049.checked]
  rfl
#print axioms hash049
theorem address049 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [252,69,117,223,75,28,193,245,113,139,104,231,98,230,139,109,224,152,128,86,124,122,36,40,153,175,49,45,182,138,161,172]) value039)=input049 := by rfl
#print axioms address049
def tree049 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [252,69,117,223,75,28,193,245,113,139,104,231,98,230,139,109,224,152,128,86,124,122,36,40,153,175,49,45,182,138,161,172])) tree039
theorem root049 : root JFp_SHADigest.digest tree049=value049 := by
  rw [tree049,root,root039]
  exact (congrArg JFp_SHADigest.digest address049).trans hash049
#print axioms root049
theorem shape049 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 245888=tree049 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 245888)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 245888 (by decide),siblings 3 (by decide) 245888 (by decide)]
  rw [shape039 f g inputs siblings]
  rfl
#print axioms shape049
end AspisR1.JGy_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input050 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash050.message
def value050 : State := JFp_SHADigest.output JGy_Gr_M0.Hash050.result
theorem cast050_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash050.B00.input).map Fin.val=JGy_Gr_M0.Hash050.B00.input := by rfl
#print axioms cast050_0
theorem tail050 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash050.tail).map Fin.val=JGy_Gr_M0.Hash050.tail := by rfl
#print axioms tail050
theorem numeric050 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash050.message).map Fin.val=JGy_Gr_M0.Hash050.message := by
  simp only [JGy_Gr_M0.Hash050.message,JGy_Gr_M0.Hash050.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast050_0,tail050]
#print axioms numeric050
theorem hash050 : JFp_SHADigest.digest input050=value050 := by
  unfold input050 JFp_SHADigest.digest
  rw [numeric050,JGy_Gr_M0.Hash050.checked]
  rfl
#print axioms hash050
theorem address050 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [236,29,86,76,30,67,12,237,81,110,150,232,163,108,233,233,80,159,68,44,137,93,213,2,246,186,157,124,230,83,136,227]) value040)=input050 := by rfl
#print axioms address050
def tree050 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [236,29,86,76,30,67,12,237,81,110,150,232,163,108,233,233,80,159,68,44,137,93,213,2,246,186,157,124,230,83,136,227])) tree040
theorem root050 : root JFp_SHADigest.digest tree050=value050 := by
  rw [tree050,root,root040]
  exact (congrArg JFp_SHADigest.digest address050).trans hash050
#print axioms root050
theorem shape050 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 65568=tree050 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 65568)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 65568 (by decide),siblings 4 (by decide) 65568 (by decide)]
  rw [shape040 f g inputs siblings]
  rfl
#print axioms shape050
def input051 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash051.message
def value051 : State := JFp_SHADigest.output JGy_Gr_M0.Hash051.result
theorem cast051_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash051.B00.input).map Fin.val=JGy_Gr_M0.Hash051.B00.input := by rfl
#print axioms cast051_0
theorem tail051 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash051.tail).map Fin.val=JGy_Gr_M0.Hash051.tail := by rfl
#print axioms tail051
theorem numeric051 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash051.message).map Fin.val=JGy_Gr_M0.Hash051.message := by
  simp only [JGy_Gr_M0.Hash051.message,JGy_Gr_M0.Hash051.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast051_0,tail051]
#print axioms numeric051
theorem hash051 : JFp_SHADigest.digest input051=value051 := by
  unfold input051 JFp_SHADigest.digest
  rw [numeric051,JGy_Gr_M0.Hash051.checked]
  rfl
#print axioms hash051
theorem address051 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [247,52,6,98,251,50,13,174,91,242,73,132,225,30,14,57,46,158,63,2,190,121,132,15,58,169,20,205,208,200,105,57]) value041)=input051 := by rfl
#print axioms address051
def tree051 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [247,52,6,98,251,50,13,174,91,242,73,132,225,30,14,57,46,158,63,2,190,121,132,15,58,169,20,205,208,200,105,57])) tree041
theorem root051 : root JFp_SHADigest.digest tree051=value051 := by
  rw [tree051,root,root041]
  exact (congrArg JFp_SHADigest.digest address051).trans hash051
#print axioms root051
theorem shape051 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 93472=tree051 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 93472)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 93472 (by decide),siblings 4 (by decide) 93472 (by decide)]
  rw [shape041 f g inputs siblings]
  rfl
#print axioms shape051
def input052 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash052.message
def value052 : State := JFp_SHADigest.output JGy_Gr_M0.Hash052.result
theorem cast052_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash052.B00.input).map Fin.val=JGy_Gr_M0.Hash052.B00.input := by rfl
#print axioms cast052_0
theorem tail052 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash052.tail).map Fin.val=JGy_Gr_M0.Hash052.tail := by rfl
#print axioms tail052
theorem numeric052 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash052.message).map Fin.val=JGy_Gr_M0.Hash052.message := by
  simp only [JGy_Gr_M0.Hash052.message,JGy_Gr_M0.Hash052.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast052_0,tail052]
#print axioms numeric052
theorem hash052 : JFp_SHADigest.digest input052=value052 := by
  unfold input052 JFp_SHADigest.digest
  rw [numeric052,JGy_Gr_M0.Hash052.checked]
  rfl
#print axioms hash052
theorem address052 : BinMerkle32Path.nodeInput (children value042 (JGc_TX2_HashBytes.state [47,45,200,13,66,168,117,82,224,239,90,35,215,108,210,255,88,3,40,35,217,209,147,174,210,246,44,160,81,239,153,153]))=input052 := by rfl
#print axioms address052
def tree052 : Tree := .branch tree042 (.supplied (JGc_TX2_HashBytes.state [47,45,200,13,66,168,117,82,224,239,90,35,215,108,210,255,88,3,40,35,217,209,147,174,210,246,44,160,81,239,153,153]))
theorem root052 : root JFp_SHADigest.digest tree052=value052 := by
  rw [tree052,root,root042]
  exact (congrArg JFp_SHADigest.digest address052).trans hash052
#print axioms root052
theorem shape052 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 147520=tree052 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 147520)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape042 f g inputs siblings]
  rw [unoccupied f g 4 147536 (by decide),siblings 4 (by decide) 147536 (by decide)]
  rfl
#print axioms shape052
def input053 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash053.message
def value053 : State := JFp_SHADigest.output JGy_Gr_M0.Hash053.result
theorem cast053_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash053.B00.input).map Fin.val=JGy_Gr_M0.Hash053.B00.input := by rfl
#print axioms cast053_0
theorem tail053 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash053.tail).map Fin.val=JGy_Gr_M0.Hash053.tail := by rfl
#print axioms tail053
theorem numeric053 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash053.message).map Fin.val=JGy_Gr_M0.Hash053.message := by
  simp only [JGy_Gr_M0.Hash053.message,JGy_Gr_M0.Hash053.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast053_0,tail053]
#print axioms numeric053
theorem hash053 : JFp_SHADigest.digest input053=value053 := by
  unfold input053 JFp_SHADigest.digest
  rw [numeric053,JGy_Gr_M0.Hash053.checked]
  rfl
#print axioms hash053
theorem address053 : BinMerkle32Path.nodeInput (children value043 (JGc_TX2_HashBytes.state [146,13,29,171,138,255,137,186,12,109,8,62,51,250,197,131,20,22,189,188,183,99,33,0,28,151,225,92,193,93,19,97]))=input053 := by rfl
#print axioms address053
def tree053 : Tree := .branch tree043 (.supplied (JGc_TX2_HashBytes.state [146,13,29,171,138,255,137,186,12,109,8,62,51,250,197,131,20,22,189,188,183,99,33,0,28,151,225,92,193,93,19,97]))
theorem root053 : root JFp_SHADigest.digest tree053=value053 := by
  rw [tree053,root,root043]
  exact (congrArg JFp_SHADigest.digest address053).trans hash053
#print axioms root053
theorem shape053 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 159808=tree053 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 159808)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape043 f g inputs siblings]
  rw [unoccupied f g 4 159824 (by decide),siblings 4 (by decide) 159824 (by decide)]
  rfl
#print axioms shape053
def input054 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash054.message
def value054 : State := JFp_SHADigest.output JGy_Gr_M0.Hash054.result
theorem cast054_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash054.B00.input).map Fin.val=JGy_Gr_M0.Hash054.B00.input := by rfl
#print axioms cast054_0
theorem tail054 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash054.tail).map Fin.val=JGy_Gr_M0.Hash054.tail := by rfl
#print axioms tail054
theorem numeric054 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash054.message).map Fin.val=JGy_Gr_M0.Hash054.message := by
  simp only [JGy_Gr_M0.Hash054.message,JGy_Gr_M0.Hash054.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast054_0,tail054]
#print axioms numeric054
theorem hash054 : JFp_SHADigest.digest input054=value054 := by
  unfold input054 JFp_SHADigest.digest
  rw [numeric054,JGy_Gr_M0.Hash054.checked]
  rfl
#print axioms hash054
theorem address054 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [179,71,254,154,5,86,67,35,162,58,89,34,52,121,77,71,180,240,121,174,98,142,50,217,93,201,208,91,199,253,90,108]) value044)=input054 := by rfl
#print axioms address054
def tree054 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [179,71,254,154,5,86,67,35,162,58,89,34,52,121,77,71,180,240,121,174,98,142,50,217,93,201,208,91,199,253,90,108])) tree044
theorem root054 : root JFp_SHADigest.digest tree054=value054 := by
  rw [tree054,root,root044]
  exact (congrArg JFp_SHADigest.digest address054).trans hash054
#print axioms root054
theorem shape054 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 183840=tree054 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 183840)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 183840 (by decide),siblings 4 (by decide) 183840 (by decide)]
  rw [shape044 f g inputs siblings]
  rfl
#print axioms shape054
def input055 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash055.message
def value055 : State := JFp_SHADigest.output JGy_Gr_M0.Hash055.result
theorem cast055_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash055.B00.input).map Fin.val=JGy_Gr_M0.Hash055.B00.input := by rfl
#print axioms cast055_0
theorem tail055 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash055.tail).map Fin.val=JGy_Gr_M0.Hash055.tail := by rfl
#print axioms tail055
theorem numeric055 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash055.message).map Fin.val=JGy_Gr_M0.Hash055.message := by
  simp only [JGy_Gr_M0.Hash055.message,JGy_Gr_M0.Hash055.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast055_0,tail055]
#print axioms numeric055
theorem hash055 : JFp_SHADigest.digest input055=value055 := by
  unfold input055 JFp_SHADigest.digest
  rw [numeric055,JGy_Gr_M0.Hash055.checked]
  rfl
#print axioms hash055
theorem address055 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [38,17,228,198,172,26,2,118,104,186,59,10,202,180,122,6,153,83,58,205,40,8,165,125,33,207,147,16,114,32,156,118]) value045)=input055 := by rfl
#print axioms address055
def tree055 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [38,17,228,198,172,26,2,118,104,186,59,10,202,180,122,6,153,83,58,205,40,8,165,125,33,207,147,16,114,32,156,118])) tree045
theorem root055 : root JFp_SHADigest.digest tree055=value055 := by
  rw [tree055,root,root045]
  exact (congrArg JFp_SHADigest.digest address055).trans hash055
#print axioms root055
theorem shape055 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 192288=tree055 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 192288)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 192288 (by decide),siblings 4 (by decide) 192288 (by decide)]
  rw [shape045 f g inputs siblings]
  rfl
#print axioms shape055
def input056 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash056.message
def value056 : State := JFp_SHADigest.output JGy_Gr_M0.Hash056.result
theorem cast056_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash056.B00.input).map Fin.val=JGy_Gr_M0.Hash056.B00.input := by rfl
#print axioms cast056_0
theorem tail056 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash056.tail).map Fin.val=JGy_Gr_M0.Hash056.tail := by rfl
#print axioms tail056
theorem numeric056 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash056.message).map Fin.val=JGy_Gr_M0.Hash056.message := by
  simp only [JGy_Gr_M0.Hash056.message,JGy_Gr_M0.Hash056.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast056_0,tail056]
#print axioms numeric056
theorem hash056 : JFp_SHADigest.digest input056=value056 := by
  unfold input056 JFp_SHADigest.digest
  rw [numeric056,JGy_Gr_M0.Hash056.checked]
  rfl
#print axioms hash056
theorem address056 : BinMerkle32Path.nodeInput (children value046 (JGc_TX2_HashBytes.state [174,64,125,54,103,77,213,103,170,28,57,102,173,92,85,231,178,203,38,164,60,235,247,116,32,127,10,7,79,88,232,33]))=input056 := by rfl
#print axioms address056
def tree056 : Tree := .branch tree046 (.supplied (JGc_TX2_HashBytes.state [174,64,125,54,103,77,213,103,170,28,57,102,173,92,85,231,178,203,38,164,60,235,247,116,32,127,10,7,79,88,232,33]))
theorem root056 : root JFp_SHADigest.digest tree056=value056 := by
  rw [tree056,root,root046]
  exact (congrArg JFp_SHADigest.digest address056).trans hash056
#print axioms root056
theorem shape056 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 193088=tree056 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 193088)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape046 f g inputs siblings]
  rw [unoccupied f g 4 193104 (by decide),siblings 4 (by decide) 193104 (by decide)]
  rfl
#print axioms shape056
def input057 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash057.message
def value057 : State := JFp_SHADigest.output JGy_Gr_M0.Hash057.result
theorem cast057_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash057.B00.input).map Fin.val=JGy_Gr_M0.Hash057.B00.input := by rfl
#print axioms cast057_0
theorem tail057 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash057.tail).map Fin.val=JGy_Gr_M0.Hash057.tail := by rfl
#print axioms tail057
theorem numeric057 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash057.message).map Fin.val=JGy_Gr_M0.Hash057.message := by
  simp only [JGy_Gr_M0.Hash057.message,JGy_Gr_M0.Hash057.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast057_0,tail057]
#print axioms numeric057
theorem hash057 : JFp_SHADigest.digest input057=value057 := by
  unfold input057 JFp_SHADigest.digest
  rw [numeric057,JGy_Gr_M0.Hash057.checked]
  rfl
#print axioms hash057
theorem address057 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [162,83,182,157,31,13,19,175,77,247,91,65,123,57,95,74,245,247,220,188,222,222,38,42,24,110,87,188,135,58,50,173]) value047)=input057 := by rfl
#print axioms address057
def tree057 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [162,83,182,157,31,13,19,175,77,247,91,65,123,57,95,74,245,247,220,188,222,222,38,42,24,110,87,188,135,58,50,173])) tree047
theorem root057 : root JFp_SHADigest.digest tree057=value057 := by
  rw [tree057,root,root047]
  exact (congrArg JFp_SHADigest.digest address057).trans hash057
#print axioms root057
theorem shape057 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 209344=tree057 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 209344)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 209344 (by decide),siblings 4 (by decide) 209344 (by decide)]
  rw [shape047 f g inputs siblings]
  rfl
#print axioms shape057
def input058 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash058.message
def value058 : State := JFp_SHADigest.output JGy_Gr_M0.Hash058.result
theorem cast058_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash058.B00.input).map Fin.val=JGy_Gr_M0.Hash058.B00.input := by rfl
#print axioms cast058_0
theorem tail058 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash058.tail).map Fin.val=JGy_Gr_M0.Hash058.tail := by rfl
#print axioms tail058
theorem numeric058 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash058.message).map Fin.val=JGy_Gr_M0.Hash058.message := by
  simp only [JGy_Gr_M0.Hash058.message,JGy_Gr_M0.Hash058.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast058_0,tail058]
#print axioms numeric058
theorem hash058 : JFp_SHADigest.digest input058=value058 := by
  unfold input058 JFp_SHADigest.digest
  rw [numeric058,JGy_Gr_M0.Hash058.checked]
  rfl
#print axioms hash058
theorem address058 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [146,40,112,149,161,135,34,145,67,59,110,211,60,96,206,150,59,192,248,67,117,8,78,102,40,34,154,21,23,151,238,154]) value048)=input058 := by rfl
#print axioms address058
def tree058 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [146,40,112,149,161,135,34,145,67,59,110,211,60,96,206,150,59,192,248,67,117,8,78,102,40,34,154,21,23,151,238,154])) tree048
theorem root058 : root JFp_SHADigest.digest tree058=value058 := by
  rw [tree058,root,root048]
  exact (congrArg JFp_SHADigest.digest address058).trans hash058
#print axioms root058
theorem shape058 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 216800=tree058 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 216800)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 216800 (by decide),siblings 4 (by decide) 216800 (by decide)]
  rw [shape048 f g inputs siblings]
  rfl
#print axioms shape058
def input059 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash059.message
def value059 : State := JFp_SHADigest.output JGy_Gr_M0.Hash059.result
theorem cast059_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash059.B00.input).map Fin.val=JGy_Gr_M0.Hash059.B00.input := by rfl
#print axioms cast059_0
theorem tail059 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash059.tail).map Fin.val=JGy_Gr_M0.Hash059.tail := by rfl
#print axioms tail059
theorem numeric059 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash059.message).map Fin.val=JGy_Gr_M0.Hash059.message := by
  simp only [JGy_Gr_M0.Hash059.message,JGy_Gr_M0.Hash059.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast059_0,tail059]
#print axioms numeric059
theorem hash059 : JFp_SHADigest.digest input059=value059 := by
  unfold input059 JFp_SHADigest.digest
  rw [numeric059,JGy_Gr_M0.Hash059.checked]
  rfl
#print axioms hash059
theorem address059 : BinMerkle32Path.nodeInput (children value049 (JGc_TX2_HashBytes.state [148,49,202,250,248,38,32,82,139,58,215,125,191,197,113,97,118,28,250,196,119,217,110,64,141,12,92,14,240,146,144,157]))=input059 := by rfl
#print axioms address059
def tree059 : Tree := .branch tree049 (.supplied (JGc_TX2_HashBytes.state [148,49,202,250,248,38,32,82,139,58,215,125,191,197,113,97,118,28,250,196,119,217,110,64,141,12,92,14,240,146,144,157]))
theorem root059 : root JFp_SHADigest.digest tree059=value059 := by
  rw [tree059,root,root049]
  exact (congrArg JFp_SHADigest.digest address059).trans hash059
#print axioms root059
theorem shape059 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 245888=tree059 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 245888)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape049 f g inputs siblings]
  rw [unoccupied f g 4 245904 (by decide),siblings 4 (by decide) 245904 (by decide)]
  rfl
#print axioms shape059
end AspisR1.JGy_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input060 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash060.message
def value060 : State := JFp_SHADigest.output JGy_Gr_M0.Hash060.result
theorem cast060_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash060.B00.input).map Fin.val=JGy_Gr_M0.Hash060.B00.input := by rfl
#print axioms cast060_0
theorem tail060 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash060.tail).map Fin.val=JGy_Gr_M0.Hash060.tail := by rfl
#print axioms tail060
theorem numeric060 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash060.message).map Fin.val=JGy_Gr_M0.Hash060.message := by
  simp only [JGy_Gr_M0.Hash060.message,JGy_Gr_M0.Hash060.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast060_0,tail060]
#print axioms numeric060
theorem hash060 : JFp_SHADigest.digest input060=value060 := by
  unfold input060 JFp_SHADigest.digest
  rw [numeric060,JGy_Gr_M0.Hash060.checked]
  rfl
#print axioms hash060
theorem address060 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [216,17,255,192,221,66,225,78,57,192,131,236,153,46,142,77,41,52,179,22,166,119,175,6,80,2,94,166,171,119,89,64]) value050)=input060 := by rfl
#print axioms address060
def tree060 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [216,17,255,192,221,66,225,78,57,192,131,236,153,46,142,77,41,52,179,22,166,119,175,6,80,2,94,166,171,119,89,64])) tree050
theorem root060 : root JFp_SHADigest.digest tree060=value060 := by
  rw [tree060,root,root050]
  exact (congrArg JFp_SHADigest.digest address060).trans hash060
#print axioms root060
theorem shape060 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 65536=tree060 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 65536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 65536 (by decide),siblings 5 (by decide) 65536 (by decide)]
  rw [shape050 f g inputs siblings]
  rfl
#print axioms shape060
def input061 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash061.message
def value061 : State := JFp_SHADigest.output JGy_Gr_M0.Hash061.result
theorem cast061_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash061.B00.input).map Fin.val=JGy_Gr_M0.Hash061.B00.input := by rfl
#print axioms cast061_0
theorem tail061 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash061.tail).map Fin.val=JGy_Gr_M0.Hash061.tail := by rfl
#print axioms tail061
theorem numeric061 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash061.message).map Fin.val=JGy_Gr_M0.Hash061.message := by
  simp only [JGy_Gr_M0.Hash061.message,JGy_Gr_M0.Hash061.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast061_0,tail061]
#print axioms numeric061
theorem hash061 : JFp_SHADigest.digest input061=value061 := by
  unfold input061 JFp_SHADigest.digest
  rw [numeric061,JGy_Gr_M0.Hash061.checked]
  rfl
#print axioms hash061
theorem address061 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [204,48,251,61,224,226,231,54,110,116,192,65,229,239,85,15,141,34,33,130,96,59,83,197,192,43,247,186,251,77,95,136]) value051)=input061 := by rfl
#print axioms address061
def tree061 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [204,48,251,61,224,226,231,54,110,116,192,65,229,239,85,15,141,34,33,130,96,59,83,197,192,43,247,186,251,77,95,136])) tree051
theorem root061 : root JFp_SHADigest.digest tree061=value061 := by
  rw [tree061,root,root051]
  exact (congrArg JFp_SHADigest.digest address061).trans hash061
#print axioms root061
theorem shape061 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 93440=tree061 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 93440)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 93440 (by decide),siblings 5 (by decide) 93440 (by decide)]
  rw [shape051 f g inputs siblings]
  rfl
#print axioms shape061
def input062 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash062.message
def value062 : State := JFp_SHADigest.output JGy_Gr_M0.Hash062.result
theorem cast062_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash062.B00.input).map Fin.val=JGy_Gr_M0.Hash062.B00.input := by rfl
#print axioms cast062_0
theorem tail062 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash062.tail).map Fin.val=JGy_Gr_M0.Hash062.tail := by rfl
#print axioms tail062
theorem numeric062 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash062.message).map Fin.val=JGy_Gr_M0.Hash062.message := by
  simp only [JGy_Gr_M0.Hash062.message,JGy_Gr_M0.Hash062.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast062_0,tail062]
#print axioms numeric062
theorem hash062 : JFp_SHADigest.digest input062=value062 := by
  unfold input062 JFp_SHADigest.digest
  rw [numeric062,JGy_Gr_M0.Hash062.checked]
  rfl
#print axioms hash062
theorem address062 : BinMerkle32Path.nodeInput (children value052 (JGc_TX2_HashBytes.state [204,210,70,143,235,140,144,248,219,78,146,18,143,241,159,115,100,67,99,77,124,5,73,9,122,59,54,61,178,235,1,45]))=input062 := by rfl
#print axioms address062
def tree062 : Tree := .branch tree052 (.supplied (JGc_TX2_HashBytes.state [204,210,70,143,235,140,144,248,219,78,146,18,143,241,159,115,100,67,99,77,124,5,73,9,122,59,54,61,178,235,1,45]))
theorem root062 : root JFp_SHADigest.digest tree062=value062 := by
  rw [tree062,root,root052]
  exact (congrArg JFp_SHADigest.digest address062).trans hash062
#print axioms root062
theorem shape062 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 147520=tree062 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 147520)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape052 f g inputs siblings]
  rw [unoccupied f g 5 147552 (by decide),siblings 5 (by decide) 147552 (by decide)]
  rfl
#print axioms shape062
def input063 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash063.message
def value063 : State := JFp_SHADigest.output JGy_Gr_M0.Hash063.result
theorem cast063_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash063.B00.input).map Fin.val=JGy_Gr_M0.Hash063.B00.input := by rfl
#print axioms cast063_0
theorem tail063 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash063.tail).map Fin.val=JGy_Gr_M0.Hash063.tail := by rfl
#print axioms tail063
theorem numeric063 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash063.message).map Fin.val=JGy_Gr_M0.Hash063.message := by
  simp only [JGy_Gr_M0.Hash063.message,JGy_Gr_M0.Hash063.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast063_0,tail063]
#print axioms numeric063
theorem hash063 : JFp_SHADigest.digest input063=value063 := by
  unfold input063 JFp_SHADigest.digest
  rw [numeric063,JGy_Gr_M0.Hash063.checked]
  rfl
#print axioms hash063
theorem address063 : BinMerkle32Path.nodeInput (children value053 (JGc_TX2_HashBytes.state [92,145,193,181,163,4,241,41,44,66,156,75,123,119,113,146,69,183,16,241,54,8,84,133,199,46,217,50,3,136,195,213]))=input063 := by rfl
#print axioms address063
def tree063 : Tree := .branch tree053 (.supplied (JGc_TX2_HashBytes.state [92,145,193,181,163,4,241,41,44,66,156,75,123,119,113,146,69,183,16,241,54,8,84,133,199,46,217,50,3,136,195,213]))
theorem root063 : root JFp_SHADigest.digest tree063=value063 := by
  rw [tree063,root,root053]
  exact (congrArg JFp_SHADigest.digest address063).trans hash063
#print axioms root063
theorem shape063 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 159808=tree063 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 159808)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape053 f g inputs siblings]
  rw [unoccupied f g 5 159840 (by decide),siblings 5 (by decide) 159840 (by decide)]
  rfl
#print axioms shape063
def input064 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash064.message
def value064 : State := JFp_SHADigest.output JGy_Gr_M0.Hash064.result
theorem cast064_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash064.B00.input).map Fin.val=JGy_Gr_M0.Hash064.B00.input := by rfl
#print axioms cast064_0
theorem tail064 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash064.tail).map Fin.val=JGy_Gr_M0.Hash064.tail := by rfl
#print axioms tail064
theorem numeric064 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash064.message).map Fin.val=JGy_Gr_M0.Hash064.message := by
  simp only [JGy_Gr_M0.Hash064.message,JGy_Gr_M0.Hash064.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast064_0,tail064]
#print axioms numeric064
theorem hash064 : JFp_SHADigest.digest input064=value064 := by
  unfold input064 JFp_SHADigest.digest
  rw [numeric064,JGy_Gr_M0.Hash064.checked]
  rfl
#print axioms hash064
theorem address064 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [177,116,4,114,61,106,88,108,118,62,192,61,211,197,68,169,43,161,77,216,92,76,54,202,145,17,143,238,105,129,100,173]) value054)=input064 := by rfl
#print axioms address064
def tree064 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [177,116,4,114,61,106,88,108,118,62,192,61,211,197,68,169,43,161,77,216,92,76,54,202,145,17,143,238,105,129,100,173])) tree054
theorem root064 : root JFp_SHADigest.digest tree064=value064 := by
  rw [tree064,root,root054]
  exact (congrArg JFp_SHADigest.digest address064).trans hash064
#print axioms root064
theorem shape064 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 183808=tree064 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 183808)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 183808 (by decide),siblings 5 (by decide) 183808 (by decide)]
  rw [shape054 f g inputs siblings]
  rfl
#print axioms shape064
def input065 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash065.message
def value065 : State := JFp_SHADigest.output JGy_Gr_M0.Hash065.result
theorem cast065_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash065.B00.input).map Fin.val=JGy_Gr_M0.Hash065.B00.input := by rfl
#print axioms cast065_0
theorem tail065 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash065.tail).map Fin.val=JGy_Gr_M0.Hash065.tail := by rfl
#print axioms tail065
theorem numeric065 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash065.message).map Fin.val=JGy_Gr_M0.Hash065.message := by
  simp only [JGy_Gr_M0.Hash065.message,JGy_Gr_M0.Hash065.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast065_0,tail065]
#print axioms numeric065
theorem hash065 : JFp_SHADigest.digest input065=value065 := by
  unfold input065 JFp_SHADigest.digest
  rw [numeric065,JGy_Gr_M0.Hash065.checked]
  rfl
#print axioms hash065
theorem address065 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [231,195,10,19,115,54,82,117,227,102,218,64,54,252,89,187,223,148,244,77,235,96,151,171,64,192,43,182,10,220,40,79]) value055)=input065 := by rfl
#print axioms address065
def tree065 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [231,195,10,19,115,54,82,117,227,102,218,64,54,252,89,187,223,148,244,77,235,96,151,171,64,192,43,182,10,220,40,79])) tree055
theorem root065 : root JFp_SHADigest.digest tree065=value065 := by
  rw [tree065,root,root055]
  exact (congrArg JFp_SHADigest.digest address065).trans hash065
#print axioms root065
theorem shape065 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 192256=tree065 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 192256)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 192256 (by decide),siblings 5 (by decide) 192256 (by decide)]
  rw [shape055 f g inputs siblings]
  rfl
#print axioms shape065
def input066 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash066.message
def value066 : State := JFp_SHADigest.output JGy_Gr_M0.Hash066.result
theorem cast066_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash066.B00.input).map Fin.val=JGy_Gr_M0.Hash066.B00.input := by rfl
#print axioms cast066_0
theorem tail066 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash066.tail).map Fin.val=JGy_Gr_M0.Hash066.tail := by rfl
#print axioms tail066
theorem numeric066 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash066.message).map Fin.val=JGy_Gr_M0.Hash066.message := by
  simp only [JGy_Gr_M0.Hash066.message,JGy_Gr_M0.Hash066.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast066_0,tail066]
#print axioms numeric066
theorem hash066 : JFp_SHADigest.digest input066=value066 := by
  unfold input066 JFp_SHADigest.digest
  rw [numeric066,JGy_Gr_M0.Hash066.checked]
  rfl
#print axioms hash066
theorem address066 : BinMerkle32Path.nodeInput (children value056 (JGc_TX2_HashBytes.state [151,95,38,140,31,5,121,26,212,129,37,16,148,199,129,176,150,84,199,90,102,60,240,239,124,65,170,220,30,127,98,162]))=input066 := by rfl
#print axioms address066
def tree066 : Tree := .branch tree056 (.supplied (JGc_TX2_HashBytes.state [151,95,38,140,31,5,121,26,212,129,37,16,148,199,129,176,150,84,199,90,102,60,240,239,124,65,170,220,30,127,98,162]))
theorem root066 : root JFp_SHADigest.digest tree066=value066 := by
  rw [tree066,root,root056]
  exact (congrArg JFp_SHADigest.digest address066).trans hash066
#print axioms root066
theorem shape066 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 193088=tree066 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 193088)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape056 f g inputs siblings]
  rw [unoccupied f g 5 193120 (by decide),siblings 5 (by decide) 193120 (by decide)]
  rfl
#print axioms shape066
def input067 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash067.message
def value067 : State := JFp_SHADigest.output JGy_Gr_M0.Hash067.result
theorem cast067_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash067.B00.input).map Fin.val=JGy_Gr_M0.Hash067.B00.input := by rfl
#print axioms cast067_0
theorem tail067 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash067.tail).map Fin.val=JGy_Gr_M0.Hash067.tail := by rfl
#print axioms tail067
theorem numeric067 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash067.message).map Fin.val=JGy_Gr_M0.Hash067.message := by
  simp only [JGy_Gr_M0.Hash067.message,JGy_Gr_M0.Hash067.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast067_0,tail067]
#print axioms numeric067
theorem hash067 : JFp_SHADigest.digest input067=value067 := by
  unfold input067 JFp_SHADigest.digest
  rw [numeric067,JGy_Gr_M0.Hash067.checked]
  rfl
#print axioms hash067
theorem address067 : BinMerkle32Path.nodeInput (children value057 (JGc_TX2_HashBytes.state [241,64,215,200,101,21,188,206,149,131,130,157,92,41,217,33,232,168,191,86,174,113,121,90,134,82,2,138,192,43,11,148]))=input067 := by rfl
#print axioms address067
def tree067 : Tree := .branch tree057 (.supplied (JGc_TX2_HashBytes.state [241,64,215,200,101,21,188,206,149,131,130,157,92,41,217,33,232,168,191,86,174,113,121,90,134,82,2,138,192,43,11,148]))
theorem root067 : root JFp_SHADigest.digest tree067=value067 := by
  rw [tree067,root,root057]
  exact (congrArg JFp_SHADigest.digest address067).trans hash067
#print axioms root067
theorem shape067 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 209344=tree067 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 209344)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape057 f g inputs siblings]
  rw [unoccupied f g 5 209376 (by decide),siblings 5 (by decide) 209376 (by decide)]
  rfl
#print axioms shape067
def input068 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash068.message
def value068 : State := JFp_SHADigest.output JGy_Gr_M0.Hash068.result
theorem cast068_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash068.B00.input).map Fin.val=JGy_Gr_M0.Hash068.B00.input := by rfl
#print axioms cast068_0
theorem tail068 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash068.tail).map Fin.val=JGy_Gr_M0.Hash068.tail := by rfl
#print axioms tail068
theorem numeric068 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash068.message).map Fin.val=JGy_Gr_M0.Hash068.message := by
  simp only [JGy_Gr_M0.Hash068.message,JGy_Gr_M0.Hash068.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast068_0,tail068]
#print axioms numeric068
theorem hash068 : JFp_SHADigest.digest input068=value068 := by
  unfold input068 JFp_SHADigest.digest
  rw [numeric068,JGy_Gr_M0.Hash068.checked]
  rfl
#print axioms hash068
theorem address068 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [154,13,206,49,223,9,254,76,182,88,42,161,203,130,30,27,176,4,101,162,115,71,35,86,137,49,8,23,137,228,38,97]) value058)=input068 := by rfl
#print axioms address068
def tree068 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [154,13,206,49,223,9,254,76,182,88,42,161,203,130,30,27,176,4,101,162,115,71,35,86,137,49,8,23,137,228,38,97])) tree058
theorem root068 : root JFp_SHADigest.digest tree068=value068 := by
  rw [tree068,root,root058]
  exact (congrArg JFp_SHADigest.digest address068).trans hash068
#print axioms root068
theorem shape068 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 216768=tree068 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 216768)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 216768 (by decide),siblings 5 (by decide) 216768 (by decide)]
  rw [shape058 f g inputs siblings]
  rfl
#print axioms shape068
def input069 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash069.message
def value069 : State := JFp_SHADigest.output JGy_Gr_M0.Hash069.result
theorem cast069_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash069.B00.input).map Fin.val=JGy_Gr_M0.Hash069.B00.input := by rfl
#print axioms cast069_0
theorem tail069 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash069.tail).map Fin.val=JGy_Gr_M0.Hash069.tail := by rfl
#print axioms tail069
theorem numeric069 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash069.message).map Fin.val=JGy_Gr_M0.Hash069.message := by
  simp only [JGy_Gr_M0.Hash069.message,JGy_Gr_M0.Hash069.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast069_0,tail069]
#print axioms numeric069
theorem hash069 : JFp_SHADigest.digest input069=value069 := by
  unfold input069 JFp_SHADigest.digest
  rw [numeric069,JGy_Gr_M0.Hash069.checked]
  rfl
#print axioms hash069
theorem address069 : BinMerkle32Path.nodeInput (children value059 (JGc_TX2_HashBytes.state [246,74,169,178,195,143,37,247,203,214,169,5,137,26,200,158,2,112,37,14,0,58,128,70,240,102,164,2,132,160,95,14]))=input069 := by rfl
#print axioms address069
def tree069 : Tree := .branch tree059 (.supplied (JGc_TX2_HashBytes.state [246,74,169,178,195,143,37,247,203,214,169,5,137,26,200,158,2,112,37,14,0,58,128,70,240,102,164,2,132,160,95,14]))
theorem root069 : root JFp_SHADigest.digest tree069=value069 := by
  rw [tree069,root,root059]
  exact (congrArg JFp_SHADigest.digest address069).trans hash069
#print axioms root069
theorem shape069 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 245888=tree069 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 245888)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape059 f g inputs siblings]
  rw [unoccupied f g 5 245920 (by decide),siblings 5 (by decide) 245920 (by decide)]
  rfl
#print axioms shape069
end AspisR1.JGy_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input070 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash070.message
def value070 : State := JFp_SHADigest.output JGy_Gr_M0.Hash070.result
theorem cast070_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash070.B00.input).map Fin.val=JGy_Gr_M0.Hash070.B00.input := by rfl
#print axioms cast070_0
theorem tail070 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash070.tail).map Fin.val=JGy_Gr_M0.Hash070.tail := by rfl
#print axioms tail070
theorem numeric070 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash070.message).map Fin.val=JGy_Gr_M0.Hash070.message := by
  simp only [JGy_Gr_M0.Hash070.message,JGy_Gr_M0.Hash070.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast070_0,tail070]
#print axioms numeric070
theorem hash070 : JFp_SHADigest.digest input070=value070 := by
  unfold input070 JFp_SHADigest.digest
  rw [numeric070,JGy_Gr_M0.Hash070.checked]
  rfl
#print axioms hash070
theorem address070 : BinMerkle32Path.nodeInput (children value060 (JGc_TX2_HashBytes.state [6,240,144,10,89,181,146,35,19,69,34,102,224,239,82,169,126,228,144,157,213,100,223,158,185,74,215,93,123,233,23,161]))=input070 := by rfl
#print axioms address070
def tree070 : Tree := .branch tree060 (.supplied (JGc_TX2_HashBytes.state [6,240,144,10,89,181,146,35,19,69,34,102,224,239,82,169,126,228,144,157,213,100,223,158,185,74,215,93,123,233,23,161]))
theorem root070 : root JFp_SHADigest.digest tree070=value070 := by
  rw [tree070,root,root060]
  exact (congrArg JFp_SHADigest.digest address070).trans hash070
#print axioms root070
theorem shape070 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 65536=tree070 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 65536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape060 f g inputs siblings]
  rw [unoccupied f g 6 65600 (by decide),siblings 6 (by decide) 65600 (by decide)]
  rfl
#print axioms shape070
def input071 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash071.message
def value071 : State := JFp_SHADigest.output JGy_Gr_M0.Hash071.result
theorem cast071_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash071.B00.input).map Fin.val=JGy_Gr_M0.Hash071.B00.input := by rfl
#print axioms cast071_0
theorem tail071 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash071.tail).map Fin.val=JGy_Gr_M0.Hash071.tail := by rfl
#print axioms tail071
theorem numeric071 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash071.message).map Fin.val=JGy_Gr_M0.Hash071.message := by
  simp only [JGy_Gr_M0.Hash071.message,JGy_Gr_M0.Hash071.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast071_0,tail071]
#print axioms numeric071
theorem hash071 : JFp_SHADigest.digest input071=value071 := by
  unfold input071 JFp_SHADigest.digest
  rw [numeric071,JGy_Gr_M0.Hash071.checked]
  rfl
#print axioms hash071
theorem address071 : BinMerkle32Path.nodeInput (children value061 (JGc_TX2_HashBytes.state [90,6,145,42,210,19,190,106,99,39,107,82,176,83,131,93,159,218,108,61,236,10,133,7,20,128,169,78,170,230,90,165]))=input071 := by rfl
#print axioms address071
def tree071 : Tree := .branch tree061 (.supplied (JGc_TX2_HashBytes.state [90,6,145,42,210,19,190,106,99,39,107,82,176,83,131,93,159,218,108,61,236,10,133,7,20,128,169,78,170,230,90,165]))
theorem root071 : root JFp_SHADigest.digest tree071=value071 := by
  rw [tree071,root,root061]
  exact (congrArg JFp_SHADigest.digest address071).trans hash071
#print axioms root071
theorem shape071 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 93440=tree071 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 93440)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape061 f g inputs siblings]
  rw [unoccupied f g 6 93504 (by decide),siblings 6 (by decide) 93504 (by decide)]
  rfl
#print axioms shape071
def input072 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash072.message
def value072 : State := JFp_SHADigest.output JGy_Gr_M0.Hash072.result
theorem cast072_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash072.B00.input).map Fin.val=JGy_Gr_M0.Hash072.B00.input := by rfl
#print axioms cast072_0
theorem tail072 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash072.tail).map Fin.val=JGy_Gr_M0.Hash072.tail := by rfl
#print axioms tail072
theorem numeric072 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash072.message).map Fin.val=JGy_Gr_M0.Hash072.message := by
  simp only [JGy_Gr_M0.Hash072.message,JGy_Gr_M0.Hash072.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast072_0,tail072]
#print axioms numeric072
theorem hash072 : JFp_SHADigest.digest input072=value072 := by
  unfold input072 JFp_SHADigest.digest
  rw [numeric072,JGy_Gr_M0.Hash072.checked]
  rfl
#print axioms hash072
theorem address072 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [196,128,247,200,205,132,186,20,133,103,68,116,144,157,48,190,208,40,165,211,155,245,88,90,127,113,249,133,5,38,245,231]) value062)=input072 := by rfl
#print axioms address072
def tree072 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [196,128,247,200,205,132,186,20,133,103,68,116,144,157,48,190,208,40,165,211,155,245,88,90,127,113,249,133,5,38,245,231])) tree062
theorem root072 : root JFp_SHADigest.digest tree072=value072 := by
  rw [tree072,root,root062]
  exact (congrArg JFp_SHADigest.digest address072).trans hash072
#print axioms root072
theorem shape072 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 147456=tree072 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 147456)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 147456 (by decide),siblings 6 (by decide) 147456 (by decide)]
  rw [shape062 f g inputs siblings]
  rfl
#print axioms shape072
def input073 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash073.message
def value073 : State := JFp_SHADigest.output JGy_Gr_M0.Hash073.result
theorem cast073_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash073.B00.input).map Fin.val=JGy_Gr_M0.Hash073.B00.input := by rfl
#print axioms cast073_0
theorem tail073 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash073.tail).map Fin.val=JGy_Gr_M0.Hash073.tail := by rfl
#print axioms tail073
theorem numeric073 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash073.message).map Fin.val=JGy_Gr_M0.Hash073.message := by
  simp only [JGy_Gr_M0.Hash073.message,JGy_Gr_M0.Hash073.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast073_0,tail073]
#print axioms numeric073
theorem hash073 : JFp_SHADigest.digest input073=value073 := by
  unfold input073 JFp_SHADigest.digest
  rw [numeric073,JGy_Gr_M0.Hash073.checked]
  rfl
#print axioms hash073
theorem address073 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [2,49,107,237,24,224,109,245,28,116,185,193,147,100,59,21,17,156,87,57,186,102,113,213,3,126,197,123,26,250,39,128]) value063)=input073 := by rfl
#print axioms address073
def tree073 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [2,49,107,237,24,224,109,245,28,116,185,193,147,100,59,21,17,156,87,57,186,102,113,213,3,126,197,123,26,250,39,128])) tree063
theorem root073 : root JFp_SHADigest.digest tree073=value073 := by
  rw [tree073,root,root063]
  exact (congrArg JFp_SHADigest.digest address073).trans hash073
#print axioms root073
theorem shape073 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 159744=tree073 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 159744)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 159744 (by decide),siblings 6 (by decide) 159744 (by decide)]
  rw [shape063 f g inputs siblings]
  rfl
#print axioms shape073
def input074 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash074.message
def value074 : State := JFp_SHADigest.output JGy_Gr_M0.Hash074.result
theorem cast074_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash074.B00.input).map Fin.val=JGy_Gr_M0.Hash074.B00.input := by rfl
#print axioms cast074_0
theorem tail074 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash074.tail).map Fin.val=JGy_Gr_M0.Hash074.tail := by rfl
#print axioms tail074
theorem numeric074 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash074.message).map Fin.val=JGy_Gr_M0.Hash074.message := by
  simp only [JGy_Gr_M0.Hash074.message,JGy_Gr_M0.Hash074.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast074_0,tail074]
#print axioms numeric074
theorem hash074 : JFp_SHADigest.digest input074=value074 := by
  unfold input074 JFp_SHADigest.digest
  rw [numeric074,JGy_Gr_M0.Hash074.checked]
  rfl
#print axioms hash074
theorem address074 : BinMerkle32Path.nodeInput (children value064 (JGc_TX2_HashBytes.state [136,31,229,129,117,15,123,172,12,255,204,60,56,41,146,141,133,147,183,231,229,23,88,42,114,153,55,180,204,108,193,174]))=input074 := by rfl
#print axioms address074
def tree074 : Tree := .branch tree064 (.supplied (JGc_TX2_HashBytes.state [136,31,229,129,117,15,123,172,12,255,204,60,56,41,146,141,133,147,183,231,229,23,88,42,114,153,55,180,204,108,193,174]))
theorem root074 : root JFp_SHADigest.digest tree074=value074 := by
  rw [tree074,root,root064]
  exact (congrArg JFp_SHADigest.digest address074).trans hash074
#print axioms root074
theorem shape074 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 183808=tree074 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 183808)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape064 f g inputs siblings]
  rw [unoccupied f g 6 183872 (by decide),siblings 6 (by decide) 183872 (by decide)]
  rfl
#print axioms shape074
def input075 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash075.message
def value075 : State := JFp_SHADigest.output JGy_Gr_M0.Hash075.result
theorem cast075_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash075.B00.input).map Fin.val=JGy_Gr_M0.Hash075.B00.input := by rfl
#print axioms cast075_0
theorem tail075 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash075.tail).map Fin.val=JGy_Gr_M0.Hash075.tail := by rfl
#print axioms tail075
theorem numeric075 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash075.message).map Fin.val=JGy_Gr_M0.Hash075.message := by
  simp only [JGy_Gr_M0.Hash075.message,JGy_Gr_M0.Hash075.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast075_0,tail075]
#print axioms numeric075
theorem hash075 : JFp_SHADigest.digest input075=value075 := by
  unfold input075 JFp_SHADigest.digest
  rw [numeric075,JGy_Gr_M0.Hash075.checked]
  rfl
#print axioms hash075
theorem address075 : BinMerkle32Path.nodeInput (children value065 (JGc_TX2_HashBytes.state [34,30,57,86,102,193,213,112,204,200,212,44,184,202,213,35,17,43,57,142,205,70,168,207,70,167,54,101,73,187,97,202]))=input075 := by rfl
#print axioms address075
def tree075 : Tree := .branch tree065 (.supplied (JGc_TX2_HashBytes.state [34,30,57,86,102,193,213,112,204,200,212,44,184,202,213,35,17,43,57,142,205,70,168,207,70,167,54,101,73,187,97,202]))
theorem root075 : root JFp_SHADigest.digest tree075=value075 := by
  rw [tree075,root,root065]
  exact (congrArg JFp_SHADigest.digest address075).trans hash075
#print axioms root075
theorem shape075 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 192256=tree075 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 192256)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape065 f g inputs siblings]
  rw [unoccupied f g 6 192320 (by decide),siblings 6 (by decide) 192320 (by decide)]
  rfl
#print axioms shape075
def input076 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash076.message
def value076 : State := JFp_SHADigest.output JGy_Gr_M0.Hash076.result
theorem cast076_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash076.B00.input).map Fin.val=JGy_Gr_M0.Hash076.B00.input := by rfl
#print axioms cast076_0
theorem tail076 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash076.tail).map Fin.val=JGy_Gr_M0.Hash076.tail := by rfl
#print axioms tail076
theorem numeric076 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash076.message).map Fin.val=JGy_Gr_M0.Hash076.message := by
  simp only [JGy_Gr_M0.Hash076.message,JGy_Gr_M0.Hash076.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast076_0,tail076]
#print axioms numeric076
theorem hash076 : JFp_SHADigest.digest input076=value076 := by
  unfold input076 JFp_SHADigest.digest
  rw [numeric076,JGy_Gr_M0.Hash076.checked]
  rfl
#print axioms hash076
theorem address076 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [92,210,92,203,65,9,235,116,179,182,0,221,48,101,150,142,75,48,236,28,93,37,5,154,73,46,86,46,88,149,55,187]) value066)=input076 := by rfl
#print axioms address076
def tree076 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [92,210,92,203,65,9,235,116,179,182,0,221,48,101,150,142,75,48,236,28,93,37,5,154,73,46,86,46,88,149,55,187])) tree066
theorem root076 : root JFp_SHADigest.digest tree076=value076 := by
  rw [tree076,root,root066]
  exact (congrArg JFp_SHADigest.digest address076).trans hash076
#print axioms root076
theorem shape076 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 193024=tree076 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 193024)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 193024 (by decide),siblings 6 (by decide) 193024 (by decide)]
  rw [shape066 f g inputs siblings]
  rfl
#print axioms shape076
def input077 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash077.message
def value077 : State := JFp_SHADigest.output JGy_Gr_M0.Hash077.result
theorem cast077_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash077.B00.input).map Fin.val=JGy_Gr_M0.Hash077.B00.input := by rfl
#print axioms cast077_0
theorem tail077 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash077.tail).map Fin.val=JGy_Gr_M0.Hash077.tail := by rfl
#print axioms tail077
theorem numeric077 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash077.message).map Fin.val=JGy_Gr_M0.Hash077.message := by
  simp only [JGy_Gr_M0.Hash077.message,JGy_Gr_M0.Hash077.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast077_0,tail077]
#print axioms numeric077
theorem hash077 : JFp_SHADigest.digest input077=value077 := by
  unfold input077 JFp_SHADigest.digest
  rw [numeric077,JGy_Gr_M0.Hash077.checked]
  rfl
#print axioms hash077
theorem address077 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [205,165,38,151,111,198,79,116,206,226,67,245,236,196,187,100,133,50,31,120,57,157,51,233,222,159,161,218,172,204,11,66]) value067)=input077 := by rfl
#print axioms address077
def tree077 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [205,165,38,151,111,198,79,116,206,226,67,245,236,196,187,100,133,50,31,120,57,157,51,233,222,159,161,218,172,204,11,66])) tree067
theorem root077 : root JFp_SHADigest.digest tree077=value077 := by
  rw [tree077,root,root067]
  exact (congrArg JFp_SHADigest.digest address077).trans hash077
#print axioms root077
theorem shape077 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 209280=tree077 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 209280)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 209280 (by decide),siblings 6 (by decide) 209280 (by decide)]
  rw [shape067 f g inputs siblings]
  rfl
#print axioms shape077
def input078 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash078.message
def value078 : State := JFp_SHADigest.output JGy_Gr_M0.Hash078.result
theorem cast078_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash078.B00.input).map Fin.val=JGy_Gr_M0.Hash078.B00.input := by rfl
#print axioms cast078_0
theorem tail078 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash078.tail).map Fin.val=JGy_Gr_M0.Hash078.tail := by rfl
#print axioms tail078
theorem numeric078 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash078.message).map Fin.val=JGy_Gr_M0.Hash078.message := by
  simp only [JGy_Gr_M0.Hash078.message,JGy_Gr_M0.Hash078.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast078_0,tail078]
#print axioms numeric078
theorem hash078 : JFp_SHADigest.digest input078=value078 := by
  unfold input078 JFp_SHADigest.digest
  rw [numeric078,JGy_Gr_M0.Hash078.checked]
  rfl
#print axioms hash078
theorem address078 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [226,108,77,28,131,136,7,58,77,240,220,71,105,254,22,209,107,74,73,188,176,248,183,95,174,54,121,81,95,90,24,102]) value068)=input078 := by rfl
#print axioms address078
def tree078 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [226,108,77,28,131,136,7,58,77,240,220,71,105,254,22,209,107,74,73,188,176,248,183,95,174,54,121,81,95,90,24,102])) tree068
theorem root078 : root JFp_SHADigest.digest tree078=value078 := by
  rw [tree078,root,root068]
  exact (congrArg JFp_SHADigest.digest address078).trans hash078
#print axioms root078
theorem shape078 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 216704=tree078 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 216704)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 216704 (by decide),siblings 6 (by decide) 216704 (by decide)]
  rw [shape068 f g inputs siblings]
  rfl
#print axioms shape078
def input079 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash079.message
def value079 : State := JFp_SHADigest.output JGy_Gr_M0.Hash079.result
theorem cast079_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash079.B00.input).map Fin.val=JGy_Gr_M0.Hash079.B00.input := by rfl
#print axioms cast079_0
theorem tail079 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash079.tail).map Fin.val=JGy_Gr_M0.Hash079.tail := by rfl
#print axioms tail079
theorem numeric079 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash079.message).map Fin.val=JGy_Gr_M0.Hash079.message := by
  simp only [JGy_Gr_M0.Hash079.message,JGy_Gr_M0.Hash079.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast079_0,tail079]
#print axioms numeric079
theorem hash079 : JFp_SHADigest.digest input079=value079 := by
  unfold input079 JFp_SHADigest.digest
  rw [numeric079,JGy_Gr_M0.Hash079.checked]
  rfl
#print axioms hash079
theorem address079 : BinMerkle32Path.nodeInput (children value069 (JGc_TX2_HashBytes.state [87,28,17,1,43,43,239,80,58,175,254,64,102,59,168,121,219,185,145,108,206,67,71,30,115,173,159,96,166,56,54,73]))=input079 := by rfl
#print axioms address079
def tree079 : Tree := .branch tree069 (.supplied (JGc_TX2_HashBytes.state [87,28,17,1,43,43,239,80,58,175,254,64,102,59,168,121,219,185,145,108,206,67,71,30,115,173,159,96,166,56,54,73]))
theorem root079 : root JFp_SHADigest.digest tree079=value079 := by
  rw [tree079,root,root069]
  exact (congrArg JFp_SHADigest.digest address079).trans hash079
#print axioms root079
theorem shape079 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 245888=tree079 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 245888)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape069 f g inputs siblings]
  rw [unoccupied f g 6 245952 (by decide),siblings 6 (by decide) 245952 (by decide)]
  rfl
#print axioms shape079
end AspisR1.JGy_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input080 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash080.message
def value080 : State := JFp_SHADigest.output JGy_Gr_M0.Hash080.result
theorem cast080_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash080.B00.input).map Fin.val=JGy_Gr_M0.Hash080.B00.input := by rfl
#print axioms cast080_0
theorem tail080 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash080.tail).map Fin.val=JGy_Gr_M0.Hash080.tail := by rfl
#print axioms tail080
theorem numeric080 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash080.message).map Fin.val=JGy_Gr_M0.Hash080.message := by
  simp only [JGy_Gr_M0.Hash080.message,JGy_Gr_M0.Hash080.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast080_0,tail080]
#print axioms numeric080
theorem hash080 : JFp_SHADigest.digest input080=value080 := by
  unfold input080 JFp_SHADigest.digest
  rw [numeric080,JGy_Gr_M0.Hash080.checked]
  rfl
#print axioms hash080
theorem address080 : BinMerkle32Path.nodeInput (children value070 (JGc_TX2_HashBytes.state [77,170,189,130,235,22,61,148,149,65,163,235,1,168,255,7,23,41,163,194,92,20,52,96,214,215,10,79,81,125,23,74]))=input080 := by rfl
#print axioms address080
def tree080 : Tree := .branch tree070 (.supplied (JGc_TX2_HashBytes.state [77,170,189,130,235,22,61,148,149,65,163,235,1,168,255,7,23,41,163,194,92,20,52,96,214,215,10,79,81,125,23,74]))
theorem root080 : root JFp_SHADigest.digest tree080=value080 := by
  rw [tree080,root,root070]
  exact (congrArg JFp_SHADigest.digest address080).trans hash080
#print axioms root080
theorem shape080 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 65536=tree080 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 65536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape070 f g inputs siblings]
  rw [unoccupied f g 7 65664 (by decide),siblings 7 (by decide) 65664 (by decide)]
  rfl
#print axioms shape080
def input081 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash081.message
def value081 : State := JFp_SHADigest.output JGy_Gr_M0.Hash081.result
theorem cast081_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash081.B00.input).map Fin.val=JGy_Gr_M0.Hash081.B00.input := by rfl
#print axioms cast081_0
theorem tail081 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash081.tail).map Fin.val=JGy_Gr_M0.Hash081.tail := by rfl
#print axioms tail081
theorem numeric081 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash081.message).map Fin.val=JGy_Gr_M0.Hash081.message := by
  simp only [JGy_Gr_M0.Hash081.message,JGy_Gr_M0.Hash081.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast081_0,tail081]
#print axioms numeric081
theorem hash081 : JFp_SHADigest.digest input081=value081 := by
  unfold input081 JFp_SHADigest.digest
  rw [numeric081,JGy_Gr_M0.Hash081.checked]
  rfl
#print axioms hash081
theorem address081 : BinMerkle32Path.nodeInput (children value071 (JGc_TX2_HashBytes.state [220,4,163,99,213,83,228,35,211,78,46,27,57,83,108,166,235,71,20,58,174,254,18,51,47,16,101,29,62,46,59,127]))=input081 := by rfl
#print axioms address081
def tree081 : Tree := .branch tree071 (.supplied (JGc_TX2_HashBytes.state [220,4,163,99,213,83,228,35,211,78,46,27,57,83,108,166,235,71,20,58,174,254,18,51,47,16,101,29,62,46,59,127]))
theorem root081 : root JFp_SHADigest.digest tree081=value081 := by
  rw [tree081,root,root071]
  exact (congrArg JFp_SHADigest.digest address081).trans hash081
#print axioms root081
theorem shape081 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 93440=tree081 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 93440)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape071 f g inputs siblings]
  rw [unoccupied f g 7 93568 (by decide),siblings 7 (by decide) 93568 (by decide)]
  rfl
#print axioms shape081
def input082 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash082.message
def value082 : State := JFp_SHADigest.output JGy_Gr_M0.Hash082.result
theorem cast082_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash082.B00.input).map Fin.val=JGy_Gr_M0.Hash082.B00.input := by rfl
#print axioms cast082_0
theorem tail082 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash082.tail).map Fin.val=JGy_Gr_M0.Hash082.tail := by rfl
#print axioms tail082
theorem numeric082 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash082.message).map Fin.val=JGy_Gr_M0.Hash082.message := by
  simp only [JGy_Gr_M0.Hash082.message,JGy_Gr_M0.Hash082.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast082_0,tail082]
#print axioms numeric082
theorem hash082 : JFp_SHADigest.digest input082=value082 := by
  unfold input082 JFp_SHADigest.digest
  rw [numeric082,JGy_Gr_M0.Hash082.checked]
  rfl
#print axioms hash082
theorem address082 : BinMerkle32Path.nodeInput (children value072 (JGc_TX2_HashBytes.state [8,32,93,135,247,254,167,22,175,205,245,1,51,185,169,99,158,32,144,204,248,6,73,82,86,253,11,31,112,23,182,248]))=input082 := by rfl
#print axioms address082
def tree082 : Tree := .branch tree072 (.supplied (JGc_TX2_HashBytes.state [8,32,93,135,247,254,167,22,175,205,245,1,51,185,169,99,158,32,144,204,248,6,73,82,86,253,11,31,112,23,182,248]))
theorem root082 : root JFp_SHADigest.digest tree082=value082 := by
  rw [tree082,root,root072]
  exact (congrArg JFp_SHADigest.digest address082).trans hash082
#print axioms root082
theorem shape082 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 147456=tree082 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 147456)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape072 f g inputs siblings]
  rw [unoccupied f g 7 147584 (by decide),siblings 7 (by decide) 147584 (by decide)]
  rfl
#print axioms shape082
def input083 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash083.message
def value083 : State := JFp_SHADigest.output JGy_Gr_M0.Hash083.result
theorem cast083_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash083.B00.input).map Fin.val=JGy_Gr_M0.Hash083.B00.input := by rfl
#print axioms cast083_0
theorem tail083 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash083.tail).map Fin.val=JGy_Gr_M0.Hash083.tail := by rfl
#print axioms tail083
theorem numeric083 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash083.message).map Fin.val=JGy_Gr_M0.Hash083.message := by
  simp only [JGy_Gr_M0.Hash083.message,JGy_Gr_M0.Hash083.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast083_0,tail083]
#print axioms numeric083
theorem hash083 : JFp_SHADigest.digest input083=value083 := by
  unfold input083 JFp_SHADigest.digest
  rw [numeric083,JGy_Gr_M0.Hash083.checked]
  rfl
#print axioms hash083
theorem address083 : BinMerkle32Path.nodeInput (children value073 (JGc_TX2_HashBytes.state [237,7,29,17,196,126,123,186,28,187,171,89,156,231,137,55,83,50,16,209,36,156,194,167,84,36,109,35,86,123,184,82]))=input083 := by rfl
#print axioms address083
def tree083 : Tree := .branch tree073 (.supplied (JGc_TX2_HashBytes.state [237,7,29,17,196,126,123,186,28,187,171,89,156,231,137,55,83,50,16,209,36,156,194,167,84,36,109,35,86,123,184,82]))
theorem root083 : root JFp_SHADigest.digest tree083=value083 := by
  rw [tree083,root,root073]
  exact (congrArg JFp_SHADigest.digest address083).trans hash083
#print axioms root083
theorem shape083 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 159744=tree083 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 159744)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape073 f g inputs siblings]
  rw [unoccupied f g 7 159872 (by decide),siblings 7 (by decide) 159872 (by decide)]
  rfl
#print axioms shape083
def input084 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash084.message
def value084 : State := JFp_SHADigest.output JGy_Gr_M0.Hash084.result
theorem cast084_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash084.B00.input).map Fin.val=JGy_Gr_M0.Hash084.B00.input := by rfl
#print axioms cast084_0
theorem tail084 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash084.tail).map Fin.val=JGy_Gr_M0.Hash084.tail := by rfl
#print axioms tail084
theorem numeric084 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash084.message).map Fin.val=JGy_Gr_M0.Hash084.message := by
  simp only [JGy_Gr_M0.Hash084.message,JGy_Gr_M0.Hash084.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast084_0,tail084]
#print axioms numeric084
theorem hash084 : JFp_SHADigest.digest input084=value084 := by
  unfold input084 JFp_SHADigest.digest
  rw [numeric084,JGy_Gr_M0.Hash084.checked]
  rfl
#print axioms hash084
theorem address084 : BinMerkle32Path.nodeInput (children value074 (JGc_TX2_HashBytes.state [164,143,95,212,102,248,18,5,14,206,35,160,137,216,216,140,138,220,155,8,95,80,232,194,90,93,3,211,167,239,202,54]))=input084 := by rfl
#print axioms address084
def tree084 : Tree := .branch tree074 (.supplied (JGc_TX2_HashBytes.state [164,143,95,212,102,248,18,5,14,206,35,160,137,216,216,140,138,220,155,8,95,80,232,194,90,93,3,211,167,239,202,54]))
theorem root084 : root JFp_SHADigest.digest tree084=value084 := by
  rw [tree084,root,root074]
  exact (congrArg JFp_SHADigest.digest address084).trans hash084
#print axioms root084
theorem shape084 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 183808=tree084 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 183808)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape074 f g inputs siblings]
  rw [unoccupied f g 7 183936 (by decide),siblings 7 (by decide) 183936 (by decide)]
  rfl
#print axioms shape084
def input085 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash085.message
def value085 : State := JFp_SHADigest.output JGy_Gr_M0.Hash085.result
theorem cast085_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash085.B00.input).map Fin.val=JGy_Gr_M0.Hash085.B00.input := by rfl
#print axioms cast085_0
theorem tail085 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash085.tail).map Fin.val=JGy_Gr_M0.Hash085.tail := by rfl
#print axioms tail085
theorem numeric085 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash085.message).map Fin.val=JGy_Gr_M0.Hash085.message := by
  simp only [JGy_Gr_M0.Hash085.message,JGy_Gr_M0.Hash085.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast085_0,tail085]
#print axioms numeric085
theorem hash085 : JFp_SHADigest.digest input085=value085 := by
  unfold input085 JFp_SHADigest.digest
  rw [numeric085,JGy_Gr_M0.Hash085.checked]
  rfl
#print axioms hash085
theorem address085 : BinMerkle32Path.nodeInput (children value075 (JGc_TX2_HashBytes.state [112,33,7,3,28,71,221,2,47,93,159,111,101,209,164,115,182,37,12,24,179,5,186,191,241,44,19,167,238,76,32,192]))=input085 := by rfl
#print axioms address085
def tree085 : Tree := .branch tree075 (.supplied (JGc_TX2_HashBytes.state [112,33,7,3,28,71,221,2,47,93,159,111,101,209,164,115,182,37,12,24,179,5,186,191,241,44,19,167,238,76,32,192]))
theorem root085 : root JFp_SHADigest.digest tree085=value085 := by
  rw [tree085,root,root075]
  exact (congrArg JFp_SHADigest.digest address085).trans hash085
#print axioms root085
theorem shape085 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 192256=tree085 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 192256)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape075 f g inputs siblings]
  rw [unoccupied f g 7 192384 (by decide),siblings 7 (by decide) 192384 (by decide)]
  rfl
#print axioms shape085
def input086 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash086.message
def value086 : State := JFp_SHADigest.output JGy_Gr_M0.Hash086.result
theorem cast086_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash086.B00.input).map Fin.val=JGy_Gr_M0.Hash086.B00.input := by rfl
#print axioms cast086_0
theorem tail086 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash086.tail).map Fin.val=JGy_Gr_M0.Hash086.tail := by rfl
#print axioms tail086
theorem numeric086 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash086.message).map Fin.val=JGy_Gr_M0.Hash086.message := by
  simp only [JGy_Gr_M0.Hash086.message,JGy_Gr_M0.Hash086.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast086_0,tail086]
#print axioms numeric086
theorem hash086 : JFp_SHADigest.digest input086=value086 := by
  unfold input086 JFp_SHADigest.digest
  rw [numeric086,JGy_Gr_M0.Hash086.checked]
  rfl
#print axioms hash086
theorem address086 : BinMerkle32Path.nodeInput (children value076 (JGc_TX2_HashBytes.state [74,175,62,170,208,166,232,20,189,64,80,118,215,50,80,8,224,151,209,81,20,7,185,85,124,62,24,188,176,43,92,225]))=input086 := by rfl
#print axioms address086
def tree086 : Tree := .branch tree076 (.supplied (JGc_TX2_HashBytes.state [74,175,62,170,208,166,232,20,189,64,80,118,215,50,80,8,224,151,209,81,20,7,185,85,124,62,24,188,176,43,92,225]))
theorem root086 : root JFp_SHADigest.digest tree086=value086 := by
  rw [tree086,root,root076]
  exact (congrArg JFp_SHADigest.digest address086).trans hash086
#print axioms root086
theorem shape086 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 193024=tree086 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 193024)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape076 f g inputs siblings]
  rw [unoccupied f g 7 193152 (by decide),siblings 7 (by decide) 193152 (by decide)]
  rfl
#print axioms shape086
def input087 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash087.message
def value087 : State := JFp_SHADigest.output JGy_Gr_M0.Hash087.result
theorem cast087_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash087.B00.input).map Fin.val=JGy_Gr_M0.Hash087.B00.input := by rfl
#print axioms cast087_0
theorem tail087 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash087.tail).map Fin.val=JGy_Gr_M0.Hash087.tail := by rfl
#print axioms tail087
theorem numeric087 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash087.message).map Fin.val=JGy_Gr_M0.Hash087.message := by
  simp only [JGy_Gr_M0.Hash087.message,JGy_Gr_M0.Hash087.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast087_0,tail087]
#print axioms numeric087
theorem hash087 : JFp_SHADigest.digest input087=value087 := by
  unfold input087 JFp_SHADigest.digest
  rw [numeric087,JGy_Gr_M0.Hash087.checked]
  rfl
#print axioms hash087
theorem address087 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [218,253,65,240,172,229,138,129,76,204,176,47,148,25,169,129,220,198,33,211,14,132,216,254,101,36,143,228,205,218,132,45]) value077)=input087 := by rfl
#print axioms address087
def tree087 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [218,253,65,240,172,229,138,129,76,204,176,47,148,25,169,129,220,198,33,211,14,132,216,254,101,36,143,228,205,218,132,45])) tree077
theorem root087 : root JFp_SHADigest.digest tree087=value087 := by
  rw [tree087,root,root077]
  exact (congrArg JFp_SHADigest.digest address087).trans hash087
#print axioms root087
theorem shape087 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 209152=tree087 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 209152)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 7 209152 (by decide),siblings 7 (by decide) 209152 (by decide)]
  rw [shape077 f g inputs siblings]
  rfl
#print axioms shape087
def input088 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash088.message
def value088 : State := JFp_SHADigest.output JGy_Gr_M0.Hash088.result
theorem cast088_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash088.B00.input).map Fin.val=JGy_Gr_M0.Hash088.B00.input := by rfl
#print axioms cast088_0
theorem tail088 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash088.tail).map Fin.val=JGy_Gr_M0.Hash088.tail := by rfl
#print axioms tail088
theorem numeric088 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash088.message).map Fin.val=JGy_Gr_M0.Hash088.message := by
  simp only [JGy_Gr_M0.Hash088.message,JGy_Gr_M0.Hash088.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast088_0,tail088]
#print axioms numeric088
theorem hash088 : JFp_SHADigest.digest input088=value088 := by
  unfold input088 JFp_SHADigest.digest
  rw [numeric088,JGy_Gr_M0.Hash088.checked]
  rfl
#print axioms hash088
theorem address088 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [92,111,165,106,142,29,249,211,6,148,240,59,145,1,129,21,239,41,72,97,151,216,109,27,177,211,241,204,132,133,92,249]) value078)=input088 := by rfl
#print axioms address088
def tree088 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [92,111,165,106,142,29,249,211,6,148,240,59,145,1,129,21,239,41,72,97,151,216,109,27,177,211,241,204,132,133,92,249])) tree078
theorem root088 : root JFp_SHADigest.digest tree088=value088 := by
  rw [tree088,root,root078]
  exact (congrArg JFp_SHADigest.digest address088).trans hash088
#print axioms root088
theorem shape088 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 216576=tree088 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 216576)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 7 216576 (by decide),siblings 7 (by decide) 216576 (by decide)]
  rw [shape078 f g inputs siblings]
  rfl
#print axioms shape088
def input089 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash089.message
def value089 : State := JFp_SHADigest.output JGy_Gr_M0.Hash089.result
theorem cast089_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash089.B00.input).map Fin.val=JGy_Gr_M0.Hash089.B00.input := by rfl
#print axioms cast089_0
theorem tail089 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash089.tail).map Fin.val=JGy_Gr_M0.Hash089.tail := by rfl
#print axioms tail089
theorem numeric089 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash089.message).map Fin.val=JGy_Gr_M0.Hash089.message := by
  simp only [JGy_Gr_M0.Hash089.message,JGy_Gr_M0.Hash089.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast089_0,tail089]
#print axioms numeric089
theorem hash089 : JFp_SHADigest.digest input089=value089 := by
  unfold input089 JFp_SHADigest.digest
  rw [numeric089,JGy_Gr_M0.Hash089.checked]
  rfl
#print axioms hash089
theorem address089 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [15,149,178,185,103,188,80,183,213,234,175,109,95,91,156,29,122,205,226,127,154,135,172,211,157,76,137,128,192,230,142,182]) value079)=input089 := by rfl
#print axioms address089
def tree089 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [15,149,178,185,103,188,80,183,213,234,175,109,95,91,156,29,122,205,226,127,154,135,172,211,157,76,137,128,192,230,142,182])) tree079
theorem root089 : root JFp_SHADigest.digest tree089=value089 := by
  rw [tree089,root,root079]
  exact (congrArg JFp_SHADigest.digest address089).trans hash089
#print axioms root089
theorem shape089 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 245760=tree089 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 245760)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 7 245760 (by decide),siblings 7 (by decide) 245760 (by decide)]
  rw [shape079 f g inputs siblings]
  rfl
#print axioms shape089
end AspisR1.JGy_Gr_M0Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input090 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash090.message
def value090 : State := JFp_SHADigest.output JGy_Gr_M0.Hash090.result
theorem cast090_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash090.B00.input).map Fin.val=JGy_Gr_M0.Hash090.B00.input := by rfl
#print axioms cast090_0
theorem tail090 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash090.tail).map Fin.val=JGy_Gr_M0.Hash090.tail := by rfl
#print axioms tail090
theorem numeric090 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash090.message).map Fin.val=JGy_Gr_M0.Hash090.message := by
  simp only [JGy_Gr_M0.Hash090.message,JGy_Gr_M0.Hash090.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast090_0,tail090]
#print axioms numeric090
theorem hash090 : JFp_SHADigest.digest input090=value090 := by
  unfold input090 JFp_SHADigest.digest
  rw [numeric090,JGy_Gr_M0.Hash090.checked]
  rfl
#print axioms hash090
theorem address090 : BinMerkle32Path.nodeInput (children value080 (JGc_TX2_HashBytes.state [113,23,49,153,65,62,50,121,121,134,77,85,4,221,172,58,119,143,25,248,30,111,211,227,9,191,95,71,39,81,225,50]))=input090 := by rfl
#print axioms address090
def tree090 : Tree := .branch tree080 (.supplied (JGc_TX2_HashBytes.state [113,23,49,153,65,62,50,121,121,134,77,85,4,221,172,58,119,143,25,248,30,111,211,227,9,191,95,71,39,81,225,50]))
theorem root090 : root JFp_SHADigest.digest tree090=value090 := by
  rw [tree090,root,root080]
  exact (congrArg JFp_SHADigest.digest address090).trans hash090
#print axioms root090
theorem shape090 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 65536=tree090 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 65536)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape080 f g inputs siblings]
  rw [unoccupied f g 8 65792 (by decide),siblings 8 (by decide) 65792 (by decide)]
  rfl
#print axioms shape090
def input091 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash091.message
def value091 : State := JFp_SHADigest.output JGy_Gr_M0.Hash091.result
theorem cast091_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash091.B00.input).map Fin.val=JGy_Gr_M0.Hash091.B00.input := by rfl
#print axioms cast091_0
theorem tail091 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash091.tail).map Fin.val=JGy_Gr_M0.Hash091.tail := by rfl
#print axioms tail091
theorem numeric091 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash091.message).map Fin.val=JGy_Gr_M0.Hash091.message := by
  simp only [JGy_Gr_M0.Hash091.message,JGy_Gr_M0.Hash091.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast091_0,tail091]
#print axioms numeric091
theorem hash091 : JFp_SHADigest.digest input091=value091 := by
  unfold input091 JFp_SHADigest.digest
  rw [numeric091,JGy_Gr_M0.Hash091.checked]
  rfl
#print axioms hash091
theorem address091 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [17,86,79,88,53,63,109,64,216,191,11,30,55,109,89,48,69,42,142,22,51,233,130,145,169,63,100,38,75,249,74,19]) value081)=input091 := by rfl
#print axioms address091
def tree091 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [17,86,79,88,53,63,109,64,216,191,11,30,55,109,89,48,69,42,142,22,51,233,130,145,169,63,100,38,75,249,74,19])) tree081
theorem root091 : root JFp_SHADigest.digest tree091=value091 := by
  rw [tree091,root,root081]
  exact (congrArg JFp_SHADigest.digest address091).trans hash091
#print axioms root091
theorem shape091 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 93184=tree091 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 93184)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 93184 (by decide),siblings 8 (by decide) 93184 (by decide)]
  rw [shape081 f g inputs siblings]
  rfl
#print axioms shape091
def input092 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash092.message
def value092 : State := JFp_SHADigest.output JGy_Gr_M0.Hash092.result
theorem cast092_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash092.B00.input).map Fin.val=JGy_Gr_M0.Hash092.B00.input := by rfl
#print axioms cast092_0
theorem tail092 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash092.tail).map Fin.val=JGy_Gr_M0.Hash092.tail := by rfl
#print axioms tail092
theorem numeric092 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash092.message).map Fin.val=JGy_Gr_M0.Hash092.message := by
  simp only [JGy_Gr_M0.Hash092.message,JGy_Gr_M0.Hash092.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast092_0,tail092]
#print axioms numeric092
theorem hash092 : JFp_SHADigest.digest input092=value092 := by
  unfold input092 JFp_SHADigest.digest
  rw [numeric092,JGy_Gr_M0.Hash092.checked]
  rfl
#print axioms hash092
theorem address092 : BinMerkle32Path.nodeInput (children value082 (JGc_TX2_HashBytes.state [226,155,182,235,137,88,156,193,14,203,121,8,103,202,235,239,155,117,229,172,214,169,41,35,14,166,228,96,191,226,79,63]))=input092 := by rfl
#print axioms address092
def tree092 : Tree := .branch tree082 (.supplied (JGc_TX2_HashBytes.state [226,155,182,235,137,88,156,193,14,203,121,8,103,202,235,239,155,117,229,172,214,169,41,35,14,166,228,96,191,226,79,63]))
theorem root092 : root JFp_SHADigest.digest tree092=value092 := by
  rw [tree092,root,root082]
  exact (congrArg JFp_SHADigest.digest address092).trans hash092
#print axioms root092
theorem shape092 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 147456=tree092 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 147456)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape082 f g inputs siblings]
  rw [unoccupied f g 8 147712 (by decide),siblings 8 (by decide) 147712 (by decide)]
  rfl
#print axioms shape092
def input093 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash093.message
def value093 : State := JFp_SHADigest.output JGy_Gr_M0.Hash093.result
theorem cast093_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash093.B00.input).map Fin.val=JGy_Gr_M0.Hash093.B00.input := by rfl
#print axioms cast093_0
theorem tail093 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash093.tail).map Fin.val=JGy_Gr_M0.Hash093.tail := by rfl
#print axioms tail093
theorem numeric093 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash093.message).map Fin.val=JGy_Gr_M0.Hash093.message := by
  simp only [JGy_Gr_M0.Hash093.message,JGy_Gr_M0.Hash093.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast093_0,tail093]
#print axioms numeric093
theorem hash093 : JFp_SHADigest.digest input093=value093 := by
  unfold input093 JFp_SHADigest.digest
  rw [numeric093,JGy_Gr_M0.Hash093.checked]
  rfl
#print axioms hash093
theorem address093 : BinMerkle32Path.nodeInput (children value083 (JGc_TX2_HashBytes.state [126,121,251,104,220,255,47,155,0,110,75,75,75,176,125,193,113,66,44,179,9,60,208,17,238,130,66,26,194,98,247,255]))=input093 := by rfl
#print axioms address093
def tree093 : Tree := .branch tree083 (.supplied (JGc_TX2_HashBytes.state [126,121,251,104,220,255,47,155,0,110,75,75,75,176,125,193,113,66,44,179,9,60,208,17,238,130,66,26,194,98,247,255]))
theorem root093 : root JFp_SHADigest.digest tree093=value093 := by
  rw [tree093,root,root083]
  exact (congrArg JFp_SHADigest.digest address093).trans hash093
#print axioms root093
theorem shape093 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 159744=tree093 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 159744)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape083 f g inputs siblings]
  rw [unoccupied f g 8 160000 (by decide),siblings 8 (by decide) 160000 (by decide)]
  rfl
#print axioms shape093
def input094 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash094.message
def value094 : State := JFp_SHADigest.output JGy_Gr_M0.Hash094.result
theorem cast094_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash094.B00.input).map Fin.val=JGy_Gr_M0.Hash094.B00.input := by rfl
#print axioms cast094_0
theorem tail094 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash094.tail).map Fin.val=JGy_Gr_M0.Hash094.tail := by rfl
#print axioms tail094
theorem numeric094 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash094.message).map Fin.val=JGy_Gr_M0.Hash094.message := by
  simp only [JGy_Gr_M0.Hash094.message,JGy_Gr_M0.Hash094.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast094_0,tail094]
#print axioms numeric094
theorem hash094 : JFp_SHADigest.digest input094=value094 := by
  unfold input094 JFp_SHADigest.digest
  rw [numeric094,JGy_Gr_M0.Hash094.checked]
  rfl
#print axioms hash094
theorem address094 : BinMerkle32Path.nodeInput (children value084 (JGc_TX2_HashBytes.state [158,176,11,125,66,96,99,8,73,93,247,85,166,153,219,250,17,121,222,96,4,149,255,161,250,23,46,233,243,21,255,119]))=input094 := by rfl
#print axioms address094
def tree094 : Tree := .branch tree084 (.supplied (JGc_TX2_HashBytes.state [158,176,11,125,66,96,99,8,73,93,247,85,166,153,219,250,17,121,222,96,4,149,255,161,250,23,46,233,243,21,255,119]))
theorem root094 : root JFp_SHADigest.digest tree094=value094 := by
  rw [tree094,root,root084]
  exact (congrArg JFp_SHADigest.digest address094).trans hash094
#print axioms root094
theorem shape094 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 183808=tree094 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 183808)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape084 f g inputs siblings]
  rw [unoccupied f g 8 184064 (by decide),siblings 8 (by decide) 184064 (by decide)]
  rfl
#print axioms shape094
def input095 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash095.message
def value095 : State := JFp_SHADigest.output JGy_Gr_M0.Hash095.result
theorem cast095_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash095.B00.input).map Fin.val=JGy_Gr_M0.Hash095.B00.input := by rfl
#print axioms cast095_0
theorem tail095 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash095.tail).map Fin.val=JGy_Gr_M0.Hash095.tail := by rfl
#print axioms tail095
theorem numeric095 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash095.message).map Fin.val=JGy_Gr_M0.Hash095.message := by
  simp only [JGy_Gr_M0.Hash095.message,JGy_Gr_M0.Hash095.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast095_0,tail095]
#print axioms numeric095
theorem hash095 : JFp_SHADigest.digest input095=value095 := by
  unfold input095 JFp_SHADigest.digest
  rw [numeric095,JGy_Gr_M0.Hash095.checked]
  rfl
#print axioms hash095
theorem address095 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [207,177,176,60,127,81,118,135,169,148,236,21,219,140,173,74,233,123,232,214,172,56,152,55,156,176,4,122,1,49,209,83]) value085)=input095 := by rfl
#print axioms address095
def tree095 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [207,177,176,60,127,81,118,135,169,148,236,21,219,140,173,74,233,123,232,214,172,56,152,55,156,176,4,122,1,49,209,83])) tree085
theorem root095 : root JFp_SHADigest.digest tree095=value095 := by
  rw [tree095,root,root085]
  exact (congrArg JFp_SHADigest.digest address095).trans hash095
#print axioms root095
theorem shape095 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 192000=tree095 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 192000)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 192000 (by decide),siblings 8 (by decide) 192000 (by decide)]
  rw [shape085 f g inputs siblings]
  rfl
#print axioms shape095
def input096 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash096.message
def value096 : State := JFp_SHADigest.output JGy_Gr_M0.Hash096.result
theorem cast096_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash096.B00.input).map Fin.val=JGy_Gr_M0.Hash096.B00.input := by rfl
#print axioms cast096_0
theorem tail096 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash096.tail).map Fin.val=JGy_Gr_M0.Hash096.tail := by rfl
#print axioms tail096
theorem numeric096 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash096.message).map Fin.val=JGy_Gr_M0.Hash096.message := by
  simp only [JGy_Gr_M0.Hash096.message,JGy_Gr_M0.Hash096.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast096_0,tail096]
#print axioms numeric096
theorem hash096 : JFp_SHADigest.digest input096=value096 := by
  unfold input096 JFp_SHADigest.digest
  rw [numeric096,JGy_Gr_M0.Hash096.checked]
  rfl
#print axioms hash096
theorem address096 : BinMerkle32Path.nodeInput (children value086 (JGc_TX2_HashBytes.state [65,182,123,189,84,7,216,217,132,96,18,74,118,7,3,237,94,9,129,18,202,71,166,195,20,119,229,148,187,131,19,241]))=input096 := by rfl
#print axioms address096
def tree096 : Tree := .branch tree086 (.supplied (JGc_TX2_HashBytes.state [65,182,123,189,84,7,216,217,132,96,18,74,118,7,3,237,94,9,129,18,202,71,166,195,20,119,229,148,187,131,19,241]))
theorem root096 : root JFp_SHADigest.digest tree096=value096 := by
  rw [tree096,root,root086]
  exact (congrArg JFp_SHADigest.digest address096).trans hash096
#print axioms root096
theorem shape096 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 193024=tree096 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 193024)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape086 f g inputs siblings]
  rw [unoccupied f g 8 193280 (by decide),siblings 8 (by decide) 193280 (by decide)]
  rfl
#print axioms shape096
def input097 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash097.message
def value097 : State := JFp_SHADigest.output JGy_Gr_M0.Hash097.result
theorem cast097_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash097.B00.input).map Fin.val=JGy_Gr_M0.Hash097.B00.input := by rfl
#print axioms cast097_0
theorem tail097 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash097.tail).map Fin.val=JGy_Gr_M0.Hash097.tail := by rfl
#print axioms tail097
theorem numeric097 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash097.message).map Fin.val=JGy_Gr_M0.Hash097.message := by
  simp only [JGy_Gr_M0.Hash097.message,JGy_Gr_M0.Hash097.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast097_0,tail097]
#print axioms numeric097
theorem hash097 : JFp_SHADigest.digest input097=value097 := by
  unfold input097 JFp_SHADigest.digest
  rw [numeric097,JGy_Gr_M0.Hash097.checked]
  rfl
#print axioms hash097
theorem address097 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [151,189,242,15,48,2,126,127,42,140,208,198,249,228,165,254,222,43,136,1,116,49,161,30,227,32,117,1,201,85,56,26]) value087)=input097 := by rfl
#print axioms address097
def tree097 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [151,189,242,15,48,2,126,127,42,140,208,198,249,228,165,254,222,43,136,1,116,49,161,30,227,32,117,1,201,85,56,26])) tree087
theorem root097 : root JFp_SHADigest.digest tree097=value097 := by
  rw [tree097,root,root087]
  exact (congrArg JFp_SHADigest.digest address097).trans hash097
#print axioms root097
theorem shape097 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 208896=tree097 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 208896)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 208896 (by decide),siblings 8 (by decide) 208896 (by decide)]
  rw [shape087 f g inputs siblings]
  rfl
#print axioms shape097
def input098 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash098.message
def value098 : State := JFp_SHADigest.output JGy_Gr_M0.Hash098.result
theorem cast098_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash098.B00.input).map Fin.val=JGy_Gr_M0.Hash098.B00.input := by rfl
#print axioms cast098_0
theorem tail098 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash098.tail).map Fin.val=JGy_Gr_M0.Hash098.tail := by rfl
#print axioms tail098
theorem numeric098 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash098.message).map Fin.val=JGy_Gr_M0.Hash098.message := by
  simp only [JGy_Gr_M0.Hash098.message,JGy_Gr_M0.Hash098.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast098_0,tail098]
#print axioms numeric098
theorem hash098 : JFp_SHADigest.digest input098=value098 := by
  unfold input098 JFp_SHADigest.digest
  rw [numeric098,JGy_Gr_M0.Hash098.checked]
  rfl
#print axioms hash098
theorem address098 : BinMerkle32Path.nodeInput (children value088 (JGc_TX2_HashBytes.state [46,78,225,61,74,143,106,41,11,1,157,44,41,247,155,126,43,181,1,160,152,29,224,187,122,141,106,211,167,157,239,161]))=input098 := by rfl
#print axioms address098
def tree098 : Tree := .branch tree088 (.supplied (JGc_TX2_HashBytes.state [46,78,225,61,74,143,106,41,11,1,157,44,41,247,155,126,43,181,1,160,152,29,224,187,122,141,106,211,167,157,239,161]))
theorem root098 : root JFp_SHADigest.digest tree098=value098 := by
  rw [tree098,root,root088]
  exact (congrArg JFp_SHADigest.digest address098).trans hash098
#print axioms root098
theorem shape098 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 216576=tree098 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 216576)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape088 f g inputs siblings]
  rw [unoccupied f g 8 216832 (by decide),siblings 8 (by decide) 216832 (by decide)]
  rfl
#print axioms shape098
def input099 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash099.message
def value099 : State := JFp_SHADigest.output JGy_Gr_M0.Hash099.result
theorem cast099_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash099.B00.input).map Fin.val=JGy_Gr_M0.Hash099.B00.input := by rfl
#print axioms cast099_0
theorem tail099 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash099.tail).map Fin.val=JGy_Gr_M0.Hash099.tail := by rfl
#print axioms tail099
theorem numeric099 : (JGc_TX2_HashBytes.bytes JGy_Gr_M0.Hash099.message).map Fin.val=JGy_Gr_M0.Hash099.message := by
  simp only [JGy_Gr_M0.Hash099.message,JGy_Gr_M0.Hash099.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast099_0,tail099]
#print axioms numeric099
theorem hash099 : JFp_SHADigest.digest input099=value099 := by
  unfold input099 JFp_SHADigest.digest
  rw [numeric099,JGy_Gr_M0.Hash099.checked]
  rfl
#print axioms hash099
theorem address099 : BinMerkle32Path.nodeInput (children value089 (JGc_TX2_HashBytes.state [8,249,218,86,52,33,101,166,203,237,91,36,157,221,19,10,53,117,89,94,91,68,66,227,193,115,151,105,136,220,126,108]))=input099 := by rfl
#print axioms address099
def tree099 : Tree := .branch tree089 (.supplied (JGc_TX2_HashBytes.state [8,249,218,86,52,33,101,166,203,237,91,36,157,221,19,10,53,117,89,94,91,68,66,227,193,115,151,105,136,220,126,108]))
theorem root099 : root JFp_SHADigest.digest tree099=value099 := by
  rw [tree099,root,root089]
  exact (congrArg JFp_SHADigest.digest address099).trans hash099
#print axioms root099
theorem shape099 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 245760=tree099 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 245760)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape089 f g inputs siblings]
  rw [unoccupied f g 8 246016 (by decide),siblings 8 (by decide) 246016 (by decide)]
  rfl
#print axioms shape099
end AspisR1.JGy_Gr_M0Roots
end
