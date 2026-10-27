import JHc_Tree1Part0
import JHc_Certs1_01
import JHc_Certs1_02
import JHc_Certs1_03
import JHc_Certs1_04
import JHc_Certs1_05
import JHc_Certs1_06
import JHc_Certs1_07
import JHc_Certs1_08
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input010 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash010.message
def value010 : State := JFp_SHADigest.output JHc_Gr_M1.Hash010.result
theorem cast010_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash010.B00.input).map Fin.val=JHc_Gr_M1.Hash010.B00.input := by rfl
#print axioms cast010_0
theorem tail010 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash010.tail).map Fin.val=JHc_Gr_M1.Hash010.tail := by rfl
#print axioms tail010
theorem numeric010 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash010.message).map Fin.val=JHc_Gr_M1.Hash010.message := by
  simp only [JHc_Gr_M1.Hash010.message,JHc_Gr_M1.Hash010.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast010_0,tail010]
#print axioms numeric010
theorem hash010 : JFp_SHADigest.digest input010=value010 := by
  unfold input010 JFp_SHADigest.digest
  rw [numeric010,JHc_Gr_M1.Hash010.checked]
  rfl
#print axioms hash010
theorem address010 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [84,158,189,163,7,211,150,118,46,159,127,12,244,157,167,96,164,240,68,44,151,232,222,236,240,147,88,216,134,56,255,201]) value006)=input010 := by rfl
#print axioms address010
def tree010 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [84,158,189,163,7,211,150,118,46,159,127,12,244,157,167,96,164,240,68,44,151,232,222,236,240,147,88,216,134,56,255,201])) tree006
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
def input011 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash011.message
def value011 : State := JFp_SHADigest.output JHc_Gr_M1.Hash011.result
theorem cast011_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash011.B00.input).map Fin.val=JHc_Gr_M1.Hash011.B00.input := by rfl
#print axioms cast011_0
theorem tail011 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash011.tail).map Fin.val=JHc_Gr_M1.Hash011.tail := by rfl
#print axioms tail011
theorem numeric011 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash011.message).map Fin.val=JHc_Gr_M1.Hash011.message := by
  simp only [JHc_Gr_M1.Hash011.message,JHc_Gr_M1.Hash011.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast011_0,tail011]
#print axioms numeric011
theorem hash011 : JFp_SHADigest.digest input011=value011 := by
  unfold input011 JFp_SHADigest.digest
  rw [numeric011,JHc_Gr_M1.Hash011.checked]
  rfl
#print axioms hash011
theorem address011 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [87,201,97,142,46,240,30,62,247,57,210,209,11,218,107,245,200,85,9,191,193,152,235,191,239,43,233,153,92,147,12,22]) value000)=input011 := by rfl
#print axioms address011
def tree011 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [87,201,97,142,46,240,30,62,247,57,210,209,11,218,107,245,200,85,9,191,193,152,235,191,239,43,233,153,92,147,12,22])) tree000
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
def input012 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash012.message
def value012 : State := JFp_SHADigest.output JHc_Gr_M1.Hash012.result
theorem cast012_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash012.B00.input).map Fin.val=JHc_Gr_M1.Hash012.B00.input := by rfl
#print axioms cast012_0
theorem tail012 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash012.tail).map Fin.val=JHc_Gr_M1.Hash012.tail := by rfl
#print axioms tail012
theorem numeric012 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash012.message).map Fin.val=JHc_Gr_M1.Hash012.message := by
  simp only [JHc_Gr_M1.Hash012.message,JHc_Gr_M1.Hash012.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast012_0,tail012]
#print axioms numeric012
theorem hash012 : JFp_SHADigest.digest input012=value012 := by
  unfold input012 JFp_SHADigest.digest
  rw [numeric012,JHc_Gr_M1.Hash012.checked]
  rfl
#print axioms hash012
theorem address012 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [126,244,47,162,206,176,63,208,66,80,97,27,124,150,156,29,16,125,4,24,229,40,80,226,50,22,217,21,9,118,223,64]) value001)=input012 := by rfl
#print axioms address012
def tree012 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [126,244,47,162,206,176,63,208,66,80,97,27,124,150,156,29,16,125,4,24,229,40,80,226,50,22,217,21,9,118,223,64])) tree001
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
def input013 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash013.message
def value013 : State := JFp_SHADigest.output JHc_Gr_M1.Hash013.result
theorem cast013_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash013.B00.input).map Fin.val=JHc_Gr_M1.Hash013.B00.input := by rfl
#print axioms cast013_0
theorem tail013 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash013.tail).map Fin.val=JHc_Gr_M1.Hash013.tail := by rfl
#print axioms tail013
theorem numeric013 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash013.message).map Fin.val=JHc_Gr_M1.Hash013.message := by
  simp only [JHc_Gr_M1.Hash013.message,JHc_Gr_M1.Hash013.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast013_0,tail013]
#print axioms numeric013
theorem hash013 : JFp_SHADigest.digest input013=value013 := by
  unfold input013 JFp_SHADigest.digest
  rw [numeric013,JHc_Gr_M1.Hash013.checked]
  rfl
#print axioms hash013
theorem address013 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [105,207,46,68,125,195,225,145,182,7,102,115,151,53,228,97,66,255,193,10,177,180,57,243,141,165,117,4,62,94,100,227]) value009)=input013 := by rfl
#print axioms address013
def tree013 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [105,207,46,68,125,195,225,145,182,7,102,115,151,53,228,97,66,255,193,10,177,180,57,243,141,165,117,4,62,94,100,227])) tree009
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
def input014 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash014.message
def value014 : State := JFp_SHADigest.output JHc_Gr_M1.Hash014.result
theorem cast014_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash014.B00.input).map Fin.val=JHc_Gr_M1.Hash014.B00.input := by rfl
#print axioms cast014_0
theorem tail014 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash014.tail).map Fin.val=JHc_Gr_M1.Hash014.tail := by rfl
#print axioms tail014
theorem numeric014 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash014.message).map Fin.val=JHc_Gr_M1.Hash014.message := by
  simp only [JHc_Gr_M1.Hash014.message,JHc_Gr_M1.Hash014.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast014_0,tail014]
#print axioms numeric014
theorem hash014 : JFp_SHADigest.digest input014=value014 := by
  unfold input014 JFp_SHADigest.digest
  rw [numeric014,JHc_Gr_M1.Hash014.checked]
  rfl
#print axioms hash014
theorem address014 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [178,45,27,133,141,100,37,222,96,165,67,100,140,205,14,251,78,74,113,201,225,78,242,12,210,165,12,143,151,125,240,161]) value007)=input014 := by rfl
#print axioms address014
def tree014 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [178,45,27,133,141,100,37,222,96,165,67,100,140,205,14,251,78,74,113,201,225,78,242,12,210,165,12,143,151,125,240,161])) tree007
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
def input015 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash015.message
def value015 : State := JFp_SHADigest.output JHc_Gr_M1.Hash015.result
theorem cast015_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash015.B00.input).map Fin.val=JHc_Gr_M1.Hash015.B00.input := by rfl
#print axioms cast015_0
theorem tail015 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash015.tail).map Fin.val=JHc_Gr_M1.Hash015.tail := by rfl
#print axioms tail015
theorem numeric015 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash015.message).map Fin.val=JHc_Gr_M1.Hash015.message := by
  simp only [JHc_Gr_M1.Hash015.message,JHc_Gr_M1.Hash015.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast015_0,tail015]
#print axioms numeric015
theorem hash015 : JFp_SHADigest.digest input015=value015 := by
  unfold input015 JFp_SHADigest.digest
  rw [numeric015,JHc_Gr_M1.Hash015.checked]
  rfl
#print axioms hash015
theorem address015 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [208,201,87,103,45,128,36,40,65,168,170,172,133,87,105,49,90,3,53,79,63,150,156,172,52,208,232,217,131,11,191,68]) value005)=input015 := by rfl
#print axioms address015
def tree015 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [208,201,87,103,45,128,36,40,65,168,170,172,133,87,105,49,90,3,53,79,63,150,156,172,52,208,232,217,131,11,191,68])) tree005
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
def input016 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash016.message
def value016 : State := JFp_SHADigest.output JHc_Gr_M1.Hash016.result
theorem cast016_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash016.B00.input).map Fin.val=JHc_Gr_M1.Hash016.B00.input := by rfl
#print axioms cast016_0
theorem tail016 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash016.tail).map Fin.val=JHc_Gr_M1.Hash016.tail := by rfl
#print axioms tail016
theorem numeric016 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash016.message).map Fin.val=JHc_Gr_M1.Hash016.message := by
  simp only [JHc_Gr_M1.Hash016.message,JHc_Gr_M1.Hash016.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast016_0,tail016]
#print axioms numeric016
theorem hash016 : JFp_SHADigest.digest input016=value016 := by
  unfold input016 JFp_SHADigest.digest
  rw [numeric016,JHc_Gr_M1.Hash016.checked]
  rfl
#print axioms hash016
theorem address016 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [58,250,234,236,124,53,147,155,154,165,220,179,164,49,96,165,20,23,164,50,251,216,34,12,121,250,222,56,113,154,22,180]) value008)=input016 := by rfl
#print axioms address016
def tree016 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [58,250,234,236,124,53,147,155,154,165,220,179,164,49,96,165,20,23,164,50,251,216,34,12,121,250,222,56,113,154,22,180])) tree008
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
def input017 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash017.message
def value017 : State := JFp_SHADigest.output JHc_Gr_M1.Hash017.result
theorem cast017_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash017.B00.input).map Fin.val=JHc_Gr_M1.Hash017.B00.input := by rfl
#print axioms cast017_0
theorem tail017 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash017.tail).map Fin.val=JHc_Gr_M1.Hash017.tail := by rfl
#print axioms tail017
theorem numeric017 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash017.message).map Fin.val=JHc_Gr_M1.Hash017.message := by
  simp only [JHc_Gr_M1.Hash017.message,JHc_Gr_M1.Hash017.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast017_0,tail017]
#print axioms numeric017
theorem hash017 : JFp_SHADigest.digest input017=value017 := by
  unfold input017 JFp_SHADigest.digest
  rw [numeric017,JHc_Gr_M1.Hash017.checked]
  rfl
#print axioms hash017
theorem address017 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [229,11,75,185,166,129,153,153,211,153,179,106,3,80,171,146,89,184,131,52,57,244,191,194,9,142,23,33,62,19,35,156]) value004)=input017 := by rfl
#print axioms address017
def tree017 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [229,11,75,185,166,129,153,153,211,153,179,106,3,80,171,146,89,184,131,52,57,244,191,194,9,142,23,33,62,19,35,156])) tree004
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
def input018 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash018.message
def value018 : State := JFp_SHADigest.output JHc_Gr_M1.Hash018.result
theorem cast018_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash018.B00.input).map Fin.val=JHc_Gr_M1.Hash018.B00.input := by rfl
#print axioms cast018_0
theorem tail018 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash018.tail).map Fin.val=JHc_Gr_M1.Hash018.tail := by rfl
#print axioms tail018
theorem numeric018 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash018.message).map Fin.val=JHc_Gr_M1.Hash018.message := by
  simp only [JHc_Gr_M1.Hash018.message,JHc_Gr_M1.Hash018.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast018_0,tail018]
#print axioms numeric018
theorem hash018 : JFp_SHADigest.digest input018=value018 := by
  unfold input018 JFp_SHADigest.digest
  rw [numeric018,JHc_Gr_M1.Hash018.checked]
  rfl
#print axioms hash018
theorem address018 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [232,135,117,237,45,118,87,95,67,116,77,226,109,208,88,160,202,241,38,170,96,84,230,88,96,117,190,107,137,190,145,40]) value002)=input018 := by rfl
#print axioms address018
def tree018 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [232,135,117,237,45,118,87,95,67,116,77,226,109,208,88,160,202,241,38,170,96,84,230,88,96,117,190,107,137,190,145,40])) tree002
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
def input019 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash019.message
def value019 : State := JFp_SHADigest.output JHc_Gr_M1.Hash019.result
theorem cast019_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash019.B00.input).map Fin.val=JHc_Gr_M1.Hash019.B00.input := by rfl
#print axioms cast019_0
theorem tail019 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash019.tail).map Fin.val=JHc_Gr_M1.Hash019.tail := by rfl
#print axioms tail019
theorem numeric019 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash019.message).map Fin.val=JHc_Gr_M1.Hash019.message := by
  simp only [JHc_Gr_M1.Hash019.message,JHc_Gr_M1.Hash019.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast019_0,tail019]
#print axioms numeric019
theorem hash019 : JFp_SHADigest.digest input019=value019 := by
  unfold input019 JFp_SHADigest.digest
  rw [numeric019,JHc_Gr_M1.Hash019.checked]
  rfl
#print axioms hash019
theorem address019 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [198,199,120,82,46,88,27,188,251,85,66,197,217,209,68,171,23,178,127,119,231,149,16,43,202,127,140,173,252,101,60,6]) value003)=input019 := by rfl
#print axioms address019
def tree019 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [198,199,120,82,46,88,27,188,251,85,66,197,217,209,68,171,23,178,127,119,231,149,16,43,202,127,140,173,252,101,60,6])) tree003
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
end AspisR1.JHc_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input020 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash020.message
def value020 : State := JFp_SHADigest.output JHc_Gr_M1.Hash020.result
theorem cast020_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash020.B00.input).map Fin.val=JHc_Gr_M1.Hash020.B00.input := by rfl
#print axioms cast020_0
theorem tail020 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash020.tail).map Fin.val=JHc_Gr_M1.Hash020.tail := by rfl
#print axioms tail020
theorem numeric020 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash020.message).map Fin.val=JHc_Gr_M1.Hash020.message := by
  simp only [JHc_Gr_M1.Hash020.message,JHc_Gr_M1.Hash020.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast020_0,tail020]
#print axioms numeric020
theorem hash020 : JFp_SHADigest.digest input020=value020 := by
  unfold input020 JFp_SHADigest.digest
  rw [numeric020,JHc_Gr_M1.Hash020.checked]
  rfl
#print axioms hash020
theorem address020 : BinMerkle32Path.nodeInput (children value010 (JGc_TX2_HashBytes.state [226,19,230,186,28,97,100,40,122,60,48,235,166,167,156,189,127,126,176,209,146,207,129,60,75,115,18,146,199,245,51,199]))=input020 := by rfl
#print axioms address020
def tree020 : Tree := .branch tree010 (.supplied (JGc_TX2_HashBytes.state [226,19,230,186,28,97,100,40,122,60,48,235,166,167,156,189,127,126,176,209,146,207,129,60,75,115,18,146,199,245,51,199]))
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
def input021 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash021.message
def value021 : State := JFp_SHADigest.output JHc_Gr_M1.Hash021.result
theorem cast021_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash021.B00.input).map Fin.val=JHc_Gr_M1.Hash021.B00.input := by rfl
#print axioms cast021_0
theorem tail021 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash021.tail).map Fin.val=JHc_Gr_M1.Hash021.tail := by rfl
#print axioms tail021
theorem numeric021 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash021.message).map Fin.val=JHc_Gr_M1.Hash021.message := by
  simp only [JHc_Gr_M1.Hash021.message,JHc_Gr_M1.Hash021.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast021_0,tail021]
#print axioms numeric021
theorem hash021 : JFp_SHADigest.digest input021=value021 := by
  unfold input021 JFp_SHADigest.digest
  rw [numeric021,JHc_Gr_M1.Hash021.checked]
  rfl
#print axioms hash021
theorem address021 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [53,199,117,75,221,203,227,135,140,20,26,44,148,40,245,6,247,144,199,69,152,25,40,59,8,112,100,10,148,1,240,224]) value011)=input021 := by rfl
#print axioms address021
def tree021 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [53,199,117,75,221,203,227,135,140,20,26,44,148,40,245,6,247,144,199,69,152,25,40,59,8,112,100,10,148,1,240,224])) tree011
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
def input022 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash022.message
def value022 : State := JFp_SHADigest.output JHc_Gr_M1.Hash022.result
theorem cast022_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash022.B00.input).map Fin.val=JHc_Gr_M1.Hash022.B00.input := by rfl
#print axioms cast022_0
theorem tail022 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash022.tail).map Fin.val=JHc_Gr_M1.Hash022.tail := by rfl
#print axioms tail022
theorem numeric022 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash022.message).map Fin.val=JHc_Gr_M1.Hash022.message := by
  simp only [JHc_Gr_M1.Hash022.message,JHc_Gr_M1.Hash022.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast022_0,tail022]
#print axioms numeric022
theorem hash022 : JFp_SHADigest.digest input022=value022 := by
  unfold input022 JFp_SHADigest.digest
  rw [numeric022,JHc_Gr_M1.Hash022.checked]
  rfl
#print axioms hash022
theorem address022 : BinMerkle32Path.nodeInput (children value012 (JGc_TX2_HashBytes.state [192,50,200,213,36,199,105,201,154,83,49,107,171,199,140,138,138,25,255,180,249,204,200,221,50,43,166,214,67,36,110,16]))=input022 := by rfl
#print axioms address022
def tree022 : Tree := .branch tree012 (.supplied (JGc_TX2_HashBytes.state [192,50,200,213,36,199,105,201,154,83,49,107,171,199,140,138,138,25,255,180,249,204,200,221,50,43,166,214,67,36,110,16]))
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
def input023 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash023.message
def value023 : State := JFp_SHADigest.output JHc_Gr_M1.Hash023.result
theorem cast023_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash023.B00.input).map Fin.val=JHc_Gr_M1.Hash023.B00.input := by rfl
#print axioms cast023_0
theorem tail023 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash023.tail).map Fin.val=JHc_Gr_M1.Hash023.tail := by rfl
#print axioms tail023
theorem numeric023 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash023.message).map Fin.val=JHc_Gr_M1.Hash023.message := by
  simp only [JHc_Gr_M1.Hash023.message,JHc_Gr_M1.Hash023.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast023_0,tail023]
#print axioms numeric023
theorem hash023 : JFp_SHADigest.digest input023=value023 := by
  unfold input023 JFp_SHADigest.digest
  rw [numeric023,JHc_Gr_M1.Hash023.checked]
  rfl
#print axioms hash023
theorem address023 : BinMerkle32Path.nodeInput (children value013 (JGc_TX2_HashBytes.state [102,110,213,2,148,96,173,189,56,93,84,101,64,44,166,50,155,9,114,234,56,56,211,60,155,126,100,123,86,255,245,207]))=input023 := by rfl
#print axioms address023
def tree023 : Tree := .branch tree013 (.supplied (JGc_TX2_HashBytes.state [102,110,213,2,148,96,173,189,56,93,84,101,64,44,166,50,155,9,114,234,56,56,211,60,155,126,100,123,86,255,245,207]))
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
def input024 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash024.message
def value024 : State := JFp_SHADigest.output JHc_Gr_M1.Hash024.result
theorem cast024_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash024.B00.input).map Fin.val=JHc_Gr_M1.Hash024.B00.input := by rfl
#print axioms cast024_0
theorem tail024 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash024.tail).map Fin.val=JHc_Gr_M1.Hash024.tail := by rfl
#print axioms tail024
theorem numeric024 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash024.message).map Fin.val=JHc_Gr_M1.Hash024.message := by
  simp only [JHc_Gr_M1.Hash024.message,JHc_Gr_M1.Hash024.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast024_0,tail024]
#print axioms numeric024
theorem hash024 : JFp_SHADigest.digest input024=value024 := by
  unfold input024 JFp_SHADigest.digest
  rw [numeric024,JHc_Gr_M1.Hash024.checked]
  rfl
#print axioms hash024
theorem address024 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [207,254,248,226,47,19,54,49,165,112,36,160,160,101,28,252,240,13,181,65,153,32,3,78,22,59,184,81,253,195,95,153]) value014)=input024 := by rfl
#print axioms address024
def tree024 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [207,254,248,226,47,19,54,49,165,112,36,160,160,101,28,252,240,13,181,65,153,32,3,78,22,59,184,81,253,195,95,153])) tree014
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
def input025 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash025.message
def value025 : State := JFp_SHADigest.output JHc_Gr_M1.Hash025.result
theorem cast025_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash025.B00.input).map Fin.val=JHc_Gr_M1.Hash025.B00.input := by rfl
#print axioms cast025_0
theorem tail025 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash025.tail).map Fin.val=JHc_Gr_M1.Hash025.tail := by rfl
#print axioms tail025
theorem numeric025 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash025.message).map Fin.val=JHc_Gr_M1.Hash025.message := by
  simp only [JHc_Gr_M1.Hash025.message,JHc_Gr_M1.Hash025.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast025_0,tail025]
#print axioms numeric025
theorem hash025 : JFp_SHADigest.digest input025=value025 := by
  unfold input025 JFp_SHADigest.digest
  rw [numeric025,JHc_Gr_M1.Hash025.checked]
  rfl
#print axioms hash025
theorem address025 : BinMerkle32Path.nodeInput (children value015 (JGc_TX2_HashBytes.state [118,182,6,74,103,244,136,114,84,255,217,64,189,71,61,128,226,133,217,73,78,68,236,158,199,227,240,136,1,108,57,83]))=input025 := by rfl
#print axioms address025
def tree025 : Tree := .branch tree015 (.supplied (JGc_TX2_HashBytes.state [118,182,6,74,103,244,136,114,84,255,217,64,189,71,61,128,226,133,217,73,78,68,236,158,199,227,240,136,1,108,57,83]))
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
def input026 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash026.message
def value026 : State := JFp_SHADigest.output JHc_Gr_M1.Hash026.result
theorem cast026_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash026.B00.input).map Fin.val=JHc_Gr_M1.Hash026.B00.input := by rfl
#print axioms cast026_0
theorem tail026 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash026.tail).map Fin.val=JHc_Gr_M1.Hash026.tail := by rfl
#print axioms tail026
theorem numeric026 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash026.message).map Fin.val=JHc_Gr_M1.Hash026.message := by
  simp only [JHc_Gr_M1.Hash026.message,JHc_Gr_M1.Hash026.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast026_0,tail026]
#print axioms numeric026
theorem hash026 : JFp_SHADigest.digest input026=value026 := by
  unfold input026 JFp_SHADigest.digest
  rw [numeric026,JHc_Gr_M1.Hash026.checked]
  rfl
#print axioms hash026
theorem address026 : BinMerkle32Path.nodeInput (children value016 (JGc_TX2_HashBytes.state [198,145,218,11,27,71,231,58,41,252,108,230,167,179,48,30,19,243,203,144,105,210,9,80,77,183,232,151,137,4,170,15]))=input026 := by rfl
#print axioms address026
def tree026 : Tree := .branch tree016 (.supplied (JGc_TX2_HashBytes.state [198,145,218,11,27,71,231,58,41,252,108,230,167,179,48,30,19,243,203,144,105,210,9,80,77,183,232,151,137,4,170,15]))
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
def input027 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash027.message
def value027 : State := JFp_SHADigest.output JHc_Gr_M1.Hash027.result
theorem cast027_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash027.B00.input).map Fin.val=JHc_Gr_M1.Hash027.B00.input := by rfl
#print axioms cast027_0
theorem tail027 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash027.tail).map Fin.val=JHc_Gr_M1.Hash027.tail := by rfl
#print axioms tail027
theorem numeric027 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash027.message).map Fin.val=JHc_Gr_M1.Hash027.message := by
  simp only [JHc_Gr_M1.Hash027.message,JHc_Gr_M1.Hash027.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast027_0,tail027]
#print axioms numeric027
theorem hash027 : JFp_SHADigest.digest input027=value027 := by
  unfold input027 JFp_SHADigest.digest
  rw [numeric027,JHc_Gr_M1.Hash027.checked]
  rfl
#print axioms hash027
theorem address027 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [104,141,228,117,121,171,3,4,176,4,107,28,254,224,219,29,112,25,96,120,70,213,98,52,25,175,170,185,190,225,223,156]) value017)=input027 := by rfl
#print axioms address027
def tree027 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [104,141,228,117,121,171,3,4,176,4,107,28,254,224,219,29,112,25,96,120,70,213,98,52,25,175,170,185,190,225,223,156])) tree017
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
def input028 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash028.message
def value028 : State := JFp_SHADigest.output JHc_Gr_M1.Hash028.result
theorem cast028_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash028.B00.input).map Fin.val=JHc_Gr_M1.Hash028.B00.input := by rfl
#print axioms cast028_0
theorem tail028 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash028.tail).map Fin.val=JHc_Gr_M1.Hash028.tail := by rfl
#print axioms tail028
theorem numeric028 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash028.message).map Fin.val=JHc_Gr_M1.Hash028.message := by
  simp only [JHc_Gr_M1.Hash028.message,JHc_Gr_M1.Hash028.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast028_0,tail028]
#print axioms numeric028
theorem hash028 : JFp_SHADigest.digest input028=value028 := by
  unfold input028 JFp_SHADigest.digest
  rw [numeric028,JHc_Gr_M1.Hash028.checked]
  rfl
#print axioms hash028
theorem address028 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [86,28,233,120,193,72,153,62,145,245,239,192,86,31,200,86,29,20,129,186,93,27,187,6,64,75,180,174,8,117,228,16]) value018)=input028 := by rfl
#print axioms address028
def tree028 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [86,28,233,120,193,72,153,62,145,245,239,192,86,31,200,86,29,20,129,186,93,27,187,6,64,75,180,174,8,117,228,16])) tree018
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
def input029 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash029.message
def value029 : State := JFp_SHADigest.output JHc_Gr_M1.Hash029.result
theorem cast029_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash029.B00.input).map Fin.val=JHc_Gr_M1.Hash029.B00.input := by rfl
#print axioms cast029_0
theorem tail029 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash029.tail).map Fin.val=JHc_Gr_M1.Hash029.tail := by rfl
#print axioms tail029
theorem numeric029 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash029.message).map Fin.val=JHc_Gr_M1.Hash029.message := by
  simp only [JHc_Gr_M1.Hash029.message,JHc_Gr_M1.Hash029.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast029_0,tail029]
#print axioms numeric029
theorem hash029 : JFp_SHADigest.digest input029=value029 := by
  unfold input029 JFp_SHADigest.digest
  rw [numeric029,JHc_Gr_M1.Hash029.checked]
  rfl
#print axioms hash029
theorem address029 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [46,114,18,158,240,245,37,120,114,167,15,134,67,123,175,250,230,84,253,40,11,47,196,152,226,249,239,35,86,182,35,30]) value019)=input029 := by rfl
#print axioms address029
def tree029 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [46,114,18,158,240,245,37,120,114,167,15,134,67,123,175,250,230,84,253,40,11,47,196,152,226,249,239,35,86,182,35,30])) tree019
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
end AspisR1.JHc_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input030 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash030.message
def value030 : State := JFp_SHADigest.output JHc_Gr_M1.Hash030.result
theorem cast030_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash030.B00.input).map Fin.val=JHc_Gr_M1.Hash030.B00.input := by rfl
#print axioms cast030_0
theorem tail030 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash030.tail).map Fin.val=JHc_Gr_M1.Hash030.tail := by rfl
#print axioms tail030
theorem numeric030 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash030.message).map Fin.val=JHc_Gr_M1.Hash030.message := by
  simp only [JHc_Gr_M1.Hash030.message,JHc_Gr_M1.Hash030.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast030_0,tail030]
#print axioms numeric030
theorem hash030 : JFp_SHADigest.digest input030=value030 := by
  unfold input030 JFp_SHADigest.digest
  rw [numeric030,JHc_Gr_M1.Hash030.checked]
  rfl
#print axioms hash030
theorem address030 : BinMerkle32Path.nodeInput (children value020 (JGc_TX2_HashBytes.state [161,76,3,159,191,249,90,238,12,33,36,222,12,85,198,154,218,16,194,33,132,91,57,18,102,89,24,129,206,192,84,2]))=input030 := by rfl
#print axioms address030
def tree030 : Tree := .branch tree020 (.supplied (JGc_TX2_HashBytes.state [161,76,3,159,191,249,90,238,12,33,36,222,12,85,198,154,218,16,194,33,132,91,57,18,102,89,24,129,206,192,84,2]))
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
def input031 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash031.message
def value031 : State := JFp_SHADigest.output JHc_Gr_M1.Hash031.result
theorem cast031_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash031.B00.input).map Fin.val=JHc_Gr_M1.Hash031.B00.input := by rfl
#print axioms cast031_0
theorem tail031 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash031.tail).map Fin.val=JHc_Gr_M1.Hash031.tail := by rfl
#print axioms tail031
theorem numeric031 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash031.message).map Fin.val=JHc_Gr_M1.Hash031.message := by
  simp only [JHc_Gr_M1.Hash031.message,JHc_Gr_M1.Hash031.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast031_0,tail031]
#print axioms numeric031
theorem hash031 : JFp_SHADigest.digest input031=value031 := by
  unfold input031 JFp_SHADigest.digest
  rw [numeric031,JHc_Gr_M1.Hash031.checked]
  rfl
#print axioms hash031
theorem address031 : BinMerkle32Path.nodeInput (children value021 (JGc_TX2_HashBytes.state [150,245,179,73,238,203,63,9,99,117,193,114,224,59,215,81,139,40,94,196,154,161,204,163,131,194,211,158,164,68,7,147]))=input031 := by rfl
#print axioms address031
def tree031 : Tree := .branch tree021 (.supplied (JGc_TX2_HashBytes.state [150,245,179,73,238,203,63,9,99,117,193,114,224,59,215,81,139,40,94,196,154,161,204,163,131,194,211,158,164,68,7,147]))
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
def input032 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash032.message
def value032 : State := JFp_SHADigest.output JHc_Gr_M1.Hash032.result
theorem cast032_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash032.B00.input).map Fin.val=JHc_Gr_M1.Hash032.B00.input := by rfl
#print axioms cast032_0
theorem tail032 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash032.tail).map Fin.val=JHc_Gr_M1.Hash032.tail := by rfl
#print axioms tail032
theorem numeric032 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash032.message).map Fin.val=JHc_Gr_M1.Hash032.message := by
  simp only [JHc_Gr_M1.Hash032.message,JHc_Gr_M1.Hash032.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast032_0,tail032]
#print axioms numeric032
theorem hash032 : JFp_SHADigest.digest input032=value032 := by
  unfold input032 JFp_SHADigest.digest
  rw [numeric032,JHc_Gr_M1.Hash032.checked]
  rfl
#print axioms hash032
theorem address032 : BinMerkle32Path.nodeInput (children value022 (JGc_TX2_HashBytes.state [97,255,106,209,39,206,184,200,255,182,229,243,150,159,37,202,105,5,207,52,192,189,18,106,9,249,42,77,128,132,228,204]))=input032 := by rfl
#print axioms address032
def tree032 : Tree := .branch tree022 (.supplied (JGc_TX2_HashBytes.state [97,255,106,209,39,206,184,200,255,182,229,243,150,159,37,202,105,5,207,52,192,189,18,106,9,249,42,77,128,132,228,204]))
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
def input033 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash033.message
def value033 : State := JFp_SHADigest.output JHc_Gr_M1.Hash033.result
theorem cast033_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash033.B00.input).map Fin.val=JHc_Gr_M1.Hash033.B00.input := by rfl
#print axioms cast033_0
theorem tail033 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash033.tail).map Fin.val=JHc_Gr_M1.Hash033.tail := by rfl
#print axioms tail033
theorem numeric033 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash033.message).map Fin.val=JHc_Gr_M1.Hash033.message := by
  simp only [JHc_Gr_M1.Hash033.message,JHc_Gr_M1.Hash033.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast033_0,tail033]
#print axioms numeric033
theorem hash033 : JFp_SHADigest.digest input033=value033 := by
  unfold input033 JFp_SHADigest.digest
  rw [numeric033,JHc_Gr_M1.Hash033.checked]
  rfl
#print axioms hash033
theorem address033 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [198,117,40,249,115,8,80,114,136,28,25,209,63,143,53,34,247,134,30,13,179,145,39,114,51,86,73,45,212,147,188,0]) value023)=input033 := by rfl
#print axioms address033
def tree033 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [198,117,40,249,115,8,80,114,136,28,25,209,63,143,53,34,247,134,30,13,179,145,39,114,51,86,73,45,212,147,188,0])) tree023
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
def input034 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash034.message
def value034 : State := JFp_SHADigest.output JHc_Gr_M1.Hash034.result
theorem cast034_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash034.B00.input).map Fin.val=JHc_Gr_M1.Hash034.B00.input := by rfl
#print axioms cast034_0
theorem tail034 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash034.tail).map Fin.val=JHc_Gr_M1.Hash034.tail := by rfl
#print axioms tail034
theorem numeric034 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash034.message).map Fin.val=JHc_Gr_M1.Hash034.message := by
  simp only [JHc_Gr_M1.Hash034.message,JHc_Gr_M1.Hash034.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast034_0,tail034]
#print axioms numeric034
theorem hash034 : JFp_SHADigest.digest input034=value034 := by
  unfold input034 JFp_SHADigest.digest
  rw [numeric034,JHc_Gr_M1.Hash034.checked]
  rfl
#print axioms hash034
theorem address034 : BinMerkle32Path.nodeInput (children value024 (JGc_TX2_HashBytes.state [173,160,200,2,87,10,143,76,228,213,202,85,241,88,184,137,184,213,12,133,110,196,125,206,65,42,21,23,14,224,135,18]))=input034 := by rfl
#print axioms address034
def tree034 : Tree := .branch tree024 (.supplied (JGc_TX2_HashBytes.state [173,160,200,2,87,10,143,76,228,213,202,85,241,88,184,137,184,213,12,133,110,196,125,206,65,42,21,23,14,224,135,18]))
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
def input035 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash035.message
def value035 : State := JFp_SHADigest.output JHc_Gr_M1.Hash035.result
theorem cast035_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash035.B00.input).map Fin.val=JHc_Gr_M1.Hash035.B00.input := by rfl
#print axioms cast035_0
theorem tail035 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash035.tail).map Fin.val=JHc_Gr_M1.Hash035.tail := by rfl
#print axioms tail035
theorem numeric035 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash035.message).map Fin.val=JHc_Gr_M1.Hash035.message := by
  simp only [JHc_Gr_M1.Hash035.message,JHc_Gr_M1.Hash035.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast035_0,tail035]
#print axioms numeric035
theorem hash035 : JFp_SHADigest.digest input035=value035 := by
  unfold input035 JFp_SHADigest.digest
  rw [numeric035,JHc_Gr_M1.Hash035.checked]
  rfl
#print axioms hash035
theorem address035 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [16,128,131,147,46,155,13,197,29,34,144,51,143,28,229,54,178,32,183,183,140,105,113,160,115,195,214,144,94,12,128,80]) value025)=input035 := by rfl
#print axioms address035
def tree035 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [16,128,131,147,46,155,13,197,29,34,144,51,143,28,229,54,178,32,183,183,140,105,113,160,115,195,214,144,94,12,128,80])) tree025
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
def input036 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash036.message
def value036 : State := JFp_SHADigest.output JHc_Gr_M1.Hash036.result
theorem cast036_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash036.B00.input).map Fin.val=JHc_Gr_M1.Hash036.B00.input := by rfl
#print axioms cast036_0
theorem tail036 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash036.tail).map Fin.val=JHc_Gr_M1.Hash036.tail := by rfl
#print axioms tail036
theorem numeric036 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash036.message).map Fin.val=JHc_Gr_M1.Hash036.message := by
  simp only [JHc_Gr_M1.Hash036.message,JHc_Gr_M1.Hash036.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast036_0,tail036]
#print axioms numeric036
theorem hash036 : JFp_SHADigest.digest input036=value036 := by
  unfold input036 JFp_SHADigest.digest
  rw [numeric036,JHc_Gr_M1.Hash036.checked]
  rfl
#print axioms hash036
theorem address036 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [140,101,31,60,165,201,60,75,58,216,73,119,83,95,32,127,113,252,104,199,28,200,24,47,1,108,50,255,0,221,161,140]) value026)=input036 := by rfl
#print axioms address036
def tree036 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [140,101,31,60,165,201,60,75,58,216,73,119,83,95,32,127,113,252,104,199,28,200,24,47,1,108,50,255,0,221,161,140])) tree026
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
def input037 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash037.message
def value037 : State := JFp_SHADigest.output JHc_Gr_M1.Hash037.result
theorem cast037_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash037.B00.input).map Fin.val=JHc_Gr_M1.Hash037.B00.input := by rfl
#print axioms cast037_0
theorem tail037 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash037.tail).map Fin.val=JHc_Gr_M1.Hash037.tail := by rfl
#print axioms tail037
theorem numeric037 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash037.message).map Fin.val=JHc_Gr_M1.Hash037.message := by
  simp only [JHc_Gr_M1.Hash037.message,JHc_Gr_M1.Hash037.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast037_0,tail037]
#print axioms numeric037
theorem hash037 : JFp_SHADigest.digest input037=value037 := by
  unfold input037 JFp_SHADigest.digest
  rw [numeric037,JHc_Gr_M1.Hash037.checked]
  rfl
#print axioms hash037
theorem address037 : BinMerkle32Path.nodeInput (children value027 (JGc_TX2_HashBytes.state [43,150,240,241,176,44,116,229,80,221,23,5,12,189,27,226,164,73,153,251,188,47,181,148,5,149,67,154,125,10,233,211]))=input037 := by rfl
#print axioms address037
def tree037 : Tree := .branch tree027 (.supplied (JGc_TX2_HashBytes.state [43,150,240,241,176,44,116,229,80,221,23,5,12,189,27,226,164,73,153,251,188,47,181,148,5,149,67,154,125,10,233,211]))
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
def input038 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash038.message
def value038 : State := JFp_SHADigest.output JHc_Gr_M1.Hash038.result
theorem cast038_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash038.B00.input).map Fin.val=JHc_Gr_M1.Hash038.B00.input := by rfl
#print axioms cast038_0
theorem tail038 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash038.tail).map Fin.val=JHc_Gr_M1.Hash038.tail := by rfl
#print axioms tail038
theorem numeric038 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash038.message).map Fin.val=JHc_Gr_M1.Hash038.message := by
  simp only [JHc_Gr_M1.Hash038.message,JHc_Gr_M1.Hash038.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast038_0,tail038]
#print axioms numeric038
theorem hash038 : JFp_SHADigest.digest input038=value038 := by
  unfold input038 JFp_SHADigest.digest
  rw [numeric038,JHc_Gr_M1.Hash038.checked]
  rfl
#print axioms hash038
theorem address038 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [43,146,168,238,162,23,68,80,31,163,96,208,148,23,64,85,154,125,92,177,215,158,253,133,121,24,22,161,219,238,202,61]) value028)=input038 := by rfl
#print axioms address038
def tree038 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [43,146,168,238,162,23,68,80,31,163,96,208,148,23,64,85,154,125,92,177,215,158,253,133,121,24,22,161,219,238,202,61])) tree028
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
def input039 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash039.message
def value039 : State := JFp_SHADigest.output JHc_Gr_M1.Hash039.result
theorem cast039_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash039.B00.input).map Fin.val=JHc_Gr_M1.Hash039.B00.input := by rfl
#print axioms cast039_0
theorem tail039 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash039.tail).map Fin.val=JHc_Gr_M1.Hash039.tail := by rfl
#print axioms tail039
theorem numeric039 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash039.message).map Fin.val=JHc_Gr_M1.Hash039.message := by
  simp only [JHc_Gr_M1.Hash039.message,JHc_Gr_M1.Hash039.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast039_0,tail039]
#print axioms numeric039
theorem hash039 : JFp_SHADigest.digest input039=value039 := by
  unfold input039 JFp_SHADigest.digest
  rw [numeric039,JHc_Gr_M1.Hash039.checked]
  rfl
#print axioms hash039
theorem address039 : BinMerkle32Path.nodeInput (children value029 (JGc_TX2_HashBytes.state [254,103,22,216,177,229,178,69,230,133,92,137,126,145,115,176,102,124,84,213,140,225,194,132,77,135,97,138,229,59,250,215]))=input039 := by rfl
#print axioms address039
def tree039 : Tree := .branch tree029 (.supplied (JGc_TX2_HashBytes.state [254,103,22,216,177,229,178,69,230,133,92,137,126,145,115,176,102,124,84,213,140,225,194,132,77,135,97,138,229,59,250,215]))
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
end AspisR1.JHc_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input040 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash040.message
def value040 : State := JFp_SHADigest.output JHc_Gr_M1.Hash040.result
theorem cast040_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash040.B00.input).map Fin.val=JHc_Gr_M1.Hash040.B00.input := by rfl
#print axioms cast040_0
theorem tail040 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash040.tail).map Fin.val=JHc_Gr_M1.Hash040.tail := by rfl
#print axioms tail040
theorem numeric040 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash040.message).map Fin.val=JHc_Gr_M1.Hash040.message := by
  simp only [JHc_Gr_M1.Hash040.message,JHc_Gr_M1.Hash040.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast040_0,tail040]
#print axioms numeric040
theorem hash040 : JFp_SHADigest.digest input040=value040 := by
  unfold input040 JFp_SHADigest.digest
  rw [numeric040,JHc_Gr_M1.Hash040.checked]
  rfl
#print axioms hash040
theorem address040 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [174,82,153,70,104,229,145,166,155,82,31,251,14,90,80,67,114,199,139,42,46,185,55,221,237,7,39,6,110,203,14,252]) value030)=input040 := by rfl
#print axioms address040
def tree040 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [174,82,153,70,104,229,145,166,155,82,31,251,14,90,80,67,114,199,139,42,46,185,55,221,237,7,39,6,110,203,14,252])) tree030
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
def input041 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash041.message
def value041 : State := JFp_SHADigest.output JHc_Gr_M1.Hash041.result
theorem cast041_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash041.B00.input).map Fin.val=JHc_Gr_M1.Hash041.B00.input := by rfl
#print axioms cast041_0
theorem tail041 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash041.tail).map Fin.val=JHc_Gr_M1.Hash041.tail := by rfl
#print axioms tail041
theorem numeric041 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash041.message).map Fin.val=JHc_Gr_M1.Hash041.message := by
  simp only [JHc_Gr_M1.Hash041.message,JHc_Gr_M1.Hash041.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast041_0,tail041]
#print axioms numeric041
theorem hash041 : JFp_SHADigest.digest input041=value041 := by
  unfold input041 JFp_SHADigest.digest
  rw [numeric041,JHc_Gr_M1.Hash041.checked]
  rfl
#print axioms hash041
theorem address041 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [23,32,94,98,180,20,186,60,5,79,157,234,247,20,120,80,164,35,4,186,25,63,57,161,43,202,149,143,82,86,154,0]) value031)=input041 := by rfl
#print axioms address041
def tree041 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [23,32,94,98,180,20,186,60,5,79,157,234,247,20,120,80,164,35,4,186,25,63,57,161,43,202,149,143,82,86,154,0])) tree031
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
def input042 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash042.message
def value042 : State := JFp_SHADigest.output JHc_Gr_M1.Hash042.result
theorem cast042_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash042.B00.input).map Fin.val=JHc_Gr_M1.Hash042.B00.input := by rfl
#print axioms cast042_0
theorem tail042 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash042.tail).map Fin.val=JHc_Gr_M1.Hash042.tail := by rfl
#print axioms tail042
theorem numeric042 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash042.message).map Fin.val=JHc_Gr_M1.Hash042.message := by
  simp only [JHc_Gr_M1.Hash042.message,JHc_Gr_M1.Hash042.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast042_0,tail042]
#print axioms numeric042
theorem hash042 : JFp_SHADigest.digest input042=value042 := by
  unfold input042 JFp_SHADigest.digest
  rw [numeric042,JHc_Gr_M1.Hash042.checked]
  rfl
#print axioms hash042
theorem address042 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [97,191,57,149,64,167,60,139,155,101,25,14,192,173,197,217,46,87,102,56,173,54,159,44,53,128,93,203,89,224,12,166]) value032)=input042 := by rfl
#print axioms address042
def tree042 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [97,191,57,149,64,167,60,139,155,101,25,14,192,173,197,217,46,87,102,56,173,54,159,44,53,128,93,203,89,224,12,166])) tree032
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
def input043 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash043.message
def value043 : State := JFp_SHADigest.output JHc_Gr_M1.Hash043.result
theorem cast043_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash043.B00.input).map Fin.val=JHc_Gr_M1.Hash043.B00.input := by rfl
#print axioms cast043_0
theorem tail043 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash043.tail).map Fin.val=JHc_Gr_M1.Hash043.tail := by rfl
#print axioms tail043
theorem numeric043 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash043.message).map Fin.val=JHc_Gr_M1.Hash043.message := by
  simp only [JHc_Gr_M1.Hash043.message,JHc_Gr_M1.Hash043.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast043_0,tail043]
#print axioms numeric043
theorem hash043 : JFp_SHADigest.digest input043=value043 := by
  unfold input043 JFp_SHADigest.digest
  rw [numeric043,JHc_Gr_M1.Hash043.checked]
  rfl
#print axioms hash043
theorem address043 : BinMerkle32Path.nodeInput (children value033 (JGc_TX2_HashBytes.state [122,249,177,125,116,181,20,239,10,177,124,212,75,148,64,213,224,76,236,136,246,44,160,184,106,201,206,170,6,68,14,182]))=input043 := by rfl
#print axioms address043
def tree043 : Tree := .branch tree033 (.supplied (JGc_TX2_HashBytes.state [122,249,177,125,116,181,20,239,10,177,124,212,75,148,64,213,224,76,236,136,246,44,160,184,106,201,206,170,6,68,14,182]))
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
def input044 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash044.message
def value044 : State := JFp_SHADigest.output JHc_Gr_M1.Hash044.result
theorem cast044_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash044.B00.input).map Fin.val=JHc_Gr_M1.Hash044.B00.input := by rfl
#print axioms cast044_0
theorem tail044 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash044.tail).map Fin.val=JHc_Gr_M1.Hash044.tail := by rfl
#print axioms tail044
theorem numeric044 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash044.message).map Fin.val=JHc_Gr_M1.Hash044.message := by
  simp only [JHc_Gr_M1.Hash044.message,JHc_Gr_M1.Hash044.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast044_0,tail044]
#print axioms numeric044
theorem hash044 : JFp_SHADigest.digest input044=value044 := by
  unfold input044 JFp_SHADigest.digest
  rw [numeric044,JHc_Gr_M1.Hash044.checked]
  rfl
#print axioms hash044
theorem address044 : BinMerkle32Path.nodeInput (children value034 (JGc_TX2_HashBytes.state [151,184,78,84,65,195,103,88,59,72,98,75,137,155,138,234,245,102,144,251,199,25,120,222,103,12,202,216,89,102,142,47]))=input044 := by rfl
#print axioms address044
def tree044 : Tree := .branch tree034 (.supplied (JGc_TX2_HashBytes.state [151,184,78,84,65,195,103,88,59,72,98,75,137,155,138,234,245,102,144,251,199,25,120,222,103,12,202,216,89,102,142,47]))
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
def input045 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash045.message
def value045 : State := JFp_SHADigest.output JHc_Gr_M1.Hash045.result
theorem cast045_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash045.B00.input).map Fin.val=JHc_Gr_M1.Hash045.B00.input := by rfl
#print axioms cast045_0
theorem tail045 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash045.tail).map Fin.val=JHc_Gr_M1.Hash045.tail := by rfl
#print axioms tail045
theorem numeric045 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash045.message).map Fin.val=JHc_Gr_M1.Hash045.message := by
  simp only [JHc_Gr_M1.Hash045.message,JHc_Gr_M1.Hash045.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast045_0,tail045]
#print axioms numeric045
theorem hash045 : JFp_SHADigest.digest input045=value045 := by
  unfold input045 JFp_SHADigest.digest
  rw [numeric045,JHc_Gr_M1.Hash045.checked]
  rfl
#print axioms hash045
theorem address045 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [63,240,224,145,205,168,7,153,218,214,129,218,29,224,241,228,12,94,116,107,157,77,53,249,244,131,19,213,15,234,161,215]) value035)=input045 := by rfl
#print axioms address045
def tree045 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [63,240,224,145,205,168,7,153,218,214,129,218,29,224,241,228,12,94,116,107,157,77,53,249,244,131,19,213,15,234,161,215])) tree035
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
def input046 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash046.message
def value046 : State := JFp_SHADigest.output JHc_Gr_M1.Hash046.result
theorem cast046_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash046.B00.input).map Fin.val=JHc_Gr_M1.Hash046.B00.input := by rfl
#print axioms cast046_0
theorem tail046 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash046.tail).map Fin.val=JHc_Gr_M1.Hash046.tail := by rfl
#print axioms tail046
theorem numeric046 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash046.message).map Fin.val=JHc_Gr_M1.Hash046.message := by
  simp only [JHc_Gr_M1.Hash046.message,JHc_Gr_M1.Hash046.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast046_0,tail046]
#print axioms numeric046
theorem hash046 : JFp_SHADigest.digest input046=value046 := by
  unfold input046 JFp_SHADigest.digest
  rw [numeric046,JHc_Gr_M1.Hash046.checked]
  rfl
#print axioms hash046
theorem address046 : BinMerkle32Path.nodeInput (children value036 (JGc_TX2_HashBytes.state [110,105,159,26,42,122,142,230,234,101,199,61,78,103,131,23,40,10,245,45,225,245,34,241,143,52,113,160,22,153,128,20]))=input046 := by rfl
#print axioms address046
def tree046 : Tree := .branch tree036 (.supplied (JGc_TX2_HashBytes.state [110,105,159,26,42,122,142,230,234,101,199,61,78,103,131,23,40,10,245,45,225,245,34,241,143,52,113,160,22,153,128,20]))
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
def input047 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash047.message
def value047 : State := JFp_SHADigest.output JHc_Gr_M1.Hash047.result
theorem cast047_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash047.B00.input).map Fin.val=JHc_Gr_M1.Hash047.B00.input := by rfl
#print axioms cast047_0
theorem tail047 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash047.tail).map Fin.val=JHc_Gr_M1.Hash047.tail := by rfl
#print axioms tail047
theorem numeric047 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash047.message).map Fin.val=JHc_Gr_M1.Hash047.message := by
  simp only [JHc_Gr_M1.Hash047.message,JHc_Gr_M1.Hash047.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast047_0,tail047]
#print axioms numeric047
theorem hash047 : JFp_SHADigest.digest input047=value047 := by
  unfold input047 JFp_SHADigest.digest
  rw [numeric047,JHc_Gr_M1.Hash047.checked]
  rfl
#print axioms hash047
theorem address047 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [141,242,62,237,199,13,154,83,181,79,134,159,130,129,160,88,62,217,221,214,111,246,205,241,230,116,152,15,205,136,237,159]) value037)=input047 := by rfl
#print axioms address047
def tree047 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [141,242,62,237,199,13,154,83,181,79,134,159,130,129,160,88,62,217,221,214,111,246,205,241,230,116,152,15,205,136,237,159])) tree037
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
def input048 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash048.message
def value048 : State := JFp_SHADigest.output JHc_Gr_M1.Hash048.result
theorem cast048_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash048.B00.input).map Fin.val=JHc_Gr_M1.Hash048.B00.input := by rfl
#print axioms cast048_0
theorem tail048 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash048.tail).map Fin.val=JHc_Gr_M1.Hash048.tail := by rfl
#print axioms tail048
theorem numeric048 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash048.message).map Fin.val=JHc_Gr_M1.Hash048.message := by
  simp only [JHc_Gr_M1.Hash048.message,JHc_Gr_M1.Hash048.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast048_0,tail048]
#print axioms numeric048
theorem hash048 : JFp_SHADigest.digest input048=value048 := by
  unfold input048 JFp_SHADigest.digest
  rw [numeric048,JHc_Gr_M1.Hash048.checked]
  rfl
#print axioms hash048
theorem address048 : BinMerkle32Path.nodeInput (children value038 (JGc_TX2_HashBytes.state [21,213,50,124,193,142,144,15,46,81,226,121,245,18,87,145,167,20,102,64,173,9,142,30,0,196,36,27,63,68,81,237]))=input048 := by rfl
#print axioms address048
def tree048 : Tree := .branch tree038 (.supplied (JGc_TX2_HashBytes.state [21,213,50,124,193,142,144,15,46,81,226,121,245,18,87,145,167,20,102,64,173,9,142,30,0,196,36,27,63,68,81,237]))
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
def input049 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash049.message
def value049 : State := JFp_SHADigest.output JHc_Gr_M1.Hash049.result
theorem cast049_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash049.B00.input).map Fin.val=JHc_Gr_M1.Hash049.B00.input := by rfl
#print axioms cast049_0
theorem tail049 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash049.tail).map Fin.val=JHc_Gr_M1.Hash049.tail := by rfl
#print axioms tail049
theorem numeric049 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash049.message).map Fin.val=JHc_Gr_M1.Hash049.message := by
  simp only [JHc_Gr_M1.Hash049.message,JHc_Gr_M1.Hash049.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast049_0,tail049]
#print axioms numeric049
theorem hash049 : JFp_SHADigest.digest input049=value049 := by
  unfold input049 JFp_SHADigest.digest
  rw [numeric049,JHc_Gr_M1.Hash049.checked]
  rfl
#print axioms hash049
theorem address049 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [138,187,147,94,199,192,2,178,20,97,98,68,215,153,0,75,115,196,220,228,200,152,250,238,63,205,135,43,65,81,103,172]) value039)=input049 := by rfl
#print axioms address049
def tree049 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [138,187,147,94,199,192,2,178,20,97,98,68,215,153,0,75,115,196,220,228,200,152,250,238,63,205,135,43,65,81,103,172])) tree039
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
end AspisR1.JHc_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input050 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash050.message
def value050 : State := JFp_SHADigest.output JHc_Gr_M1.Hash050.result
theorem cast050_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash050.B00.input).map Fin.val=JHc_Gr_M1.Hash050.B00.input := by rfl
#print axioms cast050_0
theorem tail050 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash050.tail).map Fin.val=JHc_Gr_M1.Hash050.tail := by rfl
#print axioms tail050
theorem numeric050 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash050.message).map Fin.val=JHc_Gr_M1.Hash050.message := by
  simp only [JHc_Gr_M1.Hash050.message,JHc_Gr_M1.Hash050.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast050_0,tail050]
#print axioms numeric050
theorem hash050 : JFp_SHADigest.digest input050=value050 := by
  unfold input050 JFp_SHADigest.digest
  rw [numeric050,JHc_Gr_M1.Hash050.checked]
  rfl
#print axioms hash050
theorem address050 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [213,92,133,128,25,248,250,140,193,139,150,68,77,135,147,35,142,166,119,192,218,182,91,94,228,19,198,108,127,203,242,119]) value040)=input050 := by rfl
#print axioms address050
def tree050 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [213,92,133,128,25,248,250,140,193,139,150,68,77,135,147,35,142,166,119,192,218,182,91,94,228,19,198,108,127,203,242,119])) tree040
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
def input051 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash051.message
def value051 : State := JFp_SHADigest.output JHc_Gr_M1.Hash051.result
theorem cast051_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash051.B00.input).map Fin.val=JHc_Gr_M1.Hash051.B00.input := by rfl
#print axioms cast051_0
theorem tail051 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash051.tail).map Fin.val=JHc_Gr_M1.Hash051.tail := by rfl
#print axioms tail051
theorem numeric051 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash051.message).map Fin.val=JHc_Gr_M1.Hash051.message := by
  simp only [JHc_Gr_M1.Hash051.message,JHc_Gr_M1.Hash051.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast051_0,tail051]
#print axioms numeric051
theorem hash051 : JFp_SHADigest.digest input051=value051 := by
  unfold input051 JFp_SHADigest.digest
  rw [numeric051,JHc_Gr_M1.Hash051.checked]
  rfl
#print axioms hash051
theorem address051 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [81,239,149,218,159,11,224,172,201,3,32,69,184,120,186,14,167,232,10,19,198,22,40,223,87,252,148,18,167,205,157,165]) value041)=input051 := by rfl
#print axioms address051
def tree051 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [81,239,149,218,159,11,224,172,201,3,32,69,184,120,186,14,167,232,10,19,198,22,40,223,87,252,148,18,167,205,157,165])) tree041
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
def input052 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash052.message
def value052 : State := JFp_SHADigest.output JHc_Gr_M1.Hash052.result
theorem cast052_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash052.B00.input).map Fin.val=JHc_Gr_M1.Hash052.B00.input := by rfl
#print axioms cast052_0
theorem tail052 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash052.tail).map Fin.val=JHc_Gr_M1.Hash052.tail := by rfl
#print axioms tail052
theorem numeric052 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash052.message).map Fin.val=JHc_Gr_M1.Hash052.message := by
  simp only [JHc_Gr_M1.Hash052.message,JHc_Gr_M1.Hash052.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast052_0,tail052]
#print axioms numeric052
theorem hash052 : JFp_SHADigest.digest input052=value052 := by
  unfold input052 JFp_SHADigest.digest
  rw [numeric052,JHc_Gr_M1.Hash052.checked]
  rfl
#print axioms hash052
theorem address052 : BinMerkle32Path.nodeInput (children value042 (JGc_TX2_HashBytes.state [218,67,160,176,255,242,51,54,19,70,46,31,66,58,26,18,255,181,5,147,67,43,32,75,58,146,61,9,200,176,17,181]))=input052 := by rfl
#print axioms address052
def tree052 : Tree := .branch tree042 (.supplied (JGc_TX2_HashBytes.state [218,67,160,176,255,242,51,54,19,70,46,31,66,58,26,18,255,181,5,147,67,43,32,75,58,146,61,9,200,176,17,181]))
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
def input053 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash053.message
def value053 : State := JFp_SHADigest.output JHc_Gr_M1.Hash053.result
theorem cast053_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash053.B00.input).map Fin.val=JHc_Gr_M1.Hash053.B00.input := by rfl
#print axioms cast053_0
theorem tail053 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash053.tail).map Fin.val=JHc_Gr_M1.Hash053.tail := by rfl
#print axioms tail053
theorem numeric053 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash053.message).map Fin.val=JHc_Gr_M1.Hash053.message := by
  simp only [JHc_Gr_M1.Hash053.message,JHc_Gr_M1.Hash053.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast053_0,tail053]
#print axioms numeric053
theorem hash053 : JFp_SHADigest.digest input053=value053 := by
  unfold input053 JFp_SHADigest.digest
  rw [numeric053,JHc_Gr_M1.Hash053.checked]
  rfl
#print axioms hash053
theorem address053 : BinMerkle32Path.nodeInput (children value043 (JGc_TX2_HashBytes.state [9,203,140,76,138,254,212,190,225,220,48,2,142,250,78,110,12,43,32,145,129,4,58,215,255,244,201,225,98,43,227,177]))=input053 := by rfl
#print axioms address053
def tree053 : Tree := .branch tree043 (.supplied (JGc_TX2_HashBytes.state [9,203,140,76,138,254,212,190,225,220,48,2,142,250,78,110,12,43,32,145,129,4,58,215,255,244,201,225,98,43,227,177]))
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
def input054 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash054.message
def value054 : State := JFp_SHADigest.output JHc_Gr_M1.Hash054.result
theorem cast054_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash054.B00.input).map Fin.val=JHc_Gr_M1.Hash054.B00.input := by rfl
#print axioms cast054_0
theorem tail054 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash054.tail).map Fin.val=JHc_Gr_M1.Hash054.tail := by rfl
#print axioms tail054
theorem numeric054 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash054.message).map Fin.val=JHc_Gr_M1.Hash054.message := by
  simp only [JHc_Gr_M1.Hash054.message,JHc_Gr_M1.Hash054.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast054_0,tail054]
#print axioms numeric054
theorem hash054 : JFp_SHADigest.digest input054=value054 := by
  unfold input054 JFp_SHADigest.digest
  rw [numeric054,JHc_Gr_M1.Hash054.checked]
  rfl
#print axioms hash054
theorem address054 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [248,181,250,118,85,250,26,83,114,52,136,167,60,144,132,111,120,93,125,209,49,84,32,66,30,109,91,89,231,36,237,196]) value044)=input054 := by rfl
#print axioms address054
def tree054 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [248,181,250,118,85,250,26,83,114,52,136,167,60,144,132,111,120,93,125,209,49,84,32,66,30,109,91,89,231,36,237,196])) tree044
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
def input055 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash055.message
def value055 : State := JFp_SHADigest.output JHc_Gr_M1.Hash055.result
theorem cast055_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash055.B00.input).map Fin.val=JHc_Gr_M1.Hash055.B00.input := by rfl
#print axioms cast055_0
theorem tail055 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash055.tail).map Fin.val=JHc_Gr_M1.Hash055.tail := by rfl
#print axioms tail055
theorem numeric055 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash055.message).map Fin.val=JHc_Gr_M1.Hash055.message := by
  simp only [JHc_Gr_M1.Hash055.message,JHc_Gr_M1.Hash055.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast055_0,tail055]
#print axioms numeric055
theorem hash055 : JFp_SHADigest.digest input055=value055 := by
  unfold input055 JFp_SHADigest.digest
  rw [numeric055,JHc_Gr_M1.Hash055.checked]
  rfl
#print axioms hash055
theorem address055 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [108,16,198,203,67,17,242,189,102,34,209,177,45,76,232,181,18,166,239,4,35,21,239,246,220,237,115,171,194,70,204,157]) value045)=input055 := by rfl
#print axioms address055
def tree055 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [108,16,198,203,67,17,242,189,102,34,209,177,45,76,232,181,18,166,239,4,35,21,239,246,220,237,115,171,194,70,204,157])) tree045
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
def input056 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash056.message
def value056 : State := JFp_SHADigest.output JHc_Gr_M1.Hash056.result
theorem cast056_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash056.B00.input).map Fin.val=JHc_Gr_M1.Hash056.B00.input := by rfl
#print axioms cast056_0
theorem tail056 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash056.tail).map Fin.val=JHc_Gr_M1.Hash056.tail := by rfl
#print axioms tail056
theorem numeric056 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash056.message).map Fin.val=JHc_Gr_M1.Hash056.message := by
  simp only [JHc_Gr_M1.Hash056.message,JHc_Gr_M1.Hash056.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast056_0,tail056]
#print axioms numeric056
theorem hash056 : JFp_SHADigest.digest input056=value056 := by
  unfold input056 JFp_SHADigest.digest
  rw [numeric056,JHc_Gr_M1.Hash056.checked]
  rfl
#print axioms hash056
theorem address056 : BinMerkle32Path.nodeInput (children value046 (JGc_TX2_HashBytes.state [197,43,157,201,30,225,68,160,229,190,201,182,162,53,115,97,51,234,182,243,73,166,223,190,116,177,25,188,182,144,219,200]))=input056 := by rfl
#print axioms address056
def tree056 : Tree := .branch tree046 (.supplied (JGc_TX2_HashBytes.state [197,43,157,201,30,225,68,160,229,190,201,182,162,53,115,97,51,234,182,243,73,166,223,190,116,177,25,188,182,144,219,200]))
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
def input057 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash057.message
def value057 : State := JFp_SHADigest.output JHc_Gr_M1.Hash057.result
theorem cast057_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash057.B00.input).map Fin.val=JHc_Gr_M1.Hash057.B00.input := by rfl
#print axioms cast057_0
theorem tail057 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash057.tail).map Fin.val=JHc_Gr_M1.Hash057.tail := by rfl
#print axioms tail057
theorem numeric057 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash057.message).map Fin.val=JHc_Gr_M1.Hash057.message := by
  simp only [JHc_Gr_M1.Hash057.message,JHc_Gr_M1.Hash057.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast057_0,tail057]
#print axioms numeric057
theorem hash057 : JFp_SHADigest.digest input057=value057 := by
  unfold input057 JFp_SHADigest.digest
  rw [numeric057,JHc_Gr_M1.Hash057.checked]
  rfl
#print axioms hash057
theorem address057 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [48,186,118,148,69,61,104,226,93,243,172,141,168,144,124,254,57,139,1,55,108,253,152,33,72,126,89,125,30,154,10,32]) value047)=input057 := by rfl
#print axioms address057
def tree057 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [48,186,118,148,69,61,104,226,93,243,172,141,168,144,124,254,57,139,1,55,108,253,152,33,72,126,89,125,30,154,10,32])) tree047
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
def input058 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash058.message
def value058 : State := JFp_SHADigest.output JHc_Gr_M1.Hash058.result
theorem cast058_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash058.B00.input).map Fin.val=JHc_Gr_M1.Hash058.B00.input := by rfl
#print axioms cast058_0
theorem tail058 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash058.tail).map Fin.val=JHc_Gr_M1.Hash058.tail := by rfl
#print axioms tail058
theorem numeric058 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash058.message).map Fin.val=JHc_Gr_M1.Hash058.message := by
  simp only [JHc_Gr_M1.Hash058.message,JHc_Gr_M1.Hash058.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast058_0,tail058]
#print axioms numeric058
theorem hash058 : JFp_SHADigest.digest input058=value058 := by
  unfold input058 JFp_SHADigest.digest
  rw [numeric058,JHc_Gr_M1.Hash058.checked]
  rfl
#print axioms hash058
theorem address058 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [90,249,230,45,98,111,180,129,153,122,162,170,204,61,76,254,140,54,104,181,250,67,86,138,44,28,90,64,159,9,181,47]) value048)=input058 := by rfl
#print axioms address058
def tree058 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [90,249,230,45,98,111,180,129,153,122,162,170,204,61,76,254,140,54,104,181,250,67,86,138,44,28,90,64,159,9,181,47])) tree048
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
def input059 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash059.message
def value059 : State := JFp_SHADigest.output JHc_Gr_M1.Hash059.result
theorem cast059_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash059.B00.input).map Fin.val=JHc_Gr_M1.Hash059.B00.input := by rfl
#print axioms cast059_0
theorem tail059 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash059.tail).map Fin.val=JHc_Gr_M1.Hash059.tail := by rfl
#print axioms tail059
theorem numeric059 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash059.message).map Fin.val=JHc_Gr_M1.Hash059.message := by
  simp only [JHc_Gr_M1.Hash059.message,JHc_Gr_M1.Hash059.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast059_0,tail059]
#print axioms numeric059
theorem hash059 : JFp_SHADigest.digest input059=value059 := by
  unfold input059 JFp_SHADigest.digest
  rw [numeric059,JHc_Gr_M1.Hash059.checked]
  rfl
#print axioms hash059
theorem address059 : BinMerkle32Path.nodeInput (children value049 (JGc_TX2_HashBytes.state [195,3,176,84,58,232,36,247,102,253,61,165,20,60,158,89,150,160,29,234,75,87,244,134,24,74,65,119,252,101,75,15]))=input059 := by rfl
#print axioms address059
def tree059 : Tree := .branch tree049 (.supplied (JGc_TX2_HashBytes.state [195,3,176,84,58,232,36,247,102,253,61,165,20,60,158,89,150,160,29,234,75,87,244,134,24,74,65,119,252,101,75,15]))
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
end AspisR1.JHc_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input060 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash060.message
def value060 : State := JFp_SHADigest.output JHc_Gr_M1.Hash060.result
theorem cast060_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash060.B00.input).map Fin.val=JHc_Gr_M1.Hash060.B00.input := by rfl
#print axioms cast060_0
theorem tail060 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash060.tail).map Fin.val=JHc_Gr_M1.Hash060.tail := by rfl
#print axioms tail060
theorem numeric060 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash060.message).map Fin.val=JHc_Gr_M1.Hash060.message := by
  simp only [JHc_Gr_M1.Hash060.message,JHc_Gr_M1.Hash060.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast060_0,tail060]
#print axioms numeric060
theorem hash060 : JFp_SHADigest.digest input060=value060 := by
  unfold input060 JFp_SHADigest.digest
  rw [numeric060,JHc_Gr_M1.Hash060.checked]
  rfl
#print axioms hash060
theorem address060 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [184,43,54,143,158,199,175,42,61,237,16,117,244,181,159,43,88,80,126,207,12,253,148,152,128,201,187,77,167,76,234,131]) value050)=input060 := by rfl
#print axioms address060
def tree060 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [184,43,54,143,158,199,175,42,61,237,16,117,244,181,159,43,88,80,126,207,12,253,148,152,128,201,187,77,167,76,234,131])) tree050
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
def input061 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash061.message
def value061 : State := JFp_SHADigest.output JHc_Gr_M1.Hash061.result
theorem cast061_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash061.B00.input).map Fin.val=JHc_Gr_M1.Hash061.B00.input := by rfl
#print axioms cast061_0
theorem tail061 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash061.tail).map Fin.val=JHc_Gr_M1.Hash061.tail := by rfl
#print axioms tail061
theorem numeric061 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash061.message).map Fin.val=JHc_Gr_M1.Hash061.message := by
  simp only [JHc_Gr_M1.Hash061.message,JHc_Gr_M1.Hash061.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast061_0,tail061]
#print axioms numeric061
theorem hash061 : JFp_SHADigest.digest input061=value061 := by
  unfold input061 JFp_SHADigest.digest
  rw [numeric061,JHc_Gr_M1.Hash061.checked]
  rfl
#print axioms hash061
theorem address061 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [9,59,145,89,120,54,222,74,203,219,27,53,98,237,178,181,58,227,170,3,52,21,253,207,237,232,171,52,49,52,153,1]) value051)=input061 := by rfl
#print axioms address061
def tree061 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [9,59,145,89,120,54,222,74,203,219,27,53,98,237,178,181,58,227,170,3,52,21,253,207,237,232,171,52,49,52,153,1])) tree051
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
def input062 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash062.message
def value062 : State := JFp_SHADigest.output JHc_Gr_M1.Hash062.result
theorem cast062_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash062.B00.input).map Fin.val=JHc_Gr_M1.Hash062.B00.input := by rfl
#print axioms cast062_0
theorem tail062 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash062.tail).map Fin.val=JHc_Gr_M1.Hash062.tail := by rfl
#print axioms tail062
theorem numeric062 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash062.message).map Fin.val=JHc_Gr_M1.Hash062.message := by
  simp only [JHc_Gr_M1.Hash062.message,JHc_Gr_M1.Hash062.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast062_0,tail062]
#print axioms numeric062
theorem hash062 : JFp_SHADigest.digest input062=value062 := by
  unfold input062 JFp_SHADigest.digest
  rw [numeric062,JHc_Gr_M1.Hash062.checked]
  rfl
#print axioms hash062
theorem address062 : BinMerkle32Path.nodeInput (children value052 (JGc_TX2_HashBytes.state [200,112,24,187,168,226,133,51,134,133,85,253,45,154,56,190,126,26,87,40,238,99,195,189,69,70,211,132,89,221,161,18]))=input062 := by rfl
#print axioms address062
def tree062 : Tree := .branch tree052 (.supplied (JGc_TX2_HashBytes.state [200,112,24,187,168,226,133,51,134,133,85,253,45,154,56,190,126,26,87,40,238,99,195,189,69,70,211,132,89,221,161,18]))
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
def input063 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash063.message
def value063 : State := JFp_SHADigest.output JHc_Gr_M1.Hash063.result
theorem cast063_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash063.B00.input).map Fin.val=JHc_Gr_M1.Hash063.B00.input := by rfl
#print axioms cast063_0
theorem tail063 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash063.tail).map Fin.val=JHc_Gr_M1.Hash063.tail := by rfl
#print axioms tail063
theorem numeric063 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash063.message).map Fin.val=JHc_Gr_M1.Hash063.message := by
  simp only [JHc_Gr_M1.Hash063.message,JHc_Gr_M1.Hash063.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast063_0,tail063]
#print axioms numeric063
theorem hash063 : JFp_SHADigest.digest input063=value063 := by
  unfold input063 JFp_SHADigest.digest
  rw [numeric063,JHc_Gr_M1.Hash063.checked]
  rfl
#print axioms hash063
theorem address063 : BinMerkle32Path.nodeInput (children value053 (JGc_TX2_HashBytes.state [254,17,1,69,169,101,14,124,152,58,198,80,91,197,7,201,23,89,197,83,121,49,187,33,254,195,218,154,226,70,10,132]))=input063 := by rfl
#print axioms address063
def tree063 : Tree := .branch tree053 (.supplied (JGc_TX2_HashBytes.state [254,17,1,69,169,101,14,124,152,58,198,80,91,197,7,201,23,89,197,83,121,49,187,33,254,195,218,154,226,70,10,132]))
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
def input064 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash064.message
def value064 : State := JFp_SHADigest.output JHc_Gr_M1.Hash064.result
theorem cast064_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash064.B00.input).map Fin.val=JHc_Gr_M1.Hash064.B00.input := by rfl
#print axioms cast064_0
theorem tail064 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash064.tail).map Fin.val=JHc_Gr_M1.Hash064.tail := by rfl
#print axioms tail064
theorem numeric064 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash064.message).map Fin.val=JHc_Gr_M1.Hash064.message := by
  simp only [JHc_Gr_M1.Hash064.message,JHc_Gr_M1.Hash064.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast064_0,tail064]
#print axioms numeric064
theorem hash064 : JFp_SHADigest.digest input064=value064 := by
  unfold input064 JFp_SHADigest.digest
  rw [numeric064,JHc_Gr_M1.Hash064.checked]
  rfl
#print axioms hash064
theorem address064 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [192,195,33,171,153,176,59,52,97,96,104,8,183,204,159,49,248,227,95,225,72,109,83,158,159,13,184,26,137,190,18,0]) value054)=input064 := by rfl
#print axioms address064
def tree064 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [192,195,33,171,153,176,59,52,97,96,104,8,183,204,159,49,248,227,95,225,72,109,83,158,159,13,184,26,137,190,18,0])) tree054
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
def input065 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash065.message
def value065 : State := JFp_SHADigest.output JHc_Gr_M1.Hash065.result
theorem cast065_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash065.B00.input).map Fin.val=JHc_Gr_M1.Hash065.B00.input := by rfl
#print axioms cast065_0
theorem tail065 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash065.tail).map Fin.val=JHc_Gr_M1.Hash065.tail := by rfl
#print axioms tail065
theorem numeric065 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash065.message).map Fin.val=JHc_Gr_M1.Hash065.message := by
  simp only [JHc_Gr_M1.Hash065.message,JHc_Gr_M1.Hash065.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast065_0,tail065]
#print axioms numeric065
theorem hash065 : JFp_SHADigest.digest input065=value065 := by
  unfold input065 JFp_SHADigest.digest
  rw [numeric065,JHc_Gr_M1.Hash065.checked]
  rfl
#print axioms hash065
theorem address065 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [254,206,208,23,213,50,19,160,84,122,149,199,15,73,40,119,253,111,116,175,203,205,102,52,143,81,145,192,139,46,139,68]) value055)=input065 := by rfl
#print axioms address065
def tree065 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [254,206,208,23,213,50,19,160,84,122,149,199,15,73,40,119,253,111,116,175,203,205,102,52,143,81,145,192,139,46,139,68])) tree055
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
def input066 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash066.message
def value066 : State := JFp_SHADigest.output JHc_Gr_M1.Hash066.result
theorem cast066_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash066.B00.input).map Fin.val=JHc_Gr_M1.Hash066.B00.input := by rfl
#print axioms cast066_0
theorem tail066 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash066.tail).map Fin.val=JHc_Gr_M1.Hash066.tail := by rfl
#print axioms tail066
theorem numeric066 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash066.message).map Fin.val=JHc_Gr_M1.Hash066.message := by
  simp only [JHc_Gr_M1.Hash066.message,JHc_Gr_M1.Hash066.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast066_0,tail066]
#print axioms numeric066
theorem hash066 : JFp_SHADigest.digest input066=value066 := by
  unfold input066 JFp_SHADigest.digest
  rw [numeric066,JHc_Gr_M1.Hash066.checked]
  rfl
#print axioms hash066
theorem address066 : BinMerkle32Path.nodeInput (children value056 (JGc_TX2_HashBytes.state [135,62,37,121,200,109,211,136,88,24,191,195,231,222,98,12,91,201,86,188,190,61,185,78,66,155,223,88,157,220,23,249]))=input066 := by rfl
#print axioms address066
def tree066 : Tree := .branch tree056 (.supplied (JGc_TX2_HashBytes.state [135,62,37,121,200,109,211,136,88,24,191,195,231,222,98,12,91,201,86,188,190,61,185,78,66,155,223,88,157,220,23,249]))
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
def input067 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash067.message
def value067 : State := JFp_SHADigest.output JHc_Gr_M1.Hash067.result
theorem cast067_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash067.B00.input).map Fin.val=JHc_Gr_M1.Hash067.B00.input := by rfl
#print axioms cast067_0
theorem tail067 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash067.tail).map Fin.val=JHc_Gr_M1.Hash067.tail := by rfl
#print axioms tail067
theorem numeric067 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash067.message).map Fin.val=JHc_Gr_M1.Hash067.message := by
  simp only [JHc_Gr_M1.Hash067.message,JHc_Gr_M1.Hash067.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast067_0,tail067]
#print axioms numeric067
theorem hash067 : JFp_SHADigest.digest input067=value067 := by
  unfold input067 JFp_SHADigest.digest
  rw [numeric067,JHc_Gr_M1.Hash067.checked]
  rfl
#print axioms hash067
theorem address067 : BinMerkle32Path.nodeInput (children value057 (JGc_TX2_HashBytes.state [195,20,209,28,33,12,185,7,114,250,208,29,236,188,0,141,106,128,113,110,159,175,180,255,243,33,223,145,197,31,0,147]))=input067 := by rfl
#print axioms address067
def tree067 : Tree := .branch tree057 (.supplied (JGc_TX2_HashBytes.state [195,20,209,28,33,12,185,7,114,250,208,29,236,188,0,141,106,128,113,110,159,175,180,255,243,33,223,145,197,31,0,147]))
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
def input068 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash068.message
def value068 : State := JFp_SHADigest.output JHc_Gr_M1.Hash068.result
theorem cast068_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash068.B00.input).map Fin.val=JHc_Gr_M1.Hash068.B00.input := by rfl
#print axioms cast068_0
theorem tail068 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash068.tail).map Fin.val=JHc_Gr_M1.Hash068.tail := by rfl
#print axioms tail068
theorem numeric068 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash068.message).map Fin.val=JHc_Gr_M1.Hash068.message := by
  simp only [JHc_Gr_M1.Hash068.message,JHc_Gr_M1.Hash068.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast068_0,tail068]
#print axioms numeric068
theorem hash068 : JFp_SHADigest.digest input068=value068 := by
  unfold input068 JFp_SHADigest.digest
  rw [numeric068,JHc_Gr_M1.Hash068.checked]
  rfl
#print axioms hash068
theorem address068 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [98,166,20,210,130,207,194,139,78,117,173,133,188,147,155,169,220,81,13,244,134,242,185,223,105,47,40,3,97,149,255,241]) value058)=input068 := by rfl
#print axioms address068
def tree068 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [98,166,20,210,130,207,194,139,78,117,173,133,188,147,155,169,220,81,13,244,134,242,185,223,105,47,40,3,97,149,255,241])) tree058
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
def input069 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash069.message
def value069 : State := JFp_SHADigest.output JHc_Gr_M1.Hash069.result
theorem cast069_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash069.B00.input).map Fin.val=JHc_Gr_M1.Hash069.B00.input := by rfl
#print axioms cast069_0
theorem tail069 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash069.tail).map Fin.val=JHc_Gr_M1.Hash069.tail := by rfl
#print axioms tail069
theorem numeric069 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash069.message).map Fin.val=JHc_Gr_M1.Hash069.message := by
  simp only [JHc_Gr_M1.Hash069.message,JHc_Gr_M1.Hash069.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast069_0,tail069]
#print axioms numeric069
theorem hash069 : JFp_SHADigest.digest input069=value069 := by
  unfold input069 JFp_SHADigest.digest
  rw [numeric069,JHc_Gr_M1.Hash069.checked]
  rfl
#print axioms hash069
theorem address069 : BinMerkle32Path.nodeInput (children value059 (JGc_TX2_HashBytes.state [25,110,119,90,229,115,9,14,1,136,89,142,123,146,66,240,29,42,225,45,227,245,237,143,246,109,141,79,34,148,184,86]))=input069 := by rfl
#print axioms address069
def tree069 : Tree := .branch tree059 (.supplied (JGc_TX2_HashBytes.state [25,110,119,90,229,115,9,14,1,136,89,142,123,146,66,240,29,42,225,45,227,245,237,143,246,109,141,79,34,148,184,86]))
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
end AspisR1.JHc_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input070 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash070.message
def value070 : State := JFp_SHADigest.output JHc_Gr_M1.Hash070.result
theorem cast070_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash070.B00.input).map Fin.val=JHc_Gr_M1.Hash070.B00.input := by rfl
#print axioms cast070_0
theorem tail070 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash070.tail).map Fin.val=JHc_Gr_M1.Hash070.tail := by rfl
#print axioms tail070
theorem numeric070 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash070.message).map Fin.val=JHc_Gr_M1.Hash070.message := by
  simp only [JHc_Gr_M1.Hash070.message,JHc_Gr_M1.Hash070.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast070_0,tail070]
#print axioms numeric070
theorem hash070 : JFp_SHADigest.digest input070=value070 := by
  unfold input070 JFp_SHADigest.digest
  rw [numeric070,JHc_Gr_M1.Hash070.checked]
  rfl
#print axioms hash070
theorem address070 : BinMerkle32Path.nodeInput (children value060 (JGc_TX2_HashBytes.state [213,219,66,149,132,102,202,223,2,186,92,70,102,98,174,29,190,20,146,248,36,151,27,124,170,129,132,58,230,86,6,226]))=input070 := by rfl
#print axioms address070
def tree070 : Tree := .branch tree060 (.supplied (JGc_TX2_HashBytes.state [213,219,66,149,132,102,202,223,2,186,92,70,102,98,174,29,190,20,146,248,36,151,27,124,170,129,132,58,230,86,6,226]))
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
def input071 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash071.message
def value071 : State := JFp_SHADigest.output JHc_Gr_M1.Hash071.result
theorem cast071_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash071.B00.input).map Fin.val=JHc_Gr_M1.Hash071.B00.input := by rfl
#print axioms cast071_0
theorem tail071 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash071.tail).map Fin.val=JHc_Gr_M1.Hash071.tail := by rfl
#print axioms tail071
theorem numeric071 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash071.message).map Fin.val=JHc_Gr_M1.Hash071.message := by
  simp only [JHc_Gr_M1.Hash071.message,JHc_Gr_M1.Hash071.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast071_0,tail071]
#print axioms numeric071
theorem hash071 : JFp_SHADigest.digest input071=value071 := by
  unfold input071 JFp_SHADigest.digest
  rw [numeric071,JHc_Gr_M1.Hash071.checked]
  rfl
#print axioms hash071
theorem address071 : BinMerkle32Path.nodeInput (children value061 (JGc_TX2_HashBytes.state [43,41,156,176,42,40,47,242,5,243,149,73,246,84,151,201,214,4,0,213,156,115,60,243,26,35,74,120,199,7,124,249]))=input071 := by rfl
#print axioms address071
def tree071 : Tree := .branch tree061 (.supplied (JGc_TX2_HashBytes.state [43,41,156,176,42,40,47,242,5,243,149,73,246,84,151,201,214,4,0,213,156,115,60,243,26,35,74,120,199,7,124,249]))
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
def input072 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash072.message
def value072 : State := JFp_SHADigest.output JHc_Gr_M1.Hash072.result
theorem cast072_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash072.B00.input).map Fin.val=JHc_Gr_M1.Hash072.B00.input := by rfl
#print axioms cast072_0
theorem tail072 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash072.tail).map Fin.val=JHc_Gr_M1.Hash072.tail := by rfl
#print axioms tail072
theorem numeric072 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash072.message).map Fin.val=JHc_Gr_M1.Hash072.message := by
  simp only [JHc_Gr_M1.Hash072.message,JHc_Gr_M1.Hash072.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast072_0,tail072]
#print axioms numeric072
theorem hash072 : JFp_SHADigest.digest input072=value072 := by
  unfold input072 JFp_SHADigest.digest
  rw [numeric072,JHc_Gr_M1.Hash072.checked]
  rfl
#print axioms hash072
theorem address072 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [166,169,50,209,188,5,52,23,33,230,174,188,64,116,191,107,219,82,103,128,10,79,137,212,138,189,23,60,71,204,95,45]) value062)=input072 := by rfl
#print axioms address072
def tree072 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [166,169,50,209,188,5,52,23,33,230,174,188,64,116,191,107,219,82,103,128,10,79,137,212,138,189,23,60,71,204,95,45])) tree062
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
def input073 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash073.message
def value073 : State := JFp_SHADigest.output JHc_Gr_M1.Hash073.result
theorem cast073_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash073.B00.input).map Fin.val=JHc_Gr_M1.Hash073.B00.input := by rfl
#print axioms cast073_0
theorem tail073 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash073.tail).map Fin.val=JHc_Gr_M1.Hash073.tail := by rfl
#print axioms tail073
theorem numeric073 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash073.message).map Fin.val=JHc_Gr_M1.Hash073.message := by
  simp only [JHc_Gr_M1.Hash073.message,JHc_Gr_M1.Hash073.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast073_0,tail073]
#print axioms numeric073
theorem hash073 : JFp_SHADigest.digest input073=value073 := by
  unfold input073 JFp_SHADigest.digest
  rw [numeric073,JHc_Gr_M1.Hash073.checked]
  rfl
#print axioms hash073
theorem address073 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [26,45,196,149,156,185,207,108,35,63,83,156,140,215,142,227,222,78,13,88,119,76,111,150,75,170,136,157,17,249,95,75]) value063)=input073 := by rfl
#print axioms address073
def tree073 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [26,45,196,149,156,185,207,108,35,63,83,156,140,215,142,227,222,78,13,88,119,76,111,150,75,170,136,157,17,249,95,75])) tree063
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
def input074 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash074.message
def value074 : State := JFp_SHADigest.output JHc_Gr_M1.Hash074.result
theorem cast074_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash074.B00.input).map Fin.val=JHc_Gr_M1.Hash074.B00.input := by rfl
#print axioms cast074_0
theorem tail074 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash074.tail).map Fin.val=JHc_Gr_M1.Hash074.tail := by rfl
#print axioms tail074
theorem numeric074 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash074.message).map Fin.val=JHc_Gr_M1.Hash074.message := by
  simp only [JHc_Gr_M1.Hash074.message,JHc_Gr_M1.Hash074.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast074_0,tail074]
#print axioms numeric074
theorem hash074 : JFp_SHADigest.digest input074=value074 := by
  unfold input074 JFp_SHADigest.digest
  rw [numeric074,JHc_Gr_M1.Hash074.checked]
  rfl
#print axioms hash074
theorem address074 : BinMerkle32Path.nodeInput (children value064 (JGc_TX2_HashBytes.state [187,168,249,177,7,164,3,149,98,161,102,174,50,138,206,11,30,72,150,177,137,51,106,119,176,70,87,242,152,194,189,85]))=input074 := by rfl
#print axioms address074
def tree074 : Tree := .branch tree064 (.supplied (JGc_TX2_HashBytes.state [187,168,249,177,7,164,3,149,98,161,102,174,50,138,206,11,30,72,150,177,137,51,106,119,176,70,87,242,152,194,189,85]))
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
def input075 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash075.message
def value075 : State := JFp_SHADigest.output JHc_Gr_M1.Hash075.result
theorem cast075_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash075.B00.input).map Fin.val=JHc_Gr_M1.Hash075.B00.input := by rfl
#print axioms cast075_0
theorem tail075 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash075.tail).map Fin.val=JHc_Gr_M1.Hash075.tail := by rfl
#print axioms tail075
theorem numeric075 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash075.message).map Fin.val=JHc_Gr_M1.Hash075.message := by
  simp only [JHc_Gr_M1.Hash075.message,JHc_Gr_M1.Hash075.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast075_0,tail075]
#print axioms numeric075
theorem hash075 : JFp_SHADigest.digest input075=value075 := by
  unfold input075 JFp_SHADigest.digest
  rw [numeric075,JHc_Gr_M1.Hash075.checked]
  rfl
#print axioms hash075
theorem address075 : BinMerkle32Path.nodeInput (children value065 (JGc_TX2_HashBytes.state [73,221,130,144,71,67,136,79,167,63,161,205,39,10,20,47,38,23,24,180,153,220,23,255,9,108,57,158,87,153,49,94]))=input075 := by rfl
#print axioms address075
def tree075 : Tree := .branch tree065 (.supplied (JGc_TX2_HashBytes.state [73,221,130,144,71,67,136,79,167,63,161,205,39,10,20,47,38,23,24,180,153,220,23,255,9,108,57,158,87,153,49,94]))
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
def input076 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash076.message
def value076 : State := JFp_SHADigest.output JHc_Gr_M1.Hash076.result
theorem cast076_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash076.B00.input).map Fin.val=JHc_Gr_M1.Hash076.B00.input := by rfl
#print axioms cast076_0
theorem tail076 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash076.tail).map Fin.val=JHc_Gr_M1.Hash076.tail := by rfl
#print axioms tail076
theorem numeric076 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash076.message).map Fin.val=JHc_Gr_M1.Hash076.message := by
  simp only [JHc_Gr_M1.Hash076.message,JHc_Gr_M1.Hash076.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast076_0,tail076]
#print axioms numeric076
theorem hash076 : JFp_SHADigest.digest input076=value076 := by
  unfold input076 JFp_SHADigest.digest
  rw [numeric076,JHc_Gr_M1.Hash076.checked]
  rfl
#print axioms hash076
theorem address076 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [167,255,250,78,90,35,106,202,120,194,253,220,221,11,157,53,242,35,22,107,23,89,62,195,225,140,7,190,221,244,119,208]) value066)=input076 := by rfl
#print axioms address076
def tree076 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [167,255,250,78,90,35,106,202,120,194,253,220,221,11,157,53,242,35,22,107,23,89,62,195,225,140,7,190,221,244,119,208])) tree066
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
def input077 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash077.message
def value077 : State := JFp_SHADigest.output JHc_Gr_M1.Hash077.result
theorem cast077_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash077.B00.input).map Fin.val=JHc_Gr_M1.Hash077.B00.input := by rfl
#print axioms cast077_0
theorem tail077 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash077.tail).map Fin.val=JHc_Gr_M1.Hash077.tail := by rfl
#print axioms tail077
theorem numeric077 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash077.message).map Fin.val=JHc_Gr_M1.Hash077.message := by
  simp only [JHc_Gr_M1.Hash077.message,JHc_Gr_M1.Hash077.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast077_0,tail077]
#print axioms numeric077
theorem hash077 : JFp_SHADigest.digest input077=value077 := by
  unfold input077 JFp_SHADigest.digest
  rw [numeric077,JHc_Gr_M1.Hash077.checked]
  rfl
#print axioms hash077
theorem address077 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [214,112,195,229,164,168,187,90,35,77,255,198,103,221,16,135,157,106,196,94,83,69,143,19,82,171,67,25,74,114,34,81]) value067)=input077 := by rfl
#print axioms address077
def tree077 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [214,112,195,229,164,168,187,90,35,77,255,198,103,221,16,135,157,106,196,94,83,69,143,19,82,171,67,25,74,114,34,81])) tree067
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
def input078 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash078.message
def value078 : State := JFp_SHADigest.output JHc_Gr_M1.Hash078.result
theorem cast078_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash078.B00.input).map Fin.val=JHc_Gr_M1.Hash078.B00.input := by rfl
#print axioms cast078_0
theorem tail078 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash078.tail).map Fin.val=JHc_Gr_M1.Hash078.tail := by rfl
#print axioms tail078
theorem numeric078 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash078.message).map Fin.val=JHc_Gr_M1.Hash078.message := by
  simp only [JHc_Gr_M1.Hash078.message,JHc_Gr_M1.Hash078.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast078_0,tail078]
#print axioms numeric078
theorem hash078 : JFp_SHADigest.digest input078=value078 := by
  unfold input078 JFp_SHADigest.digest
  rw [numeric078,JHc_Gr_M1.Hash078.checked]
  rfl
#print axioms hash078
theorem address078 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [99,164,177,65,229,155,166,198,59,58,144,40,119,57,191,57,32,230,224,109,132,52,196,152,102,228,8,147,143,111,177,238]) value068)=input078 := by rfl
#print axioms address078
def tree078 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [99,164,177,65,229,155,166,198,59,58,144,40,119,57,191,57,32,230,224,109,132,52,196,152,102,228,8,147,143,111,177,238])) tree068
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
def input079 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash079.message
def value079 : State := JFp_SHADigest.output JHc_Gr_M1.Hash079.result
theorem cast079_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash079.B00.input).map Fin.val=JHc_Gr_M1.Hash079.B00.input := by rfl
#print axioms cast079_0
theorem tail079 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash079.tail).map Fin.val=JHc_Gr_M1.Hash079.tail := by rfl
#print axioms tail079
theorem numeric079 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash079.message).map Fin.val=JHc_Gr_M1.Hash079.message := by
  simp only [JHc_Gr_M1.Hash079.message,JHc_Gr_M1.Hash079.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast079_0,tail079]
#print axioms numeric079
theorem hash079 : JFp_SHADigest.digest input079=value079 := by
  unfold input079 JFp_SHADigest.digest
  rw [numeric079,JHc_Gr_M1.Hash079.checked]
  rfl
#print axioms hash079
theorem address079 : BinMerkle32Path.nodeInput (children value069 (JGc_TX2_HashBytes.state [206,137,116,72,150,225,247,109,190,174,193,175,97,74,39,239,82,242,9,20,245,218,106,203,31,54,175,142,188,88,174,158]))=input079 := by rfl
#print axioms address079
def tree079 : Tree := .branch tree069 (.supplied (JGc_TX2_HashBytes.state [206,137,116,72,150,225,247,109,190,174,193,175,97,74,39,239,82,242,9,20,245,218,106,203,31,54,175,142,188,88,174,158]))
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
end AspisR1.JHc_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input080 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash080.message
def value080 : State := JFp_SHADigest.output JHc_Gr_M1.Hash080.result
theorem cast080_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash080.B00.input).map Fin.val=JHc_Gr_M1.Hash080.B00.input := by rfl
#print axioms cast080_0
theorem tail080 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash080.tail).map Fin.val=JHc_Gr_M1.Hash080.tail := by rfl
#print axioms tail080
theorem numeric080 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash080.message).map Fin.val=JHc_Gr_M1.Hash080.message := by
  simp only [JHc_Gr_M1.Hash080.message,JHc_Gr_M1.Hash080.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast080_0,tail080]
#print axioms numeric080
theorem hash080 : JFp_SHADigest.digest input080=value080 := by
  unfold input080 JFp_SHADigest.digest
  rw [numeric080,JHc_Gr_M1.Hash080.checked]
  rfl
#print axioms hash080
theorem address080 : BinMerkle32Path.nodeInput (children value070 (JGc_TX2_HashBytes.state [86,144,167,147,188,24,122,130,134,42,53,1,191,205,208,232,136,53,92,205,132,56,195,95,102,211,36,136,20,102,109,234]))=input080 := by rfl
#print axioms address080
def tree080 : Tree := .branch tree070 (.supplied (JGc_TX2_HashBytes.state [86,144,167,147,188,24,122,130,134,42,53,1,191,205,208,232,136,53,92,205,132,56,195,95,102,211,36,136,20,102,109,234]))
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
def input081 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash081.message
def value081 : State := JFp_SHADigest.output JHc_Gr_M1.Hash081.result
theorem cast081_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash081.B00.input).map Fin.val=JHc_Gr_M1.Hash081.B00.input := by rfl
#print axioms cast081_0
theorem tail081 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash081.tail).map Fin.val=JHc_Gr_M1.Hash081.tail := by rfl
#print axioms tail081
theorem numeric081 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash081.message).map Fin.val=JHc_Gr_M1.Hash081.message := by
  simp only [JHc_Gr_M1.Hash081.message,JHc_Gr_M1.Hash081.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast081_0,tail081]
#print axioms numeric081
theorem hash081 : JFp_SHADigest.digest input081=value081 := by
  unfold input081 JFp_SHADigest.digest
  rw [numeric081,JHc_Gr_M1.Hash081.checked]
  rfl
#print axioms hash081
theorem address081 : BinMerkle32Path.nodeInput (children value071 (JGc_TX2_HashBytes.state [129,134,159,111,208,119,101,44,121,214,241,176,100,83,224,186,157,157,52,15,168,151,4,234,77,57,92,217,53,20,243,178]))=input081 := by rfl
#print axioms address081
def tree081 : Tree := .branch tree071 (.supplied (JGc_TX2_HashBytes.state [129,134,159,111,208,119,101,44,121,214,241,176,100,83,224,186,157,157,52,15,168,151,4,234,77,57,92,217,53,20,243,178]))
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
def input082 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash082.message
def value082 : State := JFp_SHADigest.output JHc_Gr_M1.Hash082.result
theorem cast082_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash082.B00.input).map Fin.val=JHc_Gr_M1.Hash082.B00.input := by rfl
#print axioms cast082_0
theorem tail082 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash082.tail).map Fin.val=JHc_Gr_M1.Hash082.tail := by rfl
#print axioms tail082
theorem numeric082 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash082.message).map Fin.val=JHc_Gr_M1.Hash082.message := by
  simp only [JHc_Gr_M1.Hash082.message,JHc_Gr_M1.Hash082.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast082_0,tail082]
#print axioms numeric082
theorem hash082 : JFp_SHADigest.digest input082=value082 := by
  unfold input082 JFp_SHADigest.digest
  rw [numeric082,JHc_Gr_M1.Hash082.checked]
  rfl
#print axioms hash082
theorem address082 : BinMerkle32Path.nodeInput (children value072 (JGc_TX2_HashBytes.state [229,14,215,228,251,27,121,138,26,111,165,216,200,216,201,136,85,212,71,42,31,194,225,192,175,105,184,67,0,188,222,153]))=input082 := by rfl
#print axioms address082
def tree082 : Tree := .branch tree072 (.supplied (JGc_TX2_HashBytes.state [229,14,215,228,251,27,121,138,26,111,165,216,200,216,201,136,85,212,71,42,31,194,225,192,175,105,184,67,0,188,222,153]))
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
def input083 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash083.message
def value083 : State := JFp_SHADigest.output JHc_Gr_M1.Hash083.result
theorem cast083_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash083.B00.input).map Fin.val=JHc_Gr_M1.Hash083.B00.input := by rfl
#print axioms cast083_0
theorem tail083 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash083.tail).map Fin.val=JHc_Gr_M1.Hash083.tail := by rfl
#print axioms tail083
theorem numeric083 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash083.message).map Fin.val=JHc_Gr_M1.Hash083.message := by
  simp only [JHc_Gr_M1.Hash083.message,JHc_Gr_M1.Hash083.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast083_0,tail083]
#print axioms numeric083
theorem hash083 : JFp_SHADigest.digest input083=value083 := by
  unfold input083 JFp_SHADigest.digest
  rw [numeric083,JHc_Gr_M1.Hash083.checked]
  rfl
#print axioms hash083
theorem address083 : BinMerkle32Path.nodeInput (children value073 (JGc_TX2_HashBytes.state [46,123,57,164,118,22,77,38,72,105,83,9,179,113,17,42,45,247,143,151,243,173,174,143,222,205,203,31,224,130,255,177]))=input083 := by rfl
#print axioms address083
def tree083 : Tree := .branch tree073 (.supplied (JGc_TX2_HashBytes.state [46,123,57,164,118,22,77,38,72,105,83,9,179,113,17,42,45,247,143,151,243,173,174,143,222,205,203,31,224,130,255,177]))
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
def input084 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash084.message
def value084 : State := JFp_SHADigest.output JHc_Gr_M1.Hash084.result
theorem cast084_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash084.B00.input).map Fin.val=JHc_Gr_M1.Hash084.B00.input := by rfl
#print axioms cast084_0
theorem tail084 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash084.tail).map Fin.val=JHc_Gr_M1.Hash084.tail := by rfl
#print axioms tail084
theorem numeric084 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash084.message).map Fin.val=JHc_Gr_M1.Hash084.message := by
  simp only [JHc_Gr_M1.Hash084.message,JHc_Gr_M1.Hash084.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast084_0,tail084]
#print axioms numeric084
theorem hash084 : JFp_SHADigest.digest input084=value084 := by
  unfold input084 JFp_SHADigest.digest
  rw [numeric084,JHc_Gr_M1.Hash084.checked]
  rfl
#print axioms hash084
theorem address084 : BinMerkle32Path.nodeInput (children value074 (JGc_TX2_HashBytes.state [20,207,22,9,174,31,23,223,78,200,11,111,211,240,97,165,212,117,32,89,62,177,230,187,171,248,29,209,77,89,205,216]))=input084 := by rfl
#print axioms address084
def tree084 : Tree := .branch tree074 (.supplied (JGc_TX2_HashBytes.state [20,207,22,9,174,31,23,223,78,200,11,111,211,240,97,165,212,117,32,89,62,177,230,187,171,248,29,209,77,89,205,216]))
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
def input085 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash085.message
def value085 : State := JFp_SHADigest.output JHc_Gr_M1.Hash085.result
theorem cast085_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash085.B00.input).map Fin.val=JHc_Gr_M1.Hash085.B00.input := by rfl
#print axioms cast085_0
theorem tail085 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash085.tail).map Fin.val=JHc_Gr_M1.Hash085.tail := by rfl
#print axioms tail085
theorem numeric085 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash085.message).map Fin.val=JHc_Gr_M1.Hash085.message := by
  simp only [JHc_Gr_M1.Hash085.message,JHc_Gr_M1.Hash085.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast085_0,tail085]
#print axioms numeric085
theorem hash085 : JFp_SHADigest.digest input085=value085 := by
  unfold input085 JFp_SHADigest.digest
  rw [numeric085,JHc_Gr_M1.Hash085.checked]
  rfl
#print axioms hash085
theorem address085 : BinMerkle32Path.nodeInput (children value075 (JGc_TX2_HashBytes.state [152,7,48,143,226,24,235,182,175,169,50,91,216,225,126,157,236,234,179,168,64,123,15,245,94,142,196,215,212,12,175,250]))=input085 := by rfl
#print axioms address085
def tree085 : Tree := .branch tree075 (.supplied (JGc_TX2_HashBytes.state [152,7,48,143,226,24,235,182,175,169,50,91,216,225,126,157,236,234,179,168,64,123,15,245,94,142,196,215,212,12,175,250]))
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
def input086 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash086.message
def value086 : State := JFp_SHADigest.output JHc_Gr_M1.Hash086.result
theorem cast086_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash086.B00.input).map Fin.val=JHc_Gr_M1.Hash086.B00.input := by rfl
#print axioms cast086_0
theorem tail086 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash086.tail).map Fin.val=JHc_Gr_M1.Hash086.tail := by rfl
#print axioms tail086
theorem numeric086 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash086.message).map Fin.val=JHc_Gr_M1.Hash086.message := by
  simp only [JHc_Gr_M1.Hash086.message,JHc_Gr_M1.Hash086.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast086_0,tail086]
#print axioms numeric086
theorem hash086 : JFp_SHADigest.digest input086=value086 := by
  unfold input086 JFp_SHADigest.digest
  rw [numeric086,JHc_Gr_M1.Hash086.checked]
  rfl
#print axioms hash086
theorem address086 : BinMerkle32Path.nodeInput (children value076 (JGc_TX2_HashBytes.state [152,67,185,114,180,230,228,197,92,49,68,3,243,160,35,107,236,112,86,221,8,66,205,238,116,218,35,5,165,164,99,104]))=input086 := by rfl
#print axioms address086
def tree086 : Tree := .branch tree076 (.supplied (JGc_TX2_HashBytes.state [152,67,185,114,180,230,228,197,92,49,68,3,243,160,35,107,236,112,86,221,8,66,205,238,116,218,35,5,165,164,99,104]))
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
def input087 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash087.message
def value087 : State := JFp_SHADigest.output JHc_Gr_M1.Hash087.result
theorem cast087_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash087.B00.input).map Fin.val=JHc_Gr_M1.Hash087.B00.input := by rfl
#print axioms cast087_0
theorem tail087 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash087.tail).map Fin.val=JHc_Gr_M1.Hash087.tail := by rfl
#print axioms tail087
theorem numeric087 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash087.message).map Fin.val=JHc_Gr_M1.Hash087.message := by
  simp only [JHc_Gr_M1.Hash087.message,JHc_Gr_M1.Hash087.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast087_0,tail087]
#print axioms numeric087
theorem hash087 : JFp_SHADigest.digest input087=value087 := by
  unfold input087 JFp_SHADigest.digest
  rw [numeric087,JHc_Gr_M1.Hash087.checked]
  rfl
#print axioms hash087
theorem address087 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [121,222,231,1,61,67,70,17,115,85,96,65,234,200,241,83,60,16,185,45,192,179,155,106,241,106,46,40,153,49,208,171]) value077)=input087 := by rfl
#print axioms address087
def tree087 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [121,222,231,1,61,67,70,17,115,85,96,65,234,200,241,83,60,16,185,45,192,179,155,106,241,106,46,40,153,49,208,171])) tree077
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
def input088 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash088.message
def value088 : State := JFp_SHADigest.output JHc_Gr_M1.Hash088.result
theorem cast088_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash088.B00.input).map Fin.val=JHc_Gr_M1.Hash088.B00.input := by rfl
#print axioms cast088_0
theorem tail088 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash088.tail).map Fin.val=JHc_Gr_M1.Hash088.tail := by rfl
#print axioms tail088
theorem numeric088 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash088.message).map Fin.val=JHc_Gr_M1.Hash088.message := by
  simp only [JHc_Gr_M1.Hash088.message,JHc_Gr_M1.Hash088.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast088_0,tail088]
#print axioms numeric088
theorem hash088 : JFp_SHADigest.digest input088=value088 := by
  unfold input088 JFp_SHADigest.digest
  rw [numeric088,JHc_Gr_M1.Hash088.checked]
  rfl
#print axioms hash088
theorem address088 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [236,28,32,239,13,157,49,221,114,96,197,120,98,199,111,87,83,234,74,238,160,52,25,26,27,9,205,113,23,81,124,152]) value078)=input088 := by rfl
#print axioms address088
def tree088 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [236,28,32,239,13,157,49,221,114,96,197,120,98,199,111,87,83,234,74,238,160,52,25,26,27,9,205,113,23,81,124,152])) tree078
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
def input089 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash089.message
def value089 : State := JFp_SHADigest.output JHc_Gr_M1.Hash089.result
theorem cast089_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash089.B00.input).map Fin.val=JHc_Gr_M1.Hash089.B00.input := by rfl
#print axioms cast089_0
theorem tail089 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash089.tail).map Fin.val=JHc_Gr_M1.Hash089.tail := by rfl
#print axioms tail089
theorem numeric089 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash089.message).map Fin.val=JHc_Gr_M1.Hash089.message := by
  simp only [JHc_Gr_M1.Hash089.message,JHc_Gr_M1.Hash089.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast089_0,tail089]
#print axioms numeric089
theorem hash089 : JFp_SHADigest.digest input089=value089 := by
  unfold input089 JFp_SHADigest.digest
  rw [numeric089,JHc_Gr_M1.Hash089.checked]
  rfl
#print axioms hash089
theorem address089 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [253,228,39,179,67,102,132,204,126,95,1,242,155,20,213,142,13,57,24,198,222,113,242,180,142,143,35,176,242,56,84,56]) value079)=input089 := by rfl
#print axioms address089
def tree089 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [253,228,39,179,67,102,132,204,126,95,1,242,155,20,213,142,13,57,24,198,222,113,242,180,142,143,35,176,242,56,84,56])) tree079
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
end AspisR1.JHc_Gr_M1Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Gr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input090 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash090.message
def value090 : State := JFp_SHADigest.output JHc_Gr_M1.Hash090.result
theorem cast090_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash090.B00.input).map Fin.val=JHc_Gr_M1.Hash090.B00.input := by rfl
#print axioms cast090_0
theorem tail090 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash090.tail).map Fin.val=JHc_Gr_M1.Hash090.tail := by rfl
#print axioms tail090
theorem numeric090 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash090.message).map Fin.val=JHc_Gr_M1.Hash090.message := by
  simp only [JHc_Gr_M1.Hash090.message,JHc_Gr_M1.Hash090.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast090_0,tail090]
#print axioms numeric090
theorem hash090 : JFp_SHADigest.digest input090=value090 := by
  unfold input090 JFp_SHADigest.digest
  rw [numeric090,JHc_Gr_M1.Hash090.checked]
  rfl
#print axioms hash090
theorem address090 : BinMerkle32Path.nodeInput (children value080 (JGc_TX2_HashBytes.state [155,103,85,214,79,217,145,109,92,61,81,23,89,65,105,137,67,6,203,28,29,132,157,255,203,70,84,95,242,123,36,113]))=input090 := by rfl
#print axioms address090
def tree090 : Tree := .branch tree080 (.supplied (JGc_TX2_HashBytes.state [155,103,85,214,79,217,145,109,92,61,81,23,89,65,105,137,67,6,203,28,29,132,157,255,203,70,84,95,242,123,36,113]))
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
def input091 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash091.message
def value091 : State := JFp_SHADigest.output JHc_Gr_M1.Hash091.result
theorem cast091_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash091.B00.input).map Fin.val=JHc_Gr_M1.Hash091.B00.input := by rfl
#print axioms cast091_0
theorem tail091 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash091.tail).map Fin.val=JHc_Gr_M1.Hash091.tail := by rfl
#print axioms tail091
theorem numeric091 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash091.message).map Fin.val=JHc_Gr_M1.Hash091.message := by
  simp only [JHc_Gr_M1.Hash091.message,JHc_Gr_M1.Hash091.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast091_0,tail091]
#print axioms numeric091
theorem hash091 : JFp_SHADigest.digest input091=value091 := by
  unfold input091 JFp_SHADigest.digest
  rw [numeric091,JHc_Gr_M1.Hash091.checked]
  rfl
#print axioms hash091
theorem address091 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [58,116,96,190,215,232,35,221,38,191,2,90,224,44,164,216,51,1,133,148,238,15,199,54,87,187,234,15,80,91,124,127]) value081)=input091 := by rfl
#print axioms address091
def tree091 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [58,116,96,190,215,232,35,221,38,191,2,90,224,44,164,216,51,1,133,148,238,15,199,54,87,187,234,15,80,91,124,127])) tree081
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
def input092 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash092.message
def value092 : State := JFp_SHADigest.output JHc_Gr_M1.Hash092.result
theorem cast092_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash092.B00.input).map Fin.val=JHc_Gr_M1.Hash092.B00.input := by rfl
#print axioms cast092_0
theorem tail092 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash092.tail).map Fin.val=JHc_Gr_M1.Hash092.tail := by rfl
#print axioms tail092
theorem numeric092 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash092.message).map Fin.val=JHc_Gr_M1.Hash092.message := by
  simp only [JHc_Gr_M1.Hash092.message,JHc_Gr_M1.Hash092.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast092_0,tail092]
#print axioms numeric092
theorem hash092 : JFp_SHADigest.digest input092=value092 := by
  unfold input092 JFp_SHADigest.digest
  rw [numeric092,JHc_Gr_M1.Hash092.checked]
  rfl
#print axioms hash092
theorem address092 : BinMerkle32Path.nodeInput (children value082 (JGc_TX2_HashBytes.state [102,248,91,151,181,176,166,53,114,57,78,102,66,87,251,100,251,31,205,194,110,147,127,156,193,58,19,3,42,214,148,4]))=input092 := by rfl
#print axioms address092
def tree092 : Tree := .branch tree082 (.supplied (JGc_TX2_HashBytes.state [102,248,91,151,181,176,166,53,114,57,78,102,66,87,251,100,251,31,205,194,110,147,127,156,193,58,19,3,42,214,148,4]))
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
def input093 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash093.message
def value093 : State := JFp_SHADigest.output JHc_Gr_M1.Hash093.result
theorem cast093_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash093.B00.input).map Fin.val=JHc_Gr_M1.Hash093.B00.input := by rfl
#print axioms cast093_0
theorem tail093 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash093.tail).map Fin.val=JHc_Gr_M1.Hash093.tail := by rfl
#print axioms tail093
theorem numeric093 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash093.message).map Fin.val=JHc_Gr_M1.Hash093.message := by
  simp only [JHc_Gr_M1.Hash093.message,JHc_Gr_M1.Hash093.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast093_0,tail093]
#print axioms numeric093
theorem hash093 : JFp_SHADigest.digest input093=value093 := by
  unfold input093 JFp_SHADigest.digest
  rw [numeric093,JHc_Gr_M1.Hash093.checked]
  rfl
#print axioms hash093
theorem address093 : BinMerkle32Path.nodeInput (children value083 (JGc_TX2_HashBytes.state [181,230,180,31,12,17,59,166,205,11,33,224,169,103,22,14,162,127,69,73,33,189,217,17,98,68,108,205,174,164,64,124]))=input093 := by rfl
#print axioms address093
def tree093 : Tree := .branch tree083 (.supplied (JGc_TX2_HashBytes.state [181,230,180,31,12,17,59,166,205,11,33,224,169,103,22,14,162,127,69,73,33,189,217,17,98,68,108,205,174,164,64,124]))
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
def input094 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash094.message
def value094 : State := JFp_SHADigest.output JHc_Gr_M1.Hash094.result
theorem cast094_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash094.B00.input).map Fin.val=JHc_Gr_M1.Hash094.B00.input := by rfl
#print axioms cast094_0
theorem tail094 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash094.tail).map Fin.val=JHc_Gr_M1.Hash094.tail := by rfl
#print axioms tail094
theorem numeric094 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash094.message).map Fin.val=JHc_Gr_M1.Hash094.message := by
  simp only [JHc_Gr_M1.Hash094.message,JHc_Gr_M1.Hash094.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast094_0,tail094]
#print axioms numeric094
theorem hash094 : JFp_SHADigest.digest input094=value094 := by
  unfold input094 JFp_SHADigest.digest
  rw [numeric094,JHc_Gr_M1.Hash094.checked]
  rfl
#print axioms hash094
theorem address094 : BinMerkle32Path.nodeInput (children value084 (JGc_TX2_HashBytes.state [190,94,5,136,17,62,168,184,31,168,135,148,106,201,77,251,86,192,166,220,228,214,230,238,13,228,237,219,153,182,6,97]))=input094 := by rfl
#print axioms address094
def tree094 : Tree := .branch tree084 (.supplied (JGc_TX2_HashBytes.state [190,94,5,136,17,62,168,184,31,168,135,148,106,201,77,251,86,192,166,220,228,214,230,238,13,228,237,219,153,182,6,97]))
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
def input095 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash095.message
def value095 : State := JFp_SHADigest.output JHc_Gr_M1.Hash095.result
theorem cast095_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash095.B00.input).map Fin.val=JHc_Gr_M1.Hash095.B00.input := by rfl
#print axioms cast095_0
theorem tail095 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash095.tail).map Fin.val=JHc_Gr_M1.Hash095.tail := by rfl
#print axioms tail095
theorem numeric095 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash095.message).map Fin.val=JHc_Gr_M1.Hash095.message := by
  simp only [JHc_Gr_M1.Hash095.message,JHc_Gr_M1.Hash095.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast095_0,tail095]
#print axioms numeric095
theorem hash095 : JFp_SHADigest.digest input095=value095 := by
  unfold input095 JFp_SHADigest.digest
  rw [numeric095,JHc_Gr_M1.Hash095.checked]
  rfl
#print axioms hash095
theorem address095 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [101,117,98,190,161,169,31,147,28,228,55,74,81,235,49,28,180,213,167,50,32,72,106,99,146,44,200,203,152,20,148,224]) value085)=input095 := by rfl
#print axioms address095
def tree095 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [101,117,98,190,161,169,31,147,28,228,55,74,81,235,49,28,180,213,167,50,32,72,106,99,146,44,200,203,152,20,148,224])) tree085
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
def input096 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash096.message
def value096 : State := JFp_SHADigest.output JHc_Gr_M1.Hash096.result
theorem cast096_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash096.B00.input).map Fin.val=JHc_Gr_M1.Hash096.B00.input := by rfl
#print axioms cast096_0
theorem tail096 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash096.tail).map Fin.val=JHc_Gr_M1.Hash096.tail := by rfl
#print axioms tail096
theorem numeric096 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash096.message).map Fin.val=JHc_Gr_M1.Hash096.message := by
  simp only [JHc_Gr_M1.Hash096.message,JHc_Gr_M1.Hash096.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast096_0,tail096]
#print axioms numeric096
theorem hash096 : JFp_SHADigest.digest input096=value096 := by
  unfold input096 JFp_SHADigest.digest
  rw [numeric096,JHc_Gr_M1.Hash096.checked]
  rfl
#print axioms hash096
theorem address096 : BinMerkle32Path.nodeInput (children value086 (JGc_TX2_HashBytes.state [141,78,139,205,243,175,85,174,159,6,241,87,39,153,190,45,228,30,233,41,84,56,127,174,209,151,54,93,242,26,164,0]))=input096 := by rfl
#print axioms address096
def tree096 : Tree := .branch tree086 (.supplied (JGc_TX2_HashBytes.state [141,78,139,205,243,175,85,174,159,6,241,87,39,153,190,45,228,30,233,41,84,56,127,174,209,151,54,93,242,26,164,0]))
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
def input097 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash097.message
def value097 : State := JFp_SHADigest.output JHc_Gr_M1.Hash097.result
theorem cast097_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash097.B00.input).map Fin.val=JHc_Gr_M1.Hash097.B00.input := by rfl
#print axioms cast097_0
theorem tail097 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash097.tail).map Fin.val=JHc_Gr_M1.Hash097.tail := by rfl
#print axioms tail097
theorem numeric097 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash097.message).map Fin.val=JHc_Gr_M1.Hash097.message := by
  simp only [JHc_Gr_M1.Hash097.message,JHc_Gr_M1.Hash097.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast097_0,tail097]
#print axioms numeric097
theorem hash097 : JFp_SHADigest.digest input097=value097 := by
  unfold input097 JFp_SHADigest.digest
  rw [numeric097,JHc_Gr_M1.Hash097.checked]
  rfl
#print axioms hash097
theorem address097 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [243,43,79,171,171,236,158,171,6,102,177,162,155,60,85,93,158,195,157,106,68,63,238,61,71,98,3,55,236,229,85,103]) value087)=input097 := by rfl
#print axioms address097
def tree097 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [243,43,79,171,171,236,158,171,6,102,177,162,155,60,85,93,158,195,157,106,68,63,238,61,71,98,3,55,236,229,85,103])) tree087
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
def input098 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash098.message
def value098 : State := JFp_SHADigest.output JHc_Gr_M1.Hash098.result
theorem cast098_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash098.B00.input).map Fin.val=JHc_Gr_M1.Hash098.B00.input := by rfl
#print axioms cast098_0
theorem tail098 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash098.tail).map Fin.val=JHc_Gr_M1.Hash098.tail := by rfl
#print axioms tail098
theorem numeric098 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash098.message).map Fin.val=JHc_Gr_M1.Hash098.message := by
  simp only [JHc_Gr_M1.Hash098.message,JHc_Gr_M1.Hash098.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast098_0,tail098]
#print axioms numeric098
theorem hash098 : JFp_SHADigest.digest input098=value098 := by
  unfold input098 JFp_SHADigest.digest
  rw [numeric098,JHc_Gr_M1.Hash098.checked]
  rfl
#print axioms hash098
theorem address098 : BinMerkle32Path.nodeInput (children value088 (JGc_TX2_HashBytes.state [0,59,195,249,83,130,210,170,7,120,9,195,215,100,15,59,6,122,239,166,176,134,205,3,143,184,111,215,61,93,21,205]))=input098 := by rfl
#print axioms address098
def tree098 : Tree := .branch tree088 (.supplied (JGc_TX2_HashBytes.state [0,59,195,249,83,130,210,170,7,120,9,195,215,100,15,59,6,122,239,166,176,134,205,3,143,184,111,215,61,93,21,205]))
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
def input099 : Bytes := JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash099.message
def value099 : State := JFp_SHADigest.output JHc_Gr_M1.Hash099.result
theorem cast099_0 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash099.B00.input).map Fin.val=JHc_Gr_M1.Hash099.B00.input := by rfl
#print axioms cast099_0
theorem tail099 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash099.tail).map Fin.val=JHc_Gr_M1.Hash099.tail := by rfl
#print axioms tail099
theorem numeric099 : (JGc_TX2_HashBytes.bytes JHc_Gr_M1.Hash099.message).map Fin.val=JHc_Gr_M1.Hash099.message := by
  simp only [JHc_Gr_M1.Hash099.message,JHc_Gr_M1.Hash099.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast099_0,tail099]
#print axioms numeric099
theorem hash099 : JFp_SHADigest.digest input099=value099 := by
  unfold input099 JFp_SHADigest.digest
  rw [numeric099,JHc_Gr_M1.Hash099.checked]
  rfl
#print axioms hash099
theorem address099 : BinMerkle32Path.nodeInput (children value089 (JGc_TX2_HashBytes.state [30,110,144,85,51,255,13,5,112,59,188,211,168,27,244,37,155,108,73,250,65,218,219,68,254,71,61,200,99,148,247,126]))=input099 := by rfl
#print axioms address099
def tree099 : Tree := .branch tree089 (.supplied (JGc_TX2_HashBytes.state [30,110,144,85,51,255,13,5,112,59,188,211,168,27,244,37,155,108,73,250,65,218,219,68,254,71,61,200,99,148,247,126]))
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
end AspisR1.JHc_Gr_M1Roots
end
