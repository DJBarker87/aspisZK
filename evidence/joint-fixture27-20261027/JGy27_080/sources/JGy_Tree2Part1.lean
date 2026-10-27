import JGy_Tree2Part0
import JGy_Certs2_01
import JGy_Certs2_02
import JGy_Certs2_03
import JGy_Certs2_04
import JGy_Certs2_05
import JGy_Certs2_06
import JGy_Certs2_07
import JGy_Certs2_08
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input010 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash010.message
def value010 : State := JFp_SHADigest.output JGy_Gr_M2.Hash010.result
theorem cast010_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash010.B00.input).map Fin.val=JGy_Gr_M2.Hash010.B00.input := by rfl
#print axioms cast010_0
theorem tail010 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash010.tail).map Fin.val=JGy_Gr_M2.Hash010.tail := by rfl
#print axioms tail010
theorem numeric010 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash010.message).map Fin.val=JGy_Gr_M2.Hash010.message := by
  simp only [JGy_Gr_M2.Hash010.message,JGy_Gr_M2.Hash010.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast010_0,tail010]
#print axioms numeric010
theorem hash010 : JFp_SHADigest.digest input010=value010 := by
  unfold input010 JFp_SHADigest.digest
  rw [numeric010,JGy_Gr_M2.Hash010.checked]
  rfl
#print axioms hash010
theorem address010 : BinMerkle32Path.nodeInput (children value006 (JGc_TX2_HashBytes.state [59,19,2,0,169,92,95,200,80,218,215,254,63,229,202,59,255,62,34,152,178,252,191,0,154,18,160,100,127,195,236,140]))=input010 := by rfl
#print axioms address010
def tree010 : Tree := .branch tree006 (.supplied (JGc_TX2_HashBytes.state [59,19,2,0,169,92,95,200,80,218,215,254,63,229,202,59,255,62,34,152,178,252,191,0,154,18,160,100,127,195,236,140]))
theorem root010 : root JFp_SHADigest.digest tree010=value010 := by
  rw [tree010,root,root006]
  exact (congrArg JFp_SHADigest.digest address010).trans hash010
#print axioms root010
theorem shape010 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 16398=tree010 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 16398)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape006 f g inputs siblings]
  rw [unoccupied f g 0 16399 (by decide),siblings 0 (by decide) 16399 (by decide)]
  rfl
#print axioms shape010
def input011 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash011.message
def value011 : State := JFp_SHADigest.output JGy_Gr_M2.Hash011.result
theorem cast011_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash011.B00.input).map Fin.val=JGy_Gr_M2.Hash011.B00.input := by rfl
#print axioms cast011_0
theorem tail011 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash011.tail).map Fin.val=JGy_Gr_M2.Hash011.tail := by rfl
#print axioms tail011
theorem numeric011 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash011.message).map Fin.val=JGy_Gr_M2.Hash011.message := by
  simp only [JGy_Gr_M2.Hash011.message,JGy_Gr_M2.Hash011.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast011_0,tail011]
#print axioms numeric011
theorem hash011 : JFp_SHADigest.digest input011=value011 := by
  unfold input011 JFp_SHADigest.digest
  rw [numeric011,JGy_Gr_M2.Hash011.checked]
  rfl
#print axioms hash011
theorem address011 : BinMerkle32Path.nodeInput (children value000 (JGc_TX2_HashBytes.state [157,250,64,85,13,19,77,148,29,212,154,20,167,121,250,170,228,41,109,0,8,18,69,253,189,146,93,22,157,14,22,87]))=input011 := by rfl
#print axioms address011
def tree011 : Tree := .branch tree000 (.supplied (JGc_TX2_HashBytes.state [157,250,64,85,13,19,77,148,29,212,154,20,167,121,250,170,228,41,109,0,8,18,69,253,189,146,93,22,157,14,22,87]))
theorem root011 : root JFp_SHADigest.digest tree011=value011 := by
  rw [tree011,root,root000]
  exact (congrArg JFp_SHADigest.digest address011).trans hash011
#print axioms root011
theorem shape011 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 23374=tree011 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 23374)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape000 f g inputs siblings]
  rw [unoccupied f g 0 23375 (by decide),siblings 0 (by decide) 23375 (by decide)]
  rfl
#print axioms shape011
def input012 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash012.message
def value012 : State := JFp_SHADigest.output JGy_Gr_M2.Hash012.result
theorem cast012_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash012.B00.input).map Fin.val=JGy_Gr_M2.Hash012.B00.input := by rfl
#print axioms cast012_0
theorem tail012 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash012.tail).map Fin.val=JGy_Gr_M2.Hash012.tail := by rfl
#print axioms tail012
theorem numeric012 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash012.message).map Fin.val=JGy_Gr_M2.Hash012.message := by
  simp only [JGy_Gr_M2.Hash012.message,JGy_Gr_M2.Hash012.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast012_0,tail012]
#print axioms numeric012
theorem hash012 : JFp_SHADigest.digest input012=value012 := by
  unfold input012 JFp_SHADigest.digest
  rw [numeric012,JGy_Gr_M2.Hash012.checked]
  rfl
#print axioms hash012
theorem address012 : BinMerkle32Path.nodeInput (children value001 (JGc_TX2_HashBytes.state [200,118,125,216,76,197,168,252,66,166,175,172,159,132,202,150,238,183,109,182,215,230,204,48,38,187,56,127,4,148,156,91]))=input012 := by rfl
#print axioms address012
def tree012 : Tree := .branch tree001 (.supplied (JGc_TX2_HashBytes.state [200,118,125,216,76,197,168,252,66,166,175,172,159,132,202,150,238,183,109,182,215,230,204,48,38,187,56,127,4,148,156,91]))
theorem root012 : root JFp_SHADigest.digest tree012=value012 := by
  rw [tree012,root,root001]
  exact (congrArg JFp_SHADigest.digest address012).trans hash012
#print axioms root012
theorem shape012 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 36882=tree012 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 36882)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape001 f g inputs siblings]
  rw [unoccupied f g 0 36883 (by decide),siblings 0 (by decide) 36883 (by decide)]
  rfl
#print axioms shape012
def input013 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash013.message
def value013 : State := JFp_SHADigest.output JGy_Gr_M2.Hash013.result
theorem cast013_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash013.B00.input).map Fin.val=JGy_Gr_M2.Hash013.B00.input := by rfl
#print axioms cast013_0
theorem tail013 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash013.tail).map Fin.val=JGy_Gr_M2.Hash013.tail := by rfl
#print axioms tail013
theorem numeric013 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash013.message).map Fin.val=JGy_Gr_M2.Hash013.message := by
  simp only [JGy_Gr_M2.Hash013.message,JGy_Gr_M2.Hash013.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast013_0,tail013]
#print axioms numeric013
theorem hash013 : JFp_SHADigest.digest input013=value013 := by
  unfold input013 JFp_SHADigest.digest
  rw [numeric013,JGy_Gr_M2.Hash013.checked]
  rfl
#print axioms hash013
theorem address013 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [212,242,126,73,163,36,230,105,69,72,183,184,38,238,26,19,12,17,111,26,165,123,45,242,32,167,200,96,233,228,57,69]) value009)=input013 := by rfl
#print axioms address013
def tree013 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [212,242,126,73,163,36,230,105,69,72,183,184,38,238,26,19,12,17,111,26,165,123,45,242,32,167,200,96,233,228,57,69])) tree009
theorem root013 : root JFp_SHADigest.digest tree013=value013 := by
  rw [tree013,root,root009]
  exact (congrArg JFp_SHADigest.digest address013).trans hash013
#print axioms root013
theorem shape013 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 39952=tree013 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 39952)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 39952 (by decide),siblings 0 (by decide) 39952 (by decide)]
  rw [shape009 f g inputs siblings]
  rfl
#print axioms shape013
def input014 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash014.message
def value014 : State := JFp_SHADigest.output JGy_Gr_M2.Hash014.result
theorem cast014_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash014.B00.input).map Fin.val=JGy_Gr_M2.Hash014.B00.input := by rfl
#print axioms cast014_0
theorem tail014 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash014.tail).map Fin.val=JGy_Gr_M2.Hash014.tail := by rfl
#print axioms tail014
theorem numeric014 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash014.message).map Fin.val=JGy_Gr_M2.Hash014.message := by
  simp only [JGy_Gr_M2.Hash014.message,JGy_Gr_M2.Hash014.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast014_0,tail014]
#print axioms numeric014
theorem hash014 : JFp_SHADigest.digest input014=value014 := by
  unfold input014 JFp_SHADigest.digest
  rw [numeric014,JGy_Gr_M2.Hash014.checked]
  rfl
#print axioms hash014
theorem address014 : BinMerkle32Path.nodeInput (children value007 (JGc_TX2_HashBytes.state [82,191,91,24,205,192,231,67,121,98,110,223,12,88,203,10,225,19,214,220,215,156,248,27,81,185,96,114,168,9,78,14]))=input014 := by rfl
#print axioms address014
def tree014 : Tree := .branch tree007 (.supplied (JGc_TX2_HashBytes.state [82,191,91,24,205,192,231,67,121,98,110,223,12,88,203,10,225,19,214,220,215,156,248,27,81,185,96,114,168,9,78,14]))
theorem root014 : root JFp_SHADigest.digest tree014=value014 := by
  rw [tree014,root,root007]
  exact (congrArg JFp_SHADigest.digest address014).trans hash014
#print axioms root014
theorem shape014 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 45964=tree014 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 45964)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape007 f g inputs siblings]
  rw [unoccupied f g 0 45965 (by decide),siblings 0 (by decide) 45965 (by decide)]
  rfl
#print axioms shape014
def input015 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash015.message
def value015 : State := JFp_SHADigest.output JGy_Gr_M2.Hash015.result
theorem cast015_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash015.B00.input).map Fin.val=JGy_Gr_M2.Hash015.B00.input := by rfl
#print axioms cast015_0
theorem tail015 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash015.tail).map Fin.val=JGy_Gr_M2.Hash015.tail := by rfl
#print axioms tail015
theorem numeric015 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash015.message).map Fin.val=JGy_Gr_M2.Hash015.message := by
  simp only [JGy_Gr_M2.Hash015.message,JGy_Gr_M2.Hash015.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast015_0,tail015]
#print axioms numeric015
theorem hash015 : JFp_SHADigest.digest input015=value015 := by
  unfold input015 JFp_SHADigest.digest
  rw [numeric015,JGy_Gr_M2.Hash015.checked]
  rfl
#print axioms hash015
theorem address015 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [133,193,193,242,18,135,93,234,189,30,36,64,27,220,184,7,144,101,221,10,71,70,1,222,233,39,21,21,157,144,185,165]) value005)=input015 := by rfl
#print axioms address015
def tree015 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [133,193,193,242,18,135,93,234,189,30,36,64,27,220,184,7,144,101,221,10,71,70,1,222,233,39,21,21,157,144,185,165])) tree005
theorem root015 : root JFp_SHADigest.digest tree015=value015 := by
  rw [tree015,root,root005]
  exact (congrArg JFp_SHADigest.digest address015).trans hash015
#print axioms root015
theorem shape015 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 48078=tree015 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 48078)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 48078 (by decide),siblings 0 (by decide) 48078 (by decide)]
  rw [shape005 f g inputs siblings]
  rfl
#print axioms shape015
def input016 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash016.message
def value016 : State := JFp_SHADigest.output JGy_Gr_M2.Hash016.result
theorem cast016_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash016.B00.input).map Fin.val=JGy_Gr_M2.Hash016.B00.input := by rfl
#print axioms cast016_0
theorem tail016 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash016.tail).map Fin.val=JGy_Gr_M2.Hash016.tail := by rfl
#print axioms tail016
theorem numeric016 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash016.message).map Fin.val=JGy_Gr_M2.Hash016.message := by
  simp only [JGy_Gr_M2.Hash016.message,JGy_Gr_M2.Hash016.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast016_0,tail016]
#print axioms numeric016
theorem hash016 : JFp_SHADigest.digest input016=value016 := by
  unfold input016 JFp_SHADigest.digest
  rw [numeric016,JGy_Gr_M2.Hash016.checked]
  rfl
#print axioms hash016
theorem address016 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [98,207,122,12,13,116,247,26,12,101,199,43,169,75,183,42,84,151,241,175,190,14,219,79,255,20,41,230,147,83,213,218]) value008)=input016 := by rfl
#print axioms address016
def tree016 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [98,207,122,12,13,116,247,26,12,101,199,43,169,75,183,42,84,151,241,175,190,14,219,79,255,20,41,230,147,83,213,218])) tree008
theorem root016 : root JFp_SHADigest.digest tree016=value016 := by
  rw [tree016,root,root008]
  exact (congrArg JFp_SHADigest.digest address016).trans hash016
#print axioms root016
theorem shape016 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 48272=tree016 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 48272)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 48272 (by decide),siblings 0 (by decide) 48272 (by decide)]
  rw [shape008 f g inputs siblings]
  rfl
#print axioms shape016
def input017 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash017.message
def value017 : State := JFp_SHADigest.output JGy_Gr_M2.Hash017.result
theorem cast017_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash017.B00.input).map Fin.val=JGy_Gr_M2.Hash017.B00.input := by rfl
#print axioms cast017_0
theorem tail017 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash017.tail).map Fin.val=JGy_Gr_M2.Hash017.tail := by rfl
#print axioms tail017
theorem numeric017 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash017.message).map Fin.val=JGy_Gr_M2.Hash017.message := by
  simp only [JGy_Gr_M2.Hash017.message,JGy_Gr_M2.Hash017.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast017_0,tail017]
#print axioms numeric017
theorem hash017 : JFp_SHADigest.digest input017=value017 := by
  unfold input017 JFp_SHADigest.digest
  rw [numeric017,JGy_Gr_M2.Hash017.checked]
  rfl
#print axioms hash017
theorem address017 : BinMerkle32Path.nodeInput (children value004 (JGc_TX2_HashBytes.state [80,151,219,68,228,150,38,180,212,171,144,75,12,109,31,147,55,20,109,143,198,101,8,244,28,178,249,159,227,18,96,225]))=input017 := by rfl
#print axioms address017
def tree017 : Tree := .branch tree004 (.supplied (JGc_TX2_HashBytes.state [80,151,219,68,228,150,38,180,212,171,144,75,12,109,31,147,55,20,109,143,198,101,8,244,28,178,249,159,227,18,96,225]))
theorem root017 : root JFp_SHADigest.digest tree017=value017 := by
  rw [tree017,root,root004]
  exact (congrArg JFp_SHADigest.digest address017).trans hash017
#print axioms root017
theorem shape017 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 52342=tree017 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 52342)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape004 f g inputs siblings]
  rw [unoccupied f g 0 52343 (by decide),siblings 0 (by decide) 52343 (by decide)]
  rfl
#print axioms shape017
def input018 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash018.message
def value018 : State := JFp_SHADigest.output JGy_Gr_M2.Hash018.result
theorem cast018_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash018.B00.input).map Fin.val=JGy_Gr_M2.Hash018.B00.input := by rfl
#print axioms cast018_0
theorem tail018 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash018.tail).map Fin.val=JGy_Gr_M2.Hash018.tail := by rfl
#print axioms tail018
theorem numeric018 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash018.message).map Fin.val=JGy_Gr_M2.Hash018.message := by
  simp only [JGy_Gr_M2.Hash018.message,JGy_Gr_M2.Hash018.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast018_0,tail018]
#print axioms numeric018
theorem hash018 : JFp_SHADigest.digest input018=value018 := by
  unfold input018 JFp_SHADigest.digest
  rw [numeric018,JGy_Gr_M2.Hash018.checked]
  rfl
#print axioms hash018
theorem address018 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [52,8,95,13,105,245,56,139,100,239,201,233,12,0,102,84,64,208,206,160,240,46,2,104,110,111,39,205,28,111,190,253]) value002)=input018 := by rfl
#print axioms address018
def tree018 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [52,8,95,13,105,245,56,139,100,239,201,233,12,0,102,84,64,208,206,160,240,46,2,104,110,111,39,205,28,111,190,253])) tree002
theorem root018 : root JFp_SHADigest.digest tree018=value018 := by
  rw [tree018,root,root002]
  exact (congrArg JFp_SHADigest.digest address018).trans hash018
#print axioms root018
theorem shape018 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 54204=tree018 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 54204)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 54204 (by decide),siblings 0 (by decide) 54204 (by decide)]
  rw [shape002 f g inputs siblings]
  rfl
#print axioms shape018
def input019 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash019.message
def value019 : State := JFp_SHADigest.output JGy_Gr_M2.Hash019.result
theorem cast019_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash019.B00.input).map Fin.val=JGy_Gr_M2.Hash019.B00.input := by rfl
#print axioms cast019_0
theorem tail019 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash019.tail).map Fin.val=JGy_Gr_M2.Hash019.tail := by rfl
#print axioms tail019
theorem numeric019 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash019.message).map Fin.val=JGy_Gr_M2.Hash019.message := by
  simp only [JGy_Gr_M2.Hash019.message,JGy_Gr_M2.Hash019.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast019_0,tail019]
#print axioms numeric019
theorem hash019 : JFp_SHADigest.digest input019=value019 := by
  unfold input019 JFp_SHADigest.digest
  rw [numeric019,JGy_Gr_M2.Hash019.checked]
  rfl
#print axioms hash019
theorem address019 : BinMerkle32Path.nodeInput (children value003 (JGc_TX2_HashBytes.state [58,245,80,88,37,211,128,187,23,227,240,163,220,232,101,152,153,152,109,88,252,196,25,246,154,119,211,100,33,86,172,156]))=input019 := by rfl
#print axioms address019
def tree019 : Tree := .branch tree003 (.supplied (JGc_TX2_HashBytes.state [58,245,80,88,37,211,128,187,23,227,240,163,220,232,101,152,153,152,109,88,252,196,25,246,154,119,211,100,33,86,172,156]))
theorem root019 : root JFp_SHADigest.digest tree019=value019 := by
  rw [tree019,root,root003]
  exact (congrArg JFp_SHADigest.digest address019).trans hash019
#print axioms root019
theorem shape019 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 61474=tree019 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 61474)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape003 f g inputs siblings]
  rw [unoccupied f g 0 61475 (by decide),siblings 0 (by decide) 61475 (by decide)]
  rfl
#print axioms shape019
end AspisR1.JGy_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input020 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash020.message
def value020 : State := JFp_SHADigest.output JGy_Gr_M2.Hash020.result
theorem cast020_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash020.B00.input).map Fin.val=JGy_Gr_M2.Hash020.B00.input := by rfl
#print axioms cast020_0
theorem tail020 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash020.tail).map Fin.val=JGy_Gr_M2.Hash020.tail := by rfl
#print axioms tail020
theorem numeric020 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash020.message).map Fin.val=JGy_Gr_M2.Hash020.message := by
  simp only [JGy_Gr_M2.Hash020.message,JGy_Gr_M2.Hash020.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast020_0,tail020]
#print axioms numeric020
theorem hash020 : JFp_SHADigest.digest input020=value020 := by
  unfold input020 JFp_SHADigest.digest
  rw [numeric020,JGy_Gr_M2.Hash020.checked]
  rfl
#print axioms hash020
theorem address020 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [179,57,66,105,91,88,148,117,98,202,23,143,65,232,228,202,11,120,180,169,158,103,229,95,32,200,194,222,112,210,131,3]) value010)=input020 := by rfl
#print axioms address020
def tree020 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [179,57,66,105,91,88,148,117,98,202,23,143,65,232,228,202,11,120,180,169,158,103,229,95,32,200,194,222,112,210,131,3])) tree010
theorem root020 : root JFp_SHADigest.digest tree020=value020 := by
  rw [tree020,root,root010]
  exact (congrArg JFp_SHADigest.digest address020).trans hash020
#print axioms root020
theorem shape020 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 16396=tree020 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 16396)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 16396 (by decide),siblings 1 (by decide) 16396 (by decide)]
  rw [shape010 f g inputs siblings]
  rfl
#print axioms shape020
def input021 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash021.message
def value021 : State := JFp_SHADigest.output JGy_Gr_M2.Hash021.result
theorem cast021_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash021.B00.input).map Fin.val=JGy_Gr_M2.Hash021.B00.input := by rfl
#print axioms cast021_0
theorem tail021 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash021.tail).map Fin.val=JGy_Gr_M2.Hash021.tail := by rfl
#print axioms tail021
theorem numeric021 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash021.message).map Fin.val=JGy_Gr_M2.Hash021.message := by
  simp only [JGy_Gr_M2.Hash021.message,JGy_Gr_M2.Hash021.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast021_0,tail021]
#print axioms numeric021
theorem hash021 : JFp_SHADigest.digest input021=value021 := by
  unfold input021 JFp_SHADigest.digest
  rw [numeric021,JGy_Gr_M2.Hash021.checked]
  rfl
#print axioms hash021
theorem address021 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [107,125,164,219,26,17,227,219,9,238,70,117,237,24,14,190,244,82,156,147,101,254,180,116,45,28,98,62,32,57,198,231]) value011)=input021 := by rfl
#print axioms address021
def tree021 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [107,125,164,219,26,17,227,219,9,238,70,117,237,24,14,190,244,82,156,147,101,254,180,116,45,28,98,62,32,57,198,231])) tree011
theorem root021 : root JFp_SHADigest.digest tree021=value021 := by
  rw [tree021,root,root011]
  exact (congrArg JFp_SHADigest.digest address021).trans hash021
#print axioms root021
theorem shape021 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 23372=tree021 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 23372)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 23372 (by decide),siblings 1 (by decide) 23372 (by decide)]
  rw [shape011 f g inputs siblings]
  rfl
#print axioms shape021
def input022 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash022.message
def value022 : State := JFp_SHADigest.output JGy_Gr_M2.Hash022.result
theorem cast022_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash022.B00.input).map Fin.val=JGy_Gr_M2.Hash022.B00.input := by rfl
#print axioms cast022_0
theorem tail022 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash022.tail).map Fin.val=JGy_Gr_M2.Hash022.tail := by rfl
#print axioms tail022
theorem numeric022 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash022.message).map Fin.val=JGy_Gr_M2.Hash022.message := by
  simp only [JGy_Gr_M2.Hash022.message,JGy_Gr_M2.Hash022.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast022_0,tail022]
#print axioms numeric022
theorem hash022 : JFp_SHADigest.digest input022=value022 := by
  unfold input022 JFp_SHADigest.digest
  rw [numeric022,JGy_Gr_M2.Hash022.checked]
  rfl
#print axioms hash022
theorem address022 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [47,141,216,252,197,166,70,210,81,178,177,38,252,245,63,138,90,15,229,137,148,184,253,55,25,241,20,143,57,249,114,136]) value012)=input022 := by rfl
#print axioms address022
def tree022 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [47,141,216,252,197,166,70,210,81,178,177,38,252,245,63,138,90,15,229,137,148,184,253,55,25,241,20,143,57,249,114,136])) tree012
theorem root022 : root JFp_SHADigest.digest tree022=value022 := by
  rw [tree022,root,root012]
  exact (congrArg JFp_SHADigest.digest address022).trans hash022
#print axioms root022
theorem shape022 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 36880=tree022 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 36880)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 36880 (by decide),siblings 1 (by decide) 36880 (by decide)]
  rw [shape012 f g inputs siblings]
  rfl
#print axioms shape022
def input023 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash023.message
def value023 : State := JFp_SHADigest.output JGy_Gr_M2.Hash023.result
theorem cast023_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash023.B00.input).map Fin.val=JGy_Gr_M2.Hash023.B00.input := by rfl
#print axioms cast023_0
theorem tail023 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash023.tail).map Fin.val=JGy_Gr_M2.Hash023.tail := by rfl
#print axioms tail023
theorem numeric023 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash023.message).map Fin.val=JGy_Gr_M2.Hash023.message := by
  simp only [JGy_Gr_M2.Hash023.message,JGy_Gr_M2.Hash023.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast023_0,tail023]
#print axioms numeric023
theorem hash023 : JFp_SHADigest.digest input023=value023 := by
  unfold input023 JFp_SHADigest.digest
  rw [numeric023,JGy_Gr_M2.Hash023.checked]
  rfl
#print axioms hash023
theorem address023 : BinMerkle32Path.nodeInput (children value013 (JGc_TX2_HashBytes.state [149,82,100,53,22,189,226,92,234,12,68,130,93,161,194,244,133,5,197,140,65,188,52,164,91,170,182,75,33,104,183,190]))=input023 := by rfl
#print axioms address023
def tree023 : Tree := .branch tree013 (.supplied (JGc_TX2_HashBytes.state [149,82,100,53,22,189,226,92,234,12,68,130,93,161,194,244,133,5,197,140,65,188,52,164,91,170,182,75,33,104,183,190]))
theorem root023 : root JFp_SHADigest.digest tree023=value023 := by
  rw [tree023,root,root013]
  exact (congrArg JFp_SHADigest.digest address023).trans hash023
#print axioms root023
theorem shape023 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 39952=tree023 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 39952)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape013 f g inputs siblings]
  rw [unoccupied f g 1 39954 (by decide),siblings 1 (by decide) 39954 (by decide)]
  rfl
#print axioms shape023
def input024 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash024.message
def value024 : State := JFp_SHADigest.output JGy_Gr_M2.Hash024.result
theorem cast024_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash024.B00.input).map Fin.val=JGy_Gr_M2.Hash024.B00.input := by rfl
#print axioms cast024_0
theorem tail024 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash024.tail).map Fin.val=JGy_Gr_M2.Hash024.tail := by rfl
#print axioms tail024
theorem numeric024 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash024.message).map Fin.val=JGy_Gr_M2.Hash024.message := by
  simp only [JGy_Gr_M2.Hash024.message,JGy_Gr_M2.Hash024.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast024_0,tail024]
#print axioms numeric024
theorem hash024 : JFp_SHADigest.digest input024=value024 := by
  unfold input024 JFp_SHADigest.digest
  rw [numeric024,JGy_Gr_M2.Hash024.checked]
  rfl
#print axioms hash024
theorem address024 : BinMerkle32Path.nodeInput (children value014 (JGc_TX2_HashBytes.state [153,116,202,141,139,28,14,167,146,44,161,154,154,150,133,164,1,97,251,129,67,238,209,205,47,38,121,56,63,172,240,59]))=input024 := by rfl
#print axioms address024
def tree024 : Tree := .branch tree014 (.supplied (JGc_TX2_HashBytes.state [153,116,202,141,139,28,14,167,146,44,161,154,154,150,133,164,1,97,251,129,67,238,209,205,47,38,121,56,63,172,240,59]))
theorem root024 : root JFp_SHADigest.digest tree024=value024 := by
  rw [tree024,root,root014]
  exact (congrArg JFp_SHADigest.digest address024).trans hash024
#print axioms root024
theorem shape024 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 45964=tree024 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 45964)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape014 f g inputs siblings]
  rw [unoccupied f g 1 45966 (by decide),siblings 1 (by decide) 45966 (by decide)]
  rfl
#print axioms shape024
def input025 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash025.message
def value025 : State := JFp_SHADigest.output JGy_Gr_M2.Hash025.result
theorem cast025_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash025.B00.input).map Fin.val=JGy_Gr_M2.Hash025.B00.input := by rfl
#print axioms cast025_0
theorem tail025 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash025.tail).map Fin.val=JGy_Gr_M2.Hash025.tail := by rfl
#print axioms tail025
theorem numeric025 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash025.message).map Fin.val=JGy_Gr_M2.Hash025.message := by
  simp only [JGy_Gr_M2.Hash025.message,JGy_Gr_M2.Hash025.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast025_0,tail025]
#print axioms numeric025
theorem hash025 : JFp_SHADigest.digest input025=value025 := by
  unfold input025 JFp_SHADigest.digest
  rw [numeric025,JGy_Gr_M2.Hash025.checked]
  rfl
#print axioms hash025
theorem address025 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [59,32,195,3,19,154,209,61,43,191,156,113,54,238,181,159,13,241,5,114,216,99,9,206,156,21,132,19,133,169,28,149]) value015)=input025 := by rfl
#print axioms address025
def tree025 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [59,32,195,3,19,154,209,61,43,191,156,113,54,238,181,159,13,241,5,114,216,99,9,206,156,21,132,19,133,169,28,149])) tree015
theorem root025 : root JFp_SHADigest.digest tree025=value025 := by
  rw [tree025,root,root015]
  exact (congrArg JFp_SHADigest.digest address025).trans hash025
#print axioms root025
theorem shape025 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 48076=tree025 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 48076)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 48076 (by decide),siblings 1 (by decide) 48076 (by decide)]
  rw [shape015 f g inputs siblings]
  rfl
#print axioms shape025
def input026 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash026.message
def value026 : State := JFp_SHADigest.output JGy_Gr_M2.Hash026.result
theorem cast026_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash026.B00.input).map Fin.val=JGy_Gr_M2.Hash026.B00.input := by rfl
#print axioms cast026_0
theorem tail026 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash026.tail).map Fin.val=JGy_Gr_M2.Hash026.tail := by rfl
#print axioms tail026
theorem numeric026 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash026.message).map Fin.val=JGy_Gr_M2.Hash026.message := by
  simp only [JGy_Gr_M2.Hash026.message,JGy_Gr_M2.Hash026.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast026_0,tail026]
#print axioms numeric026
theorem hash026 : JFp_SHADigest.digest input026=value026 := by
  unfold input026 JFp_SHADigest.digest
  rw [numeric026,JGy_Gr_M2.Hash026.checked]
  rfl
#print axioms hash026
theorem address026 : BinMerkle32Path.nodeInput (children value016 (JGc_TX2_HashBytes.state [160,150,74,176,230,87,55,149,137,239,129,40,128,128,155,164,228,20,84,10,90,170,136,112,178,54,174,236,18,211,106,20]))=input026 := by rfl
#print axioms address026
def tree026 : Tree := .branch tree016 (.supplied (JGc_TX2_HashBytes.state [160,150,74,176,230,87,55,149,137,239,129,40,128,128,155,164,228,20,84,10,90,170,136,112,178,54,174,236,18,211,106,20]))
theorem root026 : root JFp_SHADigest.digest tree026=value026 := by
  rw [tree026,root,root016]
  exact (congrArg JFp_SHADigest.digest address026).trans hash026
#print axioms root026
theorem shape026 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 48272=tree026 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 48272)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape016 f g inputs siblings]
  rw [unoccupied f g 1 48274 (by decide),siblings 1 (by decide) 48274 (by decide)]
  rfl
#print axioms shape026
def input027 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash027.message
def value027 : State := JFp_SHADigest.output JGy_Gr_M2.Hash027.result
theorem cast027_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash027.B00.input).map Fin.val=JGy_Gr_M2.Hash027.B00.input := by rfl
#print axioms cast027_0
theorem tail027 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash027.tail).map Fin.val=JGy_Gr_M2.Hash027.tail := by rfl
#print axioms tail027
theorem numeric027 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash027.message).map Fin.val=JGy_Gr_M2.Hash027.message := by
  simp only [JGy_Gr_M2.Hash027.message,JGy_Gr_M2.Hash027.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast027_0,tail027]
#print axioms numeric027
theorem hash027 : JFp_SHADigest.digest input027=value027 := by
  unfold input027 JFp_SHADigest.digest
  rw [numeric027,JGy_Gr_M2.Hash027.checked]
  rfl
#print axioms hash027
theorem address027 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [228,12,216,182,13,245,17,244,56,172,67,209,165,228,216,245,36,207,219,252,76,56,80,233,32,172,129,152,94,206,186,32]) value017)=input027 := by rfl
#print axioms address027
def tree027 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [228,12,216,182,13,245,17,244,56,172,67,209,165,228,216,245,36,207,219,252,76,56,80,233,32,172,129,152,94,206,186,32])) tree017
theorem root027 : root JFp_SHADigest.digest tree027=value027 := by
  rw [tree027,root,root017]
  exact (congrArg JFp_SHADigest.digest address027).trans hash027
#print axioms root027
theorem shape027 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 52340=tree027 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 52340)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 52340 (by decide),siblings 1 (by decide) 52340 (by decide)]
  rw [shape017 f g inputs siblings]
  rfl
#print axioms shape027
def input028 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash028.message
def value028 : State := JFp_SHADigest.output JGy_Gr_M2.Hash028.result
theorem cast028_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash028.B00.input).map Fin.val=JGy_Gr_M2.Hash028.B00.input := by rfl
#print axioms cast028_0
theorem tail028 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash028.tail).map Fin.val=JGy_Gr_M2.Hash028.tail := by rfl
#print axioms tail028
theorem numeric028 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash028.message).map Fin.val=JGy_Gr_M2.Hash028.message := by
  simp only [JGy_Gr_M2.Hash028.message,JGy_Gr_M2.Hash028.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast028_0,tail028]
#print axioms numeric028
theorem hash028 : JFp_SHADigest.digest input028=value028 := by
  unfold input028 JFp_SHADigest.digest
  rw [numeric028,JGy_Gr_M2.Hash028.checked]
  rfl
#print axioms hash028
theorem address028 : BinMerkle32Path.nodeInput (children value018 (JGc_TX2_HashBytes.state [188,221,111,216,18,217,30,136,2,223,90,61,66,1,162,238,11,64,13,125,84,37,35,58,104,178,136,54,100,76,168,41]))=input028 := by rfl
#print axioms address028
def tree028 : Tree := .branch tree018 (.supplied (JGc_TX2_HashBytes.state [188,221,111,216,18,217,30,136,2,223,90,61,66,1,162,238,11,64,13,125,84,37,35,58,104,178,136,54,100,76,168,41]))
theorem root028 : root JFp_SHADigest.digest tree028=value028 := by
  rw [tree028,root,root018]
  exact (congrArg JFp_SHADigest.digest address028).trans hash028
#print axioms root028
theorem shape028 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 54204=tree028 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 54204)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape018 f g inputs siblings]
  rw [unoccupied f g 1 54206 (by decide),siblings 1 (by decide) 54206 (by decide)]
  rfl
#print axioms shape028
def input029 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash029.message
def value029 : State := JFp_SHADigest.output JGy_Gr_M2.Hash029.result
theorem cast029_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash029.B00.input).map Fin.val=JGy_Gr_M2.Hash029.B00.input := by rfl
#print axioms cast029_0
theorem tail029 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash029.tail).map Fin.val=JGy_Gr_M2.Hash029.tail := by rfl
#print axioms tail029
theorem numeric029 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash029.message).map Fin.val=JGy_Gr_M2.Hash029.message := by
  simp only [JGy_Gr_M2.Hash029.message,JGy_Gr_M2.Hash029.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast029_0,tail029]
#print axioms numeric029
theorem hash029 : JFp_SHADigest.digest input029=value029 := by
  unfold input029 JFp_SHADigest.digest
  rw [numeric029,JGy_Gr_M2.Hash029.checked]
  rfl
#print axioms hash029
theorem address029 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [41,72,84,86,132,77,231,158,173,214,235,170,124,62,85,192,227,36,17,210,21,206,189,190,89,89,69,162,196,143,89,105]) value019)=input029 := by rfl
#print axioms address029
def tree029 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [41,72,84,86,132,77,231,158,173,214,235,170,124,62,85,192,227,36,17,210,21,206,189,190,89,89,69,162,196,143,89,105])) tree019
theorem root029 : root JFp_SHADigest.digest tree029=value029 := by
  rw [tree029,root,root019]
  exact (congrArg JFp_SHADigest.digest address029).trans hash029
#print axioms root029
theorem shape029 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 2 61472=tree029 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 2 61472)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 1 61472 (by decide),siblings 1 (by decide) 61472 (by decide)]
  rw [shape019 f g inputs siblings]
  rfl
#print axioms shape029
end AspisR1.JGy_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input030 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash030.message
def value030 : State := JFp_SHADigest.output JGy_Gr_M2.Hash030.result
theorem cast030_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash030.B00.input).map Fin.val=JGy_Gr_M2.Hash030.B00.input := by rfl
#print axioms cast030_0
theorem tail030 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash030.tail).map Fin.val=JGy_Gr_M2.Hash030.tail := by rfl
#print axioms tail030
theorem numeric030 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash030.message).map Fin.val=JGy_Gr_M2.Hash030.message := by
  simp only [JGy_Gr_M2.Hash030.message,JGy_Gr_M2.Hash030.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast030_0,tail030]
#print axioms numeric030
theorem hash030 : JFp_SHADigest.digest input030=value030 := by
  unfold input030 JFp_SHADigest.digest
  rw [numeric030,JGy_Gr_M2.Hash030.checked]
  rfl
#print axioms hash030
theorem address030 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [194,245,184,247,117,235,145,13,126,50,69,25,98,255,22,215,181,195,177,122,110,168,180,137,116,143,124,181,73,28,5,69]) value020)=input030 := by rfl
#print axioms address030
def tree030 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [194,245,184,247,117,235,145,13,126,50,69,25,98,255,22,215,181,195,177,122,110,168,180,137,116,143,124,181,73,28,5,69])) tree020
theorem root030 : root JFp_SHADigest.digest tree030=value030 := by
  rw [tree030,root,root020]
  exact (congrArg JFp_SHADigest.digest address030).trans hash030
#print axioms root030
theorem shape030 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 16392=tree030 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 16392)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 16392 (by decide),siblings 2 (by decide) 16392 (by decide)]
  rw [shape020 f g inputs siblings]
  rfl
#print axioms shape030
def input031 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash031.message
def value031 : State := JFp_SHADigest.output JGy_Gr_M2.Hash031.result
theorem cast031_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash031.B00.input).map Fin.val=JGy_Gr_M2.Hash031.B00.input := by rfl
#print axioms cast031_0
theorem tail031 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash031.tail).map Fin.val=JGy_Gr_M2.Hash031.tail := by rfl
#print axioms tail031
theorem numeric031 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash031.message).map Fin.val=JGy_Gr_M2.Hash031.message := by
  simp only [JGy_Gr_M2.Hash031.message,JGy_Gr_M2.Hash031.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast031_0,tail031]
#print axioms numeric031
theorem hash031 : JFp_SHADigest.digest input031=value031 := by
  unfold input031 JFp_SHADigest.digest
  rw [numeric031,JGy_Gr_M2.Hash031.checked]
  rfl
#print axioms hash031
theorem address031 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [254,249,253,171,105,7,200,164,192,146,148,22,234,243,156,193,204,205,200,27,131,103,94,225,10,168,70,82,231,124,252,35]) value021)=input031 := by rfl
#print axioms address031
def tree031 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [254,249,253,171,105,7,200,164,192,146,148,22,234,243,156,193,204,205,200,27,131,103,94,225,10,168,70,82,231,124,252,35])) tree021
theorem root031 : root JFp_SHADigest.digest tree031=value031 := by
  rw [tree031,root,root021]
  exact (congrArg JFp_SHADigest.digest address031).trans hash031
#print axioms root031
theorem shape031 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 23368=tree031 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 23368)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 23368 (by decide),siblings 2 (by decide) 23368 (by decide)]
  rw [shape021 f g inputs siblings]
  rfl
#print axioms shape031
def input032 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash032.message
def value032 : State := JFp_SHADigest.output JGy_Gr_M2.Hash032.result
theorem cast032_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash032.B00.input).map Fin.val=JGy_Gr_M2.Hash032.B00.input := by rfl
#print axioms cast032_0
theorem tail032 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash032.tail).map Fin.val=JGy_Gr_M2.Hash032.tail := by rfl
#print axioms tail032
theorem numeric032 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash032.message).map Fin.val=JGy_Gr_M2.Hash032.message := by
  simp only [JGy_Gr_M2.Hash032.message,JGy_Gr_M2.Hash032.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast032_0,tail032]
#print axioms numeric032
theorem hash032 : JFp_SHADigest.digest input032=value032 := by
  unfold input032 JFp_SHADigest.digest
  rw [numeric032,JGy_Gr_M2.Hash032.checked]
  rfl
#print axioms hash032
theorem address032 : BinMerkle32Path.nodeInput (children value022 (JGc_TX2_HashBytes.state [186,93,169,162,221,9,97,47,195,23,151,178,51,170,82,124,130,6,105,43,70,227,136,131,203,240,135,148,160,124,113,200]))=input032 := by rfl
#print axioms address032
def tree032 : Tree := .branch tree022 (.supplied (JGc_TX2_HashBytes.state [186,93,169,162,221,9,97,47,195,23,151,178,51,170,82,124,130,6,105,43,70,227,136,131,203,240,135,148,160,124,113,200]))
theorem root032 : root JFp_SHADigest.digest tree032=value032 := by
  rw [tree032,root,root022]
  exact (congrArg JFp_SHADigest.digest address032).trans hash032
#print axioms root032
theorem shape032 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 36880=tree032 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 36880)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape022 f g inputs siblings]
  rw [unoccupied f g 2 36884 (by decide),siblings 2 (by decide) 36884 (by decide)]
  rfl
#print axioms shape032
def input033 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash033.message
def value033 : State := JFp_SHADigest.output JGy_Gr_M2.Hash033.result
theorem cast033_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash033.B00.input).map Fin.val=JGy_Gr_M2.Hash033.B00.input := by rfl
#print axioms cast033_0
theorem tail033 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash033.tail).map Fin.val=JGy_Gr_M2.Hash033.tail := by rfl
#print axioms tail033
theorem numeric033 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash033.message).map Fin.val=JGy_Gr_M2.Hash033.message := by
  simp only [JGy_Gr_M2.Hash033.message,JGy_Gr_M2.Hash033.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast033_0,tail033]
#print axioms numeric033
theorem hash033 : JFp_SHADigest.digest input033=value033 := by
  unfold input033 JFp_SHADigest.digest
  rw [numeric033,JGy_Gr_M2.Hash033.checked]
  rfl
#print axioms hash033
theorem address033 : BinMerkle32Path.nodeInput (children value023 (JGc_TX2_HashBytes.state [117,14,241,103,80,121,161,108,21,104,179,229,107,125,84,31,189,134,142,185,135,253,55,234,139,89,193,114,221,115,46,128]))=input033 := by rfl
#print axioms address033
def tree033 : Tree := .branch tree023 (.supplied (JGc_TX2_HashBytes.state [117,14,241,103,80,121,161,108,21,104,179,229,107,125,84,31,189,134,142,185,135,253,55,234,139,89,193,114,221,115,46,128]))
theorem root033 : root JFp_SHADigest.digest tree033=value033 := by
  rw [tree033,root,root023]
  exact (congrArg JFp_SHADigest.digest address033).trans hash033
#print axioms root033
theorem shape033 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 39952=tree033 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 39952)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape023 f g inputs siblings]
  rw [unoccupied f g 2 39956 (by decide),siblings 2 (by decide) 39956 (by decide)]
  rfl
#print axioms shape033
def input034 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash034.message
def value034 : State := JFp_SHADigest.output JGy_Gr_M2.Hash034.result
theorem cast034_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash034.B00.input).map Fin.val=JGy_Gr_M2.Hash034.B00.input := by rfl
#print axioms cast034_0
theorem tail034 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash034.tail).map Fin.val=JGy_Gr_M2.Hash034.tail := by rfl
#print axioms tail034
theorem numeric034 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash034.message).map Fin.val=JGy_Gr_M2.Hash034.message := by
  simp only [JGy_Gr_M2.Hash034.message,JGy_Gr_M2.Hash034.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast034_0,tail034]
#print axioms numeric034
theorem hash034 : JFp_SHADigest.digest input034=value034 := by
  unfold input034 JFp_SHADigest.digest
  rw [numeric034,JGy_Gr_M2.Hash034.checked]
  rfl
#print axioms hash034
theorem address034 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [252,199,160,112,92,68,47,54,9,188,58,105,45,11,24,100,63,52,109,70,105,61,240,30,194,73,210,110,30,137,146,5]) value024)=input034 := by rfl
#print axioms address034
def tree034 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [252,199,160,112,92,68,47,54,9,188,58,105,45,11,24,100,63,52,109,70,105,61,240,30,194,73,210,110,30,137,146,5])) tree024
theorem root034 : root JFp_SHADigest.digest tree034=value034 := by
  rw [tree034,root,root024]
  exact (congrArg JFp_SHADigest.digest address034).trans hash034
#print axioms root034
theorem shape034 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 45960=tree034 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 45960)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 45960 (by decide),siblings 2 (by decide) 45960 (by decide)]
  rw [shape024 f g inputs siblings]
  rfl
#print axioms shape034
def input035 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash035.message
def value035 : State := JFp_SHADigest.output JGy_Gr_M2.Hash035.result
theorem cast035_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash035.B00.input).map Fin.val=JGy_Gr_M2.Hash035.B00.input := by rfl
#print axioms cast035_0
theorem tail035 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash035.tail).map Fin.val=JGy_Gr_M2.Hash035.tail := by rfl
#print axioms tail035
theorem numeric035 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash035.message).map Fin.val=JGy_Gr_M2.Hash035.message := by
  simp only [JGy_Gr_M2.Hash035.message,JGy_Gr_M2.Hash035.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast035_0,tail035]
#print axioms numeric035
theorem hash035 : JFp_SHADigest.digest input035=value035 := by
  unfold input035 JFp_SHADigest.digest
  rw [numeric035,JGy_Gr_M2.Hash035.checked]
  rfl
#print axioms hash035
theorem address035 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [235,50,176,191,189,100,44,247,120,2,40,116,130,231,48,6,150,118,123,187,248,252,9,165,185,26,191,183,209,65,102,221]) value025)=input035 := by rfl
#print axioms address035
def tree035 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [235,50,176,191,189,100,44,247,120,2,40,116,130,231,48,6,150,118,123,187,248,252,9,165,185,26,191,183,209,65,102,221])) tree025
theorem root035 : root JFp_SHADigest.digest tree035=value035 := by
  rw [tree035,root,root025]
  exact (congrArg JFp_SHADigest.digest address035).trans hash035
#print axioms root035
theorem shape035 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 48072=tree035 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 48072)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 48072 (by decide),siblings 2 (by decide) 48072 (by decide)]
  rw [shape025 f g inputs siblings]
  rfl
#print axioms shape035
def input036 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash036.message
def value036 : State := JFp_SHADigest.output JGy_Gr_M2.Hash036.result
theorem cast036_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash036.B00.input).map Fin.val=JGy_Gr_M2.Hash036.B00.input := by rfl
#print axioms cast036_0
theorem tail036 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash036.tail).map Fin.val=JGy_Gr_M2.Hash036.tail := by rfl
#print axioms tail036
theorem numeric036 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash036.message).map Fin.val=JGy_Gr_M2.Hash036.message := by
  simp only [JGy_Gr_M2.Hash036.message,JGy_Gr_M2.Hash036.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast036_0,tail036]
#print axioms numeric036
theorem hash036 : JFp_SHADigest.digest input036=value036 := by
  unfold input036 JFp_SHADigest.digest
  rw [numeric036,JGy_Gr_M2.Hash036.checked]
  rfl
#print axioms hash036
theorem address036 : BinMerkle32Path.nodeInput (children value026 (JGc_TX2_HashBytes.state [220,245,95,204,173,38,219,209,33,203,132,173,44,78,7,132,64,185,24,223,162,215,156,66,211,174,245,196,96,216,230,66]))=input036 := by rfl
#print axioms address036
def tree036 : Tree := .branch tree026 (.supplied (JGc_TX2_HashBytes.state [220,245,95,204,173,38,219,209,33,203,132,173,44,78,7,132,64,185,24,223,162,215,156,66,211,174,245,196,96,216,230,66]))
theorem root036 : root JFp_SHADigest.digest tree036=value036 := by
  rw [tree036,root,root026]
  exact (congrArg JFp_SHADigest.digest address036).trans hash036
#print axioms root036
theorem shape036 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 48272=tree036 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 48272)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape026 f g inputs siblings]
  rw [unoccupied f g 2 48276 (by decide),siblings 2 (by decide) 48276 (by decide)]
  rfl
#print axioms shape036
def input037 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash037.message
def value037 : State := JFp_SHADigest.output JGy_Gr_M2.Hash037.result
theorem cast037_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash037.B00.input).map Fin.val=JGy_Gr_M2.Hash037.B00.input := by rfl
#print axioms cast037_0
theorem tail037 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash037.tail).map Fin.val=JGy_Gr_M2.Hash037.tail := by rfl
#print axioms tail037
theorem numeric037 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash037.message).map Fin.val=JGy_Gr_M2.Hash037.message := by
  simp only [JGy_Gr_M2.Hash037.message,JGy_Gr_M2.Hash037.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast037_0,tail037]
#print axioms numeric037
theorem hash037 : JFp_SHADigest.digest input037=value037 := by
  unfold input037 JFp_SHADigest.digest
  rw [numeric037,JGy_Gr_M2.Hash037.checked]
  rfl
#print axioms hash037
theorem address037 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [106,76,243,247,175,186,175,214,242,19,159,62,63,228,244,231,157,110,252,193,106,75,125,234,209,149,240,59,55,204,191,128]) value027)=input037 := by rfl
#print axioms address037
def tree037 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [106,76,243,247,175,186,175,214,242,19,159,62,63,228,244,231,157,110,252,193,106,75,125,234,209,149,240,59,55,204,191,128])) tree027
theorem root037 : root JFp_SHADigest.digest tree037=value037 := by
  rw [tree037,root,root027]
  exact (congrArg JFp_SHADigest.digest address037).trans hash037
#print axioms root037
theorem shape037 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 52336=tree037 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 52336)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 52336 (by decide),siblings 2 (by decide) 52336 (by decide)]
  rw [shape027 f g inputs siblings]
  rfl
#print axioms shape037
def input038 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash038.message
def value038 : State := JFp_SHADigest.output JGy_Gr_M2.Hash038.result
theorem cast038_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash038.B00.input).map Fin.val=JGy_Gr_M2.Hash038.B00.input := by rfl
#print axioms cast038_0
theorem tail038 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash038.tail).map Fin.val=JGy_Gr_M2.Hash038.tail := by rfl
#print axioms tail038
theorem numeric038 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash038.message).map Fin.val=JGy_Gr_M2.Hash038.message := by
  simp only [JGy_Gr_M2.Hash038.message,JGy_Gr_M2.Hash038.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast038_0,tail038]
#print axioms numeric038
theorem hash038 : JFp_SHADigest.digest input038=value038 := by
  unfold input038 JFp_SHADigest.digest
  rw [numeric038,JGy_Gr_M2.Hash038.checked]
  rfl
#print axioms hash038
theorem address038 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [236,64,23,201,253,208,86,58,10,82,89,203,137,84,53,121,112,94,44,47,16,0,83,247,169,8,40,153,151,170,22,238]) value028)=input038 := by rfl
#print axioms address038
def tree038 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [236,64,23,201,253,208,86,58,10,82,89,203,137,84,53,121,112,94,44,47,16,0,83,247,169,8,40,153,151,170,22,238])) tree028
theorem root038 : root JFp_SHADigest.digest tree038=value038 := by
  rw [tree038,root,root028]
  exact (congrArg JFp_SHADigest.digest address038).trans hash038
#print axioms root038
theorem shape038 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 54200=tree038 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 54200)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 2 54200 (by decide),siblings 2 (by decide) 54200 (by decide)]
  rw [shape028 f g inputs siblings]
  rfl
#print axioms shape038
def input039 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash039.message
def value039 : State := JFp_SHADigest.output JGy_Gr_M2.Hash039.result
theorem cast039_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash039.B00.input).map Fin.val=JGy_Gr_M2.Hash039.B00.input := by rfl
#print axioms cast039_0
theorem tail039 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash039.tail).map Fin.val=JGy_Gr_M2.Hash039.tail := by rfl
#print axioms tail039
theorem numeric039 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash039.message).map Fin.val=JGy_Gr_M2.Hash039.message := by
  simp only [JGy_Gr_M2.Hash039.message,JGy_Gr_M2.Hash039.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast039_0,tail039]
#print axioms numeric039
theorem hash039 : JFp_SHADigest.digest input039=value039 := by
  unfold input039 JFp_SHADigest.digest
  rw [numeric039,JGy_Gr_M2.Hash039.checked]
  rfl
#print axioms hash039
theorem address039 : BinMerkle32Path.nodeInput (children value029 (JGc_TX2_HashBytes.state [202,189,29,169,70,123,183,226,47,76,15,140,170,67,27,238,204,183,171,51,116,132,60,183,181,124,58,4,43,84,219,250]))=input039 := by rfl
#print axioms address039
def tree039 : Tree := .branch tree029 (.supplied (JGc_TX2_HashBytes.state [202,189,29,169,70,123,183,226,47,76,15,140,170,67,27,238,204,183,171,51,116,132,60,183,181,124,58,4,43,84,219,250]))
theorem root039 : root JFp_SHADigest.digest tree039=value039 := by
  rw [tree039,root,root029]
  exact (congrArg JFp_SHADigest.digest address039).trans hash039
#print axioms root039
theorem shape039 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 3 61472=tree039 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 3 61472)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape029 f g inputs siblings]
  rw [unoccupied f g 2 61476 (by decide),siblings 2 (by decide) 61476 (by decide)]
  rfl
#print axioms shape039
end AspisR1.JGy_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input040 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash040.message
def value040 : State := JFp_SHADigest.output JGy_Gr_M2.Hash040.result
theorem cast040_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash040.B00.input).map Fin.val=JGy_Gr_M2.Hash040.B00.input := by rfl
#print axioms cast040_0
theorem tail040 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash040.tail).map Fin.val=JGy_Gr_M2.Hash040.tail := by rfl
#print axioms tail040
theorem numeric040 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash040.message).map Fin.val=JGy_Gr_M2.Hash040.message := by
  simp only [JGy_Gr_M2.Hash040.message,JGy_Gr_M2.Hash040.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast040_0,tail040]
#print axioms numeric040
theorem hash040 : JFp_SHADigest.digest input040=value040 := by
  unfold input040 JFp_SHADigest.digest
  rw [numeric040,JGy_Gr_M2.Hash040.checked]
  rfl
#print axioms hash040
theorem address040 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [249,97,95,72,195,239,230,133,231,204,195,159,197,242,53,210,181,126,161,238,155,106,151,110,88,108,146,232,8,121,248,62]) value030)=input040 := by rfl
#print axioms address040
def tree040 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [249,97,95,72,195,239,230,133,231,204,195,159,197,242,53,210,181,126,161,238,155,106,151,110,88,108,146,232,8,121,248,62])) tree030
theorem root040 : root JFp_SHADigest.digest tree040=value040 := by
  rw [tree040,root,root030]
  exact (congrArg JFp_SHADigest.digest address040).trans hash040
#print axioms root040
theorem shape040 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 16384=tree040 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 16384)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 16384 (by decide),siblings 3 (by decide) 16384 (by decide)]
  rw [shape030 f g inputs siblings]
  rfl
#print axioms shape040
def input041 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash041.message
def value041 : State := JFp_SHADigest.output JGy_Gr_M2.Hash041.result
theorem cast041_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash041.B00.input).map Fin.val=JGy_Gr_M2.Hash041.B00.input := by rfl
#print axioms cast041_0
theorem tail041 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash041.tail).map Fin.val=JGy_Gr_M2.Hash041.tail := by rfl
#print axioms tail041
theorem numeric041 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash041.message).map Fin.val=JGy_Gr_M2.Hash041.message := by
  simp only [JGy_Gr_M2.Hash041.message,JGy_Gr_M2.Hash041.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast041_0,tail041]
#print axioms numeric041
theorem hash041 : JFp_SHADigest.digest input041=value041 := by
  unfold input041 JFp_SHADigest.digest
  rw [numeric041,JGy_Gr_M2.Hash041.checked]
  rfl
#print axioms hash041
theorem address041 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [179,62,84,67,145,245,19,145,0,76,183,216,254,164,78,100,235,197,149,22,181,176,111,192,90,35,170,224,190,165,169,130]) value031)=input041 := by rfl
#print axioms address041
def tree041 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [179,62,84,67,145,245,19,145,0,76,183,216,254,164,78,100,235,197,149,22,181,176,111,192,90,35,170,224,190,165,169,130])) tree031
theorem root041 : root JFp_SHADigest.digest tree041=value041 := by
  rw [tree041,root,root031]
  exact (congrArg JFp_SHADigest.digest address041).trans hash041
#print axioms root041
theorem shape041 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 23360=tree041 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 23360)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 23360 (by decide),siblings 3 (by decide) 23360 (by decide)]
  rw [shape031 f g inputs siblings]
  rfl
#print axioms shape041
def input042 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash042.message
def value042 : State := JFp_SHADigest.output JGy_Gr_M2.Hash042.result
theorem cast042_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash042.B00.input).map Fin.val=JGy_Gr_M2.Hash042.B00.input := by rfl
#print axioms cast042_0
theorem tail042 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash042.tail).map Fin.val=JGy_Gr_M2.Hash042.tail := by rfl
#print axioms tail042
theorem numeric042 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash042.message).map Fin.val=JGy_Gr_M2.Hash042.message := by
  simp only [JGy_Gr_M2.Hash042.message,JGy_Gr_M2.Hash042.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast042_0,tail042]
#print axioms numeric042
theorem hash042 : JFp_SHADigest.digest input042=value042 := by
  unfold input042 JFp_SHADigest.digest
  rw [numeric042,JGy_Gr_M2.Hash042.checked]
  rfl
#print axioms hash042
theorem address042 : BinMerkle32Path.nodeInput (children value032 (JGc_TX2_HashBytes.state [169,21,194,86,169,83,68,57,145,59,224,82,4,255,183,95,137,88,198,233,243,230,177,89,132,186,175,162,5,209,79,171]))=input042 := by rfl
#print axioms address042
def tree042 : Tree := .branch tree032 (.supplied (JGc_TX2_HashBytes.state [169,21,194,86,169,83,68,57,145,59,224,82,4,255,183,95,137,88,198,233,243,230,177,89,132,186,175,162,5,209,79,171]))
theorem root042 : root JFp_SHADigest.digest tree042=value042 := by
  rw [tree042,root,root032]
  exact (congrArg JFp_SHADigest.digest address042).trans hash042
#print axioms root042
theorem shape042 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 36880=tree042 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 36880)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape032 f g inputs siblings]
  rw [unoccupied f g 3 36888 (by decide),siblings 3 (by decide) 36888 (by decide)]
  rfl
#print axioms shape042
def input043 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash043.message
def value043 : State := JFp_SHADigest.output JGy_Gr_M2.Hash043.result
theorem cast043_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash043.B00.input).map Fin.val=JGy_Gr_M2.Hash043.B00.input := by rfl
#print axioms cast043_0
theorem tail043 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash043.tail).map Fin.val=JGy_Gr_M2.Hash043.tail := by rfl
#print axioms tail043
theorem numeric043 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash043.message).map Fin.val=JGy_Gr_M2.Hash043.message := by
  simp only [JGy_Gr_M2.Hash043.message,JGy_Gr_M2.Hash043.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast043_0,tail043]
#print axioms numeric043
theorem hash043 : JFp_SHADigest.digest input043=value043 := by
  unfold input043 JFp_SHADigest.digest
  rw [numeric043,JGy_Gr_M2.Hash043.checked]
  rfl
#print axioms hash043
theorem address043 : BinMerkle32Path.nodeInput (children value033 (JGc_TX2_HashBytes.state [249,125,104,173,124,225,131,121,245,201,10,19,165,30,103,92,67,162,190,80,0,142,172,114,183,72,182,186,237,7,60,125]))=input043 := by rfl
#print axioms address043
def tree043 : Tree := .branch tree033 (.supplied (JGc_TX2_HashBytes.state [249,125,104,173,124,225,131,121,245,201,10,19,165,30,103,92,67,162,190,80,0,142,172,114,183,72,182,186,237,7,60,125]))
theorem root043 : root JFp_SHADigest.digest tree043=value043 := by
  rw [tree043,root,root033]
  exact (congrArg JFp_SHADigest.digest address043).trans hash043
#print axioms root043
theorem shape043 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 39952=tree043 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 39952)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape033 f g inputs siblings]
  rw [unoccupied f g 3 39960 (by decide),siblings 3 (by decide) 39960 (by decide)]
  rfl
#print axioms shape043
def input044 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash044.message
def value044 : State := JFp_SHADigest.output JGy_Gr_M2.Hash044.result
theorem cast044_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash044.B00.input).map Fin.val=JGy_Gr_M2.Hash044.B00.input := by rfl
#print axioms cast044_0
theorem tail044 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash044.tail).map Fin.val=JGy_Gr_M2.Hash044.tail := by rfl
#print axioms tail044
theorem numeric044 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash044.message).map Fin.val=JGy_Gr_M2.Hash044.message := by
  simp only [JGy_Gr_M2.Hash044.message,JGy_Gr_M2.Hash044.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast044_0,tail044]
#print axioms numeric044
theorem hash044 : JFp_SHADigest.digest input044=value044 := by
  unfold input044 JFp_SHADigest.digest
  rw [numeric044,JGy_Gr_M2.Hash044.checked]
  rfl
#print axioms hash044
theorem address044 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [195,11,91,13,242,157,237,14,230,48,53,152,68,28,146,173,39,23,72,54,22,225,121,215,107,229,54,60,170,68,238,72]) value034)=input044 := by rfl
#print axioms address044
def tree044 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [195,11,91,13,242,157,237,14,230,48,53,152,68,28,146,173,39,23,72,54,22,225,121,215,107,229,54,60,170,68,238,72])) tree034
theorem root044 : root JFp_SHADigest.digest tree044=value044 := by
  rw [tree044,root,root034]
  exact (congrArg JFp_SHADigest.digest address044).trans hash044
#print axioms root044
theorem shape044 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 45952=tree044 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 45952)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 45952 (by decide),siblings 3 (by decide) 45952 (by decide)]
  rw [shape034 f g inputs siblings]
  rfl
#print axioms shape044
def input045 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash045.message
def value045 : State := JFp_SHADigest.output JGy_Gr_M2.Hash045.result
theorem cast045_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash045.B00.input).map Fin.val=JGy_Gr_M2.Hash045.B00.input := by rfl
#print axioms cast045_0
theorem tail045 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash045.tail).map Fin.val=JGy_Gr_M2.Hash045.tail := by rfl
#print axioms tail045
theorem numeric045 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash045.message).map Fin.val=JGy_Gr_M2.Hash045.message := by
  simp only [JGy_Gr_M2.Hash045.message,JGy_Gr_M2.Hash045.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast045_0,tail045]
#print axioms numeric045
theorem hash045 : JFp_SHADigest.digest input045=value045 := by
  unfold input045 JFp_SHADigest.digest
  rw [numeric045,JGy_Gr_M2.Hash045.checked]
  rfl
#print axioms hash045
theorem address045 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [179,112,196,108,44,160,62,125,194,38,29,185,108,215,4,140,11,246,68,159,82,31,45,80,100,31,239,92,243,120,250,219]) value035)=input045 := by rfl
#print axioms address045
def tree045 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [179,112,196,108,44,160,62,125,194,38,29,185,108,215,4,140,11,246,68,159,82,31,45,80,100,31,239,92,243,120,250,219])) tree035
theorem root045 : root JFp_SHADigest.digest tree045=value045 := by
  rw [tree045,root,root035]
  exact (congrArg JFp_SHADigest.digest address045).trans hash045
#print axioms root045
theorem shape045 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 48064=tree045 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 48064)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 48064 (by decide),siblings 3 (by decide) 48064 (by decide)]
  rw [shape035 f g inputs siblings]
  rfl
#print axioms shape045
def input046 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash046.message
def value046 : State := JFp_SHADigest.output JGy_Gr_M2.Hash046.result
theorem cast046_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash046.B00.input).map Fin.val=JGy_Gr_M2.Hash046.B00.input := by rfl
#print axioms cast046_0
theorem tail046 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash046.tail).map Fin.val=JGy_Gr_M2.Hash046.tail := by rfl
#print axioms tail046
theorem numeric046 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash046.message).map Fin.val=JGy_Gr_M2.Hash046.message := by
  simp only [JGy_Gr_M2.Hash046.message,JGy_Gr_M2.Hash046.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast046_0,tail046]
#print axioms numeric046
theorem hash046 : JFp_SHADigest.digest input046=value046 := by
  unfold input046 JFp_SHADigest.digest
  rw [numeric046,JGy_Gr_M2.Hash046.checked]
  rfl
#print axioms hash046
theorem address046 : BinMerkle32Path.nodeInput (children value036 (JGc_TX2_HashBytes.state [62,167,250,165,65,31,182,78,176,251,194,75,161,83,115,3,81,118,25,197,64,0,255,47,232,78,185,56,42,93,69,86]))=input046 := by rfl
#print axioms address046
def tree046 : Tree := .branch tree036 (.supplied (JGc_TX2_HashBytes.state [62,167,250,165,65,31,182,78,176,251,194,75,161,83,115,3,81,118,25,197,64,0,255,47,232,78,185,56,42,93,69,86]))
theorem root046 : root JFp_SHADigest.digest tree046=value046 := by
  rw [tree046,root,root036]
  exact (congrArg JFp_SHADigest.digest address046).trans hash046
#print axioms root046
theorem shape046 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 48272=tree046 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 48272)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape036 f g inputs siblings]
  rw [unoccupied f g 3 48280 (by decide),siblings 3 (by decide) 48280 (by decide)]
  rfl
#print axioms shape046
def input047 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash047.message
def value047 : State := JFp_SHADigest.output JGy_Gr_M2.Hash047.result
theorem cast047_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash047.B00.input).map Fin.val=JGy_Gr_M2.Hash047.B00.input := by rfl
#print axioms cast047_0
theorem tail047 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash047.tail).map Fin.val=JGy_Gr_M2.Hash047.tail := by rfl
#print axioms tail047
theorem numeric047 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash047.message).map Fin.val=JGy_Gr_M2.Hash047.message := by
  simp only [JGy_Gr_M2.Hash047.message,JGy_Gr_M2.Hash047.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast047_0,tail047]
#print axioms numeric047
theorem hash047 : JFp_SHADigest.digest input047=value047 := by
  unfold input047 JFp_SHADigest.digest
  rw [numeric047,JGy_Gr_M2.Hash047.checked]
  rfl
#print axioms hash047
theorem address047 : BinMerkle32Path.nodeInput (children value037 (JGc_TX2_HashBytes.state [57,54,77,49,101,42,95,108,7,193,128,156,160,108,172,205,176,94,234,119,178,60,14,61,107,83,83,99,46,128,55,36]))=input047 := by rfl
#print axioms address047
def tree047 : Tree := .branch tree037 (.supplied (JGc_TX2_HashBytes.state [57,54,77,49,101,42,95,108,7,193,128,156,160,108,172,205,176,94,234,119,178,60,14,61,107,83,83,99,46,128,55,36]))
theorem root047 : root JFp_SHADigest.digest tree047=value047 := by
  rw [tree047,root,root037]
  exact (congrArg JFp_SHADigest.digest address047).trans hash047
#print axioms root047
theorem shape047 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 52336=tree047 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 52336)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape037 f g inputs siblings]
  rw [unoccupied f g 3 52344 (by decide),siblings 3 (by decide) 52344 (by decide)]
  rfl
#print axioms shape047
def input048 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash048.message
def value048 : State := JFp_SHADigest.output JGy_Gr_M2.Hash048.result
theorem cast048_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash048.B00.input).map Fin.val=JGy_Gr_M2.Hash048.B00.input := by rfl
#print axioms cast048_0
theorem tail048 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash048.tail).map Fin.val=JGy_Gr_M2.Hash048.tail := by rfl
#print axioms tail048
theorem numeric048 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash048.message).map Fin.val=JGy_Gr_M2.Hash048.message := by
  simp only [JGy_Gr_M2.Hash048.message,JGy_Gr_M2.Hash048.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast048_0,tail048]
#print axioms numeric048
theorem hash048 : JFp_SHADigest.digest input048=value048 := by
  unfold input048 JFp_SHADigest.digest
  rw [numeric048,JGy_Gr_M2.Hash048.checked]
  rfl
#print axioms hash048
theorem address048 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [162,78,44,26,160,83,123,134,218,232,6,213,29,159,101,194,116,107,147,229,122,88,91,82,166,42,5,120,181,179,197,167]) value038)=input048 := by rfl
#print axioms address048
def tree048 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [162,78,44,26,160,83,123,134,218,232,6,213,29,159,101,194,116,107,147,229,122,88,91,82,166,42,5,120,181,179,197,167])) tree038
theorem root048 : root JFp_SHADigest.digest tree048=value048 := by
  rw [tree048,root,root038]
  exact (congrArg JFp_SHADigest.digest address048).trans hash048
#print axioms root048
theorem shape048 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 54192=tree048 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 54192)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 3 54192 (by decide),siblings 3 (by decide) 54192 (by decide)]
  rw [shape038 f g inputs siblings]
  rfl
#print axioms shape048
def input049 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash049.message
def value049 : State := JFp_SHADigest.output JGy_Gr_M2.Hash049.result
theorem cast049_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash049.B00.input).map Fin.val=JGy_Gr_M2.Hash049.B00.input := by rfl
#print axioms cast049_0
theorem tail049 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash049.tail).map Fin.val=JGy_Gr_M2.Hash049.tail := by rfl
#print axioms tail049
theorem numeric049 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash049.message).map Fin.val=JGy_Gr_M2.Hash049.message := by
  simp only [JGy_Gr_M2.Hash049.message,JGy_Gr_M2.Hash049.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast049_0,tail049]
#print axioms numeric049
theorem hash049 : JFp_SHADigest.digest input049=value049 := by
  unfold input049 JFp_SHADigest.digest
  rw [numeric049,JGy_Gr_M2.Hash049.checked]
  rfl
#print axioms hash049
theorem address049 : BinMerkle32Path.nodeInput (children value039 (JGc_TX2_HashBytes.state [16,233,214,196,219,235,118,177,214,211,77,23,126,52,140,234,128,247,206,133,105,180,135,29,2,2,189,128,41,90,9,193]))=input049 := by rfl
#print axioms address049
def tree049 : Tree := .branch tree039 (.supplied (JGc_TX2_HashBytes.state [16,233,214,196,219,235,118,177,214,211,77,23,126,52,140,234,128,247,206,133,105,180,135,29,2,2,189,128,41,90,9,193]))
theorem root049 : root JFp_SHADigest.digest tree049=value049 := by
  rw [tree049,root,root039]
  exact (congrArg JFp_SHADigest.digest address049).trans hash049
#print axioms root049
theorem shape049 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 4 61472=tree049 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 4 61472)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape039 f g inputs siblings]
  rw [unoccupied f g 3 61480 (by decide),siblings 3 (by decide) 61480 (by decide)]
  rfl
#print axioms shape049
end AspisR1.JGy_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input050 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash050.message
def value050 : State := JFp_SHADigest.output JGy_Gr_M2.Hash050.result
theorem cast050_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash050.B00.input).map Fin.val=JGy_Gr_M2.Hash050.B00.input := by rfl
#print axioms cast050_0
theorem tail050 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash050.tail).map Fin.val=JGy_Gr_M2.Hash050.tail := by rfl
#print axioms tail050
theorem numeric050 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash050.message).map Fin.val=JGy_Gr_M2.Hash050.message := by
  simp only [JGy_Gr_M2.Hash050.message,JGy_Gr_M2.Hash050.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast050_0,tail050]
#print axioms numeric050
theorem hash050 : JFp_SHADigest.digest input050=value050 := by
  unfold input050 JFp_SHADigest.digest
  rw [numeric050,JGy_Gr_M2.Hash050.checked]
  rfl
#print axioms hash050
theorem address050 : BinMerkle32Path.nodeInput (children value040 (JGc_TX2_HashBytes.state [65,234,38,73,66,178,230,20,65,121,30,37,225,239,162,80,19,158,198,194,173,16,25,109,108,151,246,72,8,249,139,52]))=input050 := by rfl
#print axioms address050
def tree050 : Tree := .branch tree040 (.supplied (JGc_TX2_HashBytes.state [65,234,38,73,66,178,230,20,65,121,30,37,225,239,162,80,19,158,198,194,173,16,25,109,108,151,246,72,8,249,139,52]))
theorem root050 : root JFp_SHADigest.digest tree050=value050 := by
  rw [tree050,root,root040]
  exact (congrArg JFp_SHADigest.digest address050).trans hash050
#print axioms root050
theorem shape050 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 16384=tree050 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 16384)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape040 f g inputs siblings]
  rw [unoccupied f g 4 16400 (by decide),siblings 4 (by decide) 16400 (by decide)]
  rfl
#print axioms shape050
def input051 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash051.message
def value051 : State := JFp_SHADigest.output JGy_Gr_M2.Hash051.result
theorem cast051_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash051.B00.input).map Fin.val=JGy_Gr_M2.Hash051.B00.input := by rfl
#print axioms cast051_0
theorem tail051 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash051.tail).map Fin.val=JGy_Gr_M2.Hash051.tail := by rfl
#print axioms tail051
theorem numeric051 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash051.message).map Fin.val=JGy_Gr_M2.Hash051.message := by
  simp only [JGy_Gr_M2.Hash051.message,JGy_Gr_M2.Hash051.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast051_0,tail051]
#print axioms numeric051
theorem hash051 : JFp_SHADigest.digest input051=value051 := by
  unfold input051 JFp_SHADigest.digest
  rw [numeric051,JGy_Gr_M2.Hash051.checked]
  rfl
#print axioms hash051
theorem address051 : BinMerkle32Path.nodeInput (children value041 (JGc_TX2_HashBytes.state [160,196,206,167,250,112,3,28,143,138,174,230,166,61,96,100,21,194,32,169,75,99,235,184,138,126,251,198,150,238,190,52]))=input051 := by rfl
#print axioms address051
def tree051 : Tree := .branch tree041 (.supplied (JGc_TX2_HashBytes.state [160,196,206,167,250,112,3,28,143,138,174,230,166,61,96,100,21,194,32,169,75,99,235,184,138,126,251,198,150,238,190,52]))
theorem root051 : root JFp_SHADigest.digest tree051=value051 := by
  rw [tree051,root,root041]
  exact (congrArg JFp_SHADigest.digest address051).trans hash051
#print axioms root051
theorem shape051 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 23360=tree051 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 23360)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape041 f g inputs siblings]
  rw [unoccupied f g 4 23376 (by decide),siblings 4 (by decide) 23376 (by decide)]
  rfl
#print axioms shape051
def input052 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash052.message
def value052 : State := JFp_SHADigest.output JGy_Gr_M2.Hash052.result
theorem cast052_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash052.B00.input).map Fin.val=JGy_Gr_M2.Hash052.B00.input := by rfl
#print axioms cast052_0
theorem tail052 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash052.tail).map Fin.val=JGy_Gr_M2.Hash052.tail := by rfl
#print axioms tail052
theorem numeric052 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash052.message).map Fin.val=JGy_Gr_M2.Hash052.message := by
  simp only [JGy_Gr_M2.Hash052.message,JGy_Gr_M2.Hash052.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast052_0,tail052]
#print axioms numeric052
theorem hash052 : JFp_SHADigest.digest input052=value052 := by
  unfold input052 JFp_SHADigest.digest
  rw [numeric052,JGy_Gr_M2.Hash052.checked]
  rfl
#print axioms hash052
theorem address052 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [116,149,89,253,254,19,246,16,170,116,173,230,189,196,143,72,229,205,60,207,4,27,195,29,163,34,89,116,252,50,119,14]) value042)=input052 := by rfl
#print axioms address052
def tree052 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [116,149,89,253,254,19,246,16,170,116,173,230,189,196,143,72,229,205,60,207,4,27,195,29,163,34,89,116,252,50,119,14])) tree042
theorem root052 : root JFp_SHADigest.digest tree052=value052 := by
  rw [tree052,root,root042]
  exact (congrArg JFp_SHADigest.digest address052).trans hash052
#print axioms root052
theorem shape052 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 36864=tree052 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 36864)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 36864 (by decide),siblings 4 (by decide) 36864 (by decide)]
  rw [shape042 f g inputs siblings]
  rfl
#print axioms shape052
def input053 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash053.message
def value053 : State := JFp_SHADigest.output JGy_Gr_M2.Hash053.result
theorem cast053_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash053.B00.input).map Fin.val=JGy_Gr_M2.Hash053.B00.input := by rfl
#print axioms cast053_0
theorem tail053 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash053.tail).map Fin.val=JGy_Gr_M2.Hash053.tail := by rfl
#print axioms tail053
theorem numeric053 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash053.message).map Fin.val=JGy_Gr_M2.Hash053.message := by
  simp only [JGy_Gr_M2.Hash053.message,JGy_Gr_M2.Hash053.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast053_0,tail053]
#print axioms numeric053
theorem hash053 : JFp_SHADigest.digest input053=value053 := by
  unfold input053 JFp_SHADigest.digest
  rw [numeric053,JGy_Gr_M2.Hash053.checked]
  rfl
#print axioms hash053
theorem address053 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [55,78,39,200,76,202,7,1,140,171,82,253,129,15,177,0,61,7,55,23,33,240,211,141,37,123,101,117,182,39,64,187]) value043)=input053 := by rfl
#print axioms address053
def tree053 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [55,78,39,200,76,202,7,1,140,171,82,253,129,15,177,0,61,7,55,23,33,240,211,141,37,123,101,117,182,39,64,187])) tree043
theorem root053 : root JFp_SHADigest.digest tree053=value053 := by
  rw [tree053,root,root043]
  exact (congrArg JFp_SHADigest.digest address053).trans hash053
#print axioms root053
theorem shape053 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 39936=tree053 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 39936)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 39936 (by decide),siblings 4 (by decide) 39936 (by decide)]
  rw [shape043 f g inputs siblings]
  rfl
#print axioms shape053
def input054 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash054.message
def value054 : State := JFp_SHADigest.output JGy_Gr_M2.Hash054.result
theorem cast054_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash054.B00.input).map Fin.val=JGy_Gr_M2.Hash054.B00.input := by rfl
#print axioms cast054_0
theorem tail054 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash054.tail).map Fin.val=JGy_Gr_M2.Hash054.tail := by rfl
#print axioms tail054
theorem numeric054 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash054.message).map Fin.val=JGy_Gr_M2.Hash054.message := by
  simp only [JGy_Gr_M2.Hash054.message,JGy_Gr_M2.Hash054.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast054_0,tail054]
#print axioms numeric054
theorem hash054 : JFp_SHADigest.digest input054=value054 := by
  unfold input054 JFp_SHADigest.digest
  rw [numeric054,JGy_Gr_M2.Hash054.checked]
  rfl
#print axioms hash054
theorem address054 : BinMerkle32Path.nodeInput (children value044 (JGc_TX2_HashBytes.state [214,125,42,28,128,37,83,168,43,239,170,218,176,52,50,65,50,39,88,130,133,76,132,84,182,217,3,23,118,224,99,151]))=input054 := by rfl
#print axioms address054
def tree054 : Tree := .branch tree044 (.supplied (JGc_TX2_HashBytes.state [214,125,42,28,128,37,83,168,43,239,170,218,176,52,50,65,50,39,88,130,133,76,132,84,182,217,3,23,118,224,99,151]))
theorem root054 : root JFp_SHADigest.digest tree054=value054 := by
  rw [tree054,root,root044]
  exact (congrArg JFp_SHADigest.digest address054).trans hash054
#print axioms root054
theorem shape054 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 45952=tree054 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 45952)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape044 f g inputs siblings]
  rw [unoccupied f g 4 45968 (by decide),siblings 4 (by decide) 45968 (by decide)]
  rfl
#print axioms shape054
def input055 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash055.message
def value055 : State := JFp_SHADigest.output JGy_Gr_M2.Hash055.result
theorem cast055_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash055.B00.input).map Fin.val=JGy_Gr_M2.Hash055.B00.input := by rfl
#print axioms cast055_0
theorem tail055 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash055.tail).map Fin.val=JGy_Gr_M2.Hash055.tail := by rfl
#print axioms tail055
theorem numeric055 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash055.message).map Fin.val=JGy_Gr_M2.Hash055.message := by
  simp only [JGy_Gr_M2.Hash055.message,JGy_Gr_M2.Hash055.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast055_0,tail055]
#print axioms numeric055
theorem hash055 : JFp_SHADigest.digest input055=value055 := by
  unfold input055 JFp_SHADigest.digest
  rw [numeric055,JGy_Gr_M2.Hash055.checked]
  rfl
#print axioms hash055
theorem address055 : BinMerkle32Path.nodeInput (children value045 (JGc_TX2_HashBytes.state [59,77,103,151,197,77,27,177,181,138,84,152,90,178,108,53,229,207,203,146,23,110,171,197,65,83,20,196,13,21,172,117]))=input055 := by rfl
#print axioms address055
def tree055 : Tree := .branch tree045 (.supplied (JGc_TX2_HashBytes.state [59,77,103,151,197,77,27,177,181,138,84,152,90,178,108,53,229,207,203,146,23,110,171,197,65,83,20,196,13,21,172,117]))
theorem root055 : root JFp_SHADigest.digest tree055=value055 := by
  rw [tree055,root,root045]
  exact (congrArg JFp_SHADigest.digest address055).trans hash055
#print axioms root055
theorem shape055 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 48064=tree055 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 48064)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape045 f g inputs siblings]
  rw [unoccupied f g 4 48080 (by decide),siblings 4 (by decide) 48080 (by decide)]
  rfl
#print axioms shape055
def input056 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash056.message
def value056 : State := JFp_SHADigest.output JGy_Gr_M2.Hash056.result
theorem cast056_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash056.B00.input).map Fin.val=JGy_Gr_M2.Hash056.B00.input := by rfl
#print axioms cast056_0
theorem tail056 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash056.tail).map Fin.val=JGy_Gr_M2.Hash056.tail := by rfl
#print axioms tail056
theorem numeric056 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash056.message).map Fin.val=JGy_Gr_M2.Hash056.message := by
  simp only [JGy_Gr_M2.Hash056.message,JGy_Gr_M2.Hash056.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast056_0,tail056]
#print axioms numeric056
theorem hash056 : JFp_SHADigest.digest input056=value056 := by
  unfold input056 JFp_SHADigest.digest
  rw [numeric056,JGy_Gr_M2.Hash056.checked]
  rfl
#print axioms hash056
theorem address056 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [121,155,170,137,92,23,153,245,180,227,87,14,77,237,32,32,201,175,78,100,37,206,227,60,30,169,227,45,145,173,245,195]) value046)=input056 := by rfl
#print axioms address056
def tree056 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [121,155,170,137,92,23,153,245,180,227,87,14,77,237,32,32,201,175,78,100,37,206,227,60,30,169,227,45,145,173,245,195])) tree046
theorem root056 : root JFp_SHADigest.digest tree056=value056 := by
  rw [tree056,root,root046]
  exact (congrArg JFp_SHADigest.digest address056).trans hash056
#print axioms root056
theorem shape056 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 48256=tree056 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 48256)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 48256 (by decide),siblings 4 (by decide) 48256 (by decide)]
  rw [shape046 f g inputs siblings]
  rfl
#print axioms shape056
def input057 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash057.message
def value057 : State := JFp_SHADigest.output JGy_Gr_M2.Hash057.result
theorem cast057_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash057.B00.input).map Fin.val=JGy_Gr_M2.Hash057.B00.input := by rfl
#print axioms cast057_0
theorem tail057 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash057.tail).map Fin.val=JGy_Gr_M2.Hash057.tail := by rfl
#print axioms tail057
theorem numeric057 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash057.message).map Fin.val=JGy_Gr_M2.Hash057.message := by
  simp only [JGy_Gr_M2.Hash057.message,JGy_Gr_M2.Hash057.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast057_0,tail057]
#print axioms numeric057
theorem hash057 : JFp_SHADigest.digest input057=value057 := by
  unfold input057 JFp_SHADigest.digest
  rw [numeric057,JGy_Gr_M2.Hash057.checked]
  rfl
#print axioms hash057
theorem address057 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [77,20,168,204,126,214,237,104,69,211,193,212,69,14,169,89,19,73,26,130,68,35,49,151,26,120,232,187,43,24,108,230]) value047)=input057 := by rfl
#print axioms address057
def tree057 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [77,20,168,204,126,214,237,104,69,211,193,212,69,14,169,89,19,73,26,130,68,35,49,151,26,120,232,187,43,24,108,230])) tree047
theorem root057 : root JFp_SHADigest.digest tree057=value057 := by
  rw [tree057,root,root047]
  exact (congrArg JFp_SHADigest.digest address057).trans hash057
#print axioms root057
theorem shape057 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 52320=tree057 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 52320)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 52320 (by decide),siblings 4 (by decide) 52320 (by decide)]
  rw [shape047 f g inputs siblings]
  rfl
#print axioms shape057
def input058 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash058.message
def value058 : State := JFp_SHADigest.output JGy_Gr_M2.Hash058.result
theorem cast058_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash058.B00.input).map Fin.val=JGy_Gr_M2.Hash058.B00.input := by rfl
#print axioms cast058_0
theorem tail058 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash058.tail).map Fin.val=JGy_Gr_M2.Hash058.tail := by rfl
#print axioms tail058
theorem numeric058 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash058.message).map Fin.val=JGy_Gr_M2.Hash058.message := by
  simp only [JGy_Gr_M2.Hash058.message,JGy_Gr_M2.Hash058.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast058_0,tail058]
#print axioms numeric058
theorem hash058 : JFp_SHADigest.digest input058=value058 := by
  unfold input058 JFp_SHADigest.digest
  rw [numeric058,JGy_Gr_M2.Hash058.checked]
  rfl
#print axioms hash058
theorem address058 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [219,113,206,154,96,101,14,206,79,208,91,12,62,43,111,15,159,175,162,128,58,189,130,180,129,14,209,29,246,135,107,199]) value048)=input058 := by rfl
#print axioms address058
def tree058 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [219,113,206,154,96,101,14,206,79,208,91,12,62,43,111,15,159,175,162,128,58,189,130,180,129,14,209,29,246,135,107,199])) tree048
theorem root058 : root JFp_SHADigest.digest tree058=value058 := by
  rw [tree058,root,root048]
  exact (congrArg JFp_SHADigest.digest address058).trans hash058
#print axioms root058
theorem shape058 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 54176=tree058 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 54176)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 4 54176 (by decide),siblings 4 (by decide) 54176 (by decide)]
  rw [shape048 f g inputs siblings]
  rfl
#print axioms shape058
def input059 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash059.message
def value059 : State := JFp_SHADigest.output JGy_Gr_M2.Hash059.result
theorem cast059_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash059.B00.input).map Fin.val=JGy_Gr_M2.Hash059.B00.input := by rfl
#print axioms cast059_0
theorem tail059 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash059.tail).map Fin.val=JGy_Gr_M2.Hash059.tail := by rfl
#print axioms tail059
theorem numeric059 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash059.message).map Fin.val=JGy_Gr_M2.Hash059.message := by
  simp only [JGy_Gr_M2.Hash059.message,JGy_Gr_M2.Hash059.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast059_0,tail059]
#print axioms numeric059
theorem hash059 : JFp_SHADigest.digest input059=value059 := by
  unfold input059 JFp_SHADigest.digest
  rw [numeric059,JGy_Gr_M2.Hash059.checked]
  rfl
#print axioms hash059
theorem address059 : BinMerkle32Path.nodeInput (children value049 (JGc_TX2_HashBytes.state [179,218,162,212,20,131,120,109,52,129,111,92,132,18,158,30,184,98,130,212,185,233,158,145,127,59,221,46,0,214,80,21]))=input059 := by rfl
#print axioms address059
def tree059 : Tree := .branch tree049 (.supplied (JGc_TX2_HashBytes.state [179,218,162,212,20,131,120,109,52,129,111,92,132,18,158,30,184,98,130,212,185,233,158,145,127,59,221,46,0,214,80,21]))
theorem root059 : root JFp_SHADigest.digest tree059=value059 := by
  rw [tree059,root,root049]
  exact (congrArg JFp_SHADigest.digest address059).trans hash059
#print axioms root059
theorem shape059 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 5 61472=tree059 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 5 61472)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape049 f g inputs siblings]
  rw [unoccupied f g 4 61488 (by decide),siblings 4 (by decide) 61488 (by decide)]
  rfl
#print axioms shape059
end AspisR1.JGy_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input060 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash060.message
def value060 : State := JFp_SHADigest.output JGy_Gr_M2.Hash060.result
theorem cast060_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash060.B00.input).map Fin.val=JGy_Gr_M2.Hash060.B00.input := by rfl
#print axioms cast060_0
theorem tail060 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash060.tail).map Fin.val=JGy_Gr_M2.Hash060.tail := by rfl
#print axioms tail060
theorem numeric060 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash060.message).map Fin.val=JGy_Gr_M2.Hash060.message := by
  simp only [JGy_Gr_M2.Hash060.message,JGy_Gr_M2.Hash060.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast060_0,tail060]
#print axioms numeric060
theorem hash060 : JFp_SHADigest.digest input060=value060 := by
  unfold input060 JFp_SHADigest.digest
  rw [numeric060,JGy_Gr_M2.Hash060.checked]
  rfl
#print axioms hash060
theorem address060 : BinMerkle32Path.nodeInput (children value050 (JGc_TX2_HashBytes.state [125,62,11,58,152,121,161,20,87,123,59,146,157,58,136,241,164,159,33,232,66,172,208,243,124,111,180,225,182,173,183,11]))=input060 := by rfl
#print axioms address060
def tree060 : Tree := .branch tree050 (.supplied (JGc_TX2_HashBytes.state [125,62,11,58,152,121,161,20,87,123,59,146,157,58,136,241,164,159,33,232,66,172,208,243,124,111,180,225,182,173,183,11]))
theorem root060 : root JFp_SHADigest.digest tree060=value060 := by
  rw [tree060,root,root050]
  exact (congrArg JFp_SHADigest.digest address060).trans hash060
#print axioms root060
theorem shape060 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 16384=tree060 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 16384)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape050 f g inputs siblings]
  rw [unoccupied f g 5 16416 (by decide),siblings 5 (by decide) 16416 (by decide)]
  rfl
#print axioms shape060
def input061 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash061.message
def value061 : State := JFp_SHADigest.output JGy_Gr_M2.Hash061.result
theorem cast061_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash061.B00.input).map Fin.val=JGy_Gr_M2.Hash061.B00.input := by rfl
#print axioms cast061_0
theorem tail061 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash061.tail).map Fin.val=JGy_Gr_M2.Hash061.tail := by rfl
#print axioms tail061
theorem numeric061 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash061.message).map Fin.val=JGy_Gr_M2.Hash061.message := by
  simp only [JGy_Gr_M2.Hash061.message,JGy_Gr_M2.Hash061.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast061_0,tail061]
#print axioms numeric061
theorem hash061 : JFp_SHADigest.digest input061=value061 := by
  unfold input061 JFp_SHADigest.digest
  rw [numeric061,JGy_Gr_M2.Hash061.checked]
  rfl
#print axioms hash061
theorem address061 : BinMerkle32Path.nodeInput (children value051 (JGc_TX2_HashBytes.state [108,85,227,67,255,107,240,217,131,85,181,219,24,10,252,188,214,141,198,133,159,73,116,15,37,35,242,27,251,66,11,3]))=input061 := by rfl
#print axioms address061
def tree061 : Tree := .branch tree051 (.supplied (JGc_TX2_HashBytes.state [108,85,227,67,255,107,240,217,131,85,181,219,24,10,252,188,214,141,198,133,159,73,116,15,37,35,242,27,251,66,11,3]))
theorem root061 : root JFp_SHADigest.digest tree061=value061 := by
  rw [tree061,root,root051]
  exact (congrArg JFp_SHADigest.digest address061).trans hash061
#print axioms root061
theorem shape061 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 23360=tree061 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 23360)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape051 f g inputs siblings]
  rw [unoccupied f g 5 23392 (by decide),siblings 5 (by decide) 23392 (by decide)]
  rfl
#print axioms shape061
def input062 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash062.message
def value062 : State := JFp_SHADigest.output JGy_Gr_M2.Hash062.result
theorem cast062_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash062.B00.input).map Fin.val=JGy_Gr_M2.Hash062.B00.input := by rfl
#print axioms cast062_0
theorem tail062 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash062.tail).map Fin.val=JGy_Gr_M2.Hash062.tail := by rfl
#print axioms tail062
theorem numeric062 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash062.message).map Fin.val=JGy_Gr_M2.Hash062.message := by
  simp only [JGy_Gr_M2.Hash062.message,JGy_Gr_M2.Hash062.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast062_0,tail062]
#print axioms numeric062
theorem hash062 : JFp_SHADigest.digest input062=value062 := by
  unfold input062 JFp_SHADigest.digest
  rw [numeric062,JGy_Gr_M2.Hash062.checked]
  rfl
#print axioms hash062
theorem address062 : BinMerkle32Path.nodeInput (children value052 (JGc_TX2_HashBytes.state [20,69,131,244,4,224,142,147,45,30,160,115,55,150,86,41,62,233,146,3,5,126,120,19,244,204,58,53,181,84,196,197]))=input062 := by rfl
#print axioms address062
def tree062 : Tree := .branch tree052 (.supplied (JGc_TX2_HashBytes.state [20,69,131,244,4,224,142,147,45,30,160,115,55,150,86,41,62,233,146,3,5,126,120,19,244,204,58,53,181,84,196,197]))
theorem root062 : root JFp_SHADigest.digest tree062=value062 := by
  rw [tree062,root,root052]
  exact (congrArg JFp_SHADigest.digest address062).trans hash062
#print axioms root062
theorem shape062 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 36864=tree062 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 36864)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape052 f g inputs siblings]
  rw [unoccupied f g 5 36896 (by decide),siblings 5 (by decide) 36896 (by decide)]
  rfl
#print axioms shape062
def input063 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash063.message
def value063 : State := JFp_SHADigest.output JGy_Gr_M2.Hash063.result
theorem cast063_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash063.B00.input).map Fin.val=JGy_Gr_M2.Hash063.B00.input := by rfl
#print axioms cast063_0
theorem tail063 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash063.tail).map Fin.val=JGy_Gr_M2.Hash063.tail := by rfl
#print axioms tail063
theorem numeric063 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash063.message).map Fin.val=JGy_Gr_M2.Hash063.message := by
  simp only [JGy_Gr_M2.Hash063.message,JGy_Gr_M2.Hash063.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast063_0,tail063]
#print axioms numeric063
theorem hash063 : JFp_SHADigest.digest input063=value063 := by
  unfold input063 JFp_SHADigest.digest
  rw [numeric063,JGy_Gr_M2.Hash063.checked]
  rfl
#print axioms hash063
theorem address063 : BinMerkle32Path.nodeInput (children value053 (JGc_TX2_HashBytes.state [46,207,213,156,44,97,223,5,239,95,131,76,225,10,249,132,169,237,91,238,24,122,79,76,77,172,35,29,240,46,161,81]))=input063 := by rfl
#print axioms address063
def tree063 : Tree := .branch tree053 (.supplied (JGc_TX2_HashBytes.state [46,207,213,156,44,97,223,5,239,95,131,76,225,10,249,132,169,237,91,238,24,122,79,76,77,172,35,29,240,46,161,81]))
theorem root063 : root JFp_SHADigest.digest tree063=value063 := by
  rw [tree063,root,root053]
  exact (congrArg JFp_SHADigest.digest address063).trans hash063
#print axioms root063
theorem shape063 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 39936=tree063 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 39936)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape053 f g inputs siblings]
  rw [unoccupied f g 5 39968 (by decide),siblings 5 (by decide) 39968 (by decide)]
  rfl
#print axioms shape063
def input064 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash064.message
def value064 : State := JFp_SHADigest.output JGy_Gr_M2.Hash064.result
theorem cast064_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash064.B00.input).map Fin.val=JGy_Gr_M2.Hash064.B00.input := by rfl
#print axioms cast064_0
theorem tail064 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash064.tail).map Fin.val=JGy_Gr_M2.Hash064.tail := by rfl
#print axioms tail064
theorem numeric064 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash064.message).map Fin.val=JGy_Gr_M2.Hash064.message := by
  simp only [JGy_Gr_M2.Hash064.message,JGy_Gr_M2.Hash064.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast064_0,tail064]
#print axioms numeric064
theorem hash064 : JFp_SHADigest.digest input064=value064 := by
  unfold input064 JFp_SHADigest.digest
  rw [numeric064,JGy_Gr_M2.Hash064.checked]
  rfl
#print axioms hash064
theorem address064 : BinMerkle32Path.nodeInput (children value054 (JGc_TX2_HashBytes.state [95,12,139,86,115,166,43,216,121,70,107,251,72,70,51,33,19,180,64,129,152,241,136,194,104,235,4,19,207,59,71,38]))=input064 := by rfl
#print axioms address064
def tree064 : Tree := .branch tree054 (.supplied (JGc_TX2_HashBytes.state [95,12,139,86,115,166,43,216,121,70,107,251,72,70,51,33,19,180,64,129,152,241,136,194,104,235,4,19,207,59,71,38]))
theorem root064 : root JFp_SHADigest.digest tree064=value064 := by
  rw [tree064,root,root054]
  exact (congrArg JFp_SHADigest.digest address064).trans hash064
#print axioms root064
theorem shape064 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 45952=tree064 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 45952)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape054 f g inputs siblings]
  rw [unoccupied f g 5 45984 (by decide),siblings 5 (by decide) 45984 (by decide)]
  rfl
#print axioms shape064
def input065 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash065.message
def value065 : State := JFp_SHADigest.output JGy_Gr_M2.Hash065.result
theorem cast065_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash065.B00.input).map Fin.val=JGy_Gr_M2.Hash065.B00.input := by rfl
#print axioms cast065_0
theorem tail065 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash065.tail).map Fin.val=JGy_Gr_M2.Hash065.tail := by rfl
#print axioms tail065
theorem numeric065 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash065.message).map Fin.val=JGy_Gr_M2.Hash065.message := by
  simp only [JGy_Gr_M2.Hash065.message,JGy_Gr_M2.Hash065.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast065_0,tail065]
#print axioms numeric065
theorem hash065 : JFp_SHADigest.digest input065=value065 := by
  unfold input065 JFp_SHADigest.digest
  rw [numeric065,JGy_Gr_M2.Hash065.checked]
  rfl
#print axioms hash065
theorem address065 : BinMerkle32Path.nodeInput (children value055 (JGc_TX2_HashBytes.state [96,144,30,173,153,163,192,34,238,70,42,254,168,235,204,203,30,126,228,206,111,202,34,173,110,50,39,31,76,7,91,117]))=input065 := by rfl
#print axioms address065
def tree065 : Tree := .branch tree055 (.supplied (JGc_TX2_HashBytes.state [96,144,30,173,153,163,192,34,238,70,42,254,168,235,204,203,30,126,228,206,111,202,34,173,110,50,39,31,76,7,91,117]))
theorem root065 : root JFp_SHADigest.digest tree065=value065 := by
  rw [tree065,root,root055]
  exact (congrArg JFp_SHADigest.digest address065).trans hash065
#print axioms root065
theorem shape065 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 48064=tree065 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 48064)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape055 f g inputs siblings]
  rw [unoccupied f g 5 48096 (by decide),siblings 5 (by decide) 48096 (by decide)]
  rfl
#print axioms shape065
def input066 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash066.message
def value066 : State := JFp_SHADigest.output JGy_Gr_M2.Hash066.result
theorem cast066_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash066.B00.input).map Fin.val=JGy_Gr_M2.Hash066.B00.input := by rfl
#print axioms cast066_0
theorem tail066 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash066.tail).map Fin.val=JGy_Gr_M2.Hash066.tail := by rfl
#print axioms tail066
theorem numeric066 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash066.message).map Fin.val=JGy_Gr_M2.Hash066.message := by
  simp only [JGy_Gr_M2.Hash066.message,JGy_Gr_M2.Hash066.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast066_0,tail066]
#print axioms numeric066
theorem hash066 : JFp_SHADigest.digest input066=value066 := by
  unfold input066 JFp_SHADigest.digest
  rw [numeric066,JGy_Gr_M2.Hash066.checked]
  rfl
#print axioms hash066
theorem address066 : BinMerkle32Path.nodeInput (children value056 (JGc_TX2_HashBytes.state [193,40,69,139,235,218,184,141,95,6,104,82,149,17,63,148,181,126,57,142,185,25,231,88,16,185,114,171,2,44,236,81]))=input066 := by rfl
#print axioms address066
def tree066 : Tree := .branch tree056 (.supplied (JGc_TX2_HashBytes.state [193,40,69,139,235,218,184,141,95,6,104,82,149,17,63,148,181,126,57,142,185,25,231,88,16,185,114,171,2,44,236,81]))
theorem root066 : root JFp_SHADigest.digest tree066=value066 := by
  rw [tree066,root,root056]
  exact (congrArg JFp_SHADigest.digest address066).trans hash066
#print axioms root066
theorem shape066 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 48256=tree066 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 48256)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape056 f g inputs siblings]
  rw [unoccupied f g 5 48288 (by decide),siblings 5 (by decide) 48288 (by decide)]
  rfl
#print axioms shape066
def input067 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash067.message
def value067 : State := JFp_SHADigest.output JGy_Gr_M2.Hash067.result
theorem cast067_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash067.B00.input).map Fin.val=JGy_Gr_M2.Hash067.B00.input := by rfl
#print axioms cast067_0
theorem tail067 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash067.tail).map Fin.val=JGy_Gr_M2.Hash067.tail := by rfl
#print axioms tail067
theorem numeric067 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash067.message).map Fin.val=JGy_Gr_M2.Hash067.message := by
  simp only [JGy_Gr_M2.Hash067.message,JGy_Gr_M2.Hash067.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast067_0,tail067]
#print axioms numeric067
theorem hash067 : JFp_SHADigest.digest input067=value067 := by
  unfold input067 JFp_SHADigest.digest
  rw [numeric067,JGy_Gr_M2.Hash067.checked]
  rfl
#print axioms hash067
theorem address067 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [108,244,30,13,4,164,224,60,6,70,5,194,113,19,224,179,103,199,233,246,124,170,2,80,220,146,148,253,253,191,218,219]) value057)=input067 := by rfl
#print axioms address067
def tree067 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [108,244,30,13,4,164,224,60,6,70,5,194,113,19,224,179,103,199,233,246,124,170,2,80,220,146,148,253,253,191,218,219])) tree057
theorem root067 : root JFp_SHADigest.digest tree067=value067 := by
  rw [tree067,root,root057]
  exact (congrArg JFp_SHADigest.digest address067).trans hash067
#print axioms root067
theorem shape067 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 52288=tree067 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 52288)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 52288 (by decide),siblings 5 (by decide) 52288 (by decide)]
  rw [shape057 f g inputs siblings]
  rfl
#print axioms shape067
def input068 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash068.message
def value068 : State := JFp_SHADigest.output JGy_Gr_M2.Hash068.result
theorem cast068_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash068.B00.input).map Fin.val=JGy_Gr_M2.Hash068.B00.input := by rfl
#print axioms cast068_0
theorem tail068 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash068.tail).map Fin.val=JGy_Gr_M2.Hash068.tail := by rfl
#print axioms tail068
theorem numeric068 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash068.message).map Fin.val=JGy_Gr_M2.Hash068.message := by
  simp only [JGy_Gr_M2.Hash068.message,JGy_Gr_M2.Hash068.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast068_0,tail068]
#print axioms numeric068
theorem hash068 : JFp_SHADigest.digest input068=value068 := by
  unfold input068 JFp_SHADigest.digest
  rw [numeric068,JGy_Gr_M2.Hash068.checked]
  rfl
#print axioms hash068
theorem address068 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [77,83,165,84,145,44,241,189,189,116,178,122,62,239,124,255,41,4,75,96,207,188,221,80,196,143,108,51,218,23,202,213]) value058)=input068 := by rfl
#print axioms address068
def tree068 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [77,83,165,84,145,44,241,189,189,116,178,122,62,239,124,255,41,4,75,96,207,188,221,80,196,143,108,51,218,23,202,213])) tree058
theorem root068 : root JFp_SHADigest.digest tree068=value068 := by
  rw [tree068,root,root058]
  exact (congrArg JFp_SHADigest.digest address068).trans hash068
#print axioms root068
theorem shape068 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 54144=tree068 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 54144)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 54144 (by decide),siblings 5 (by decide) 54144 (by decide)]
  rw [shape058 f g inputs siblings]
  rfl
#print axioms shape068
def input069 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash069.message
def value069 : State := JFp_SHADigest.output JGy_Gr_M2.Hash069.result
theorem cast069_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash069.B00.input).map Fin.val=JGy_Gr_M2.Hash069.B00.input := by rfl
#print axioms cast069_0
theorem tail069 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash069.tail).map Fin.val=JGy_Gr_M2.Hash069.tail := by rfl
#print axioms tail069
theorem numeric069 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash069.message).map Fin.val=JGy_Gr_M2.Hash069.message := by
  simp only [JGy_Gr_M2.Hash069.message,JGy_Gr_M2.Hash069.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast069_0,tail069]
#print axioms numeric069
theorem hash069 : JFp_SHADigest.digest input069=value069 := by
  unfold input069 JFp_SHADigest.digest
  rw [numeric069,JGy_Gr_M2.Hash069.checked]
  rfl
#print axioms hash069
theorem address069 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [111,137,193,249,230,246,19,197,115,7,165,255,66,184,205,55,249,202,250,176,180,214,60,254,61,126,78,118,255,181,149,35]) value059)=input069 := by rfl
#print axioms address069
def tree069 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [111,137,193,249,230,246,19,197,115,7,165,255,66,184,205,55,249,202,250,176,180,214,60,254,61,126,78,118,255,181,149,35])) tree059
theorem root069 : root JFp_SHADigest.digest tree069=value069 := by
  rw [tree069,root,root059]
  exact (congrArg JFp_SHADigest.digest address069).trans hash069
#print axioms root069
theorem shape069 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 6 61440=tree069 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 6 61440)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 5 61440 (by decide),siblings 5 (by decide) 61440 (by decide)]
  rw [shape059 f g inputs siblings]
  rfl
#print axioms shape069
end AspisR1.JGy_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input070 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash070.message
def value070 : State := JFp_SHADigest.output JGy_Gr_M2.Hash070.result
theorem cast070_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash070.B00.input).map Fin.val=JGy_Gr_M2.Hash070.B00.input := by rfl
#print axioms cast070_0
theorem tail070 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash070.tail).map Fin.val=JGy_Gr_M2.Hash070.tail := by rfl
#print axioms tail070
theorem numeric070 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash070.message).map Fin.val=JGy_Gr_M2.Hash070.message := by
  simp only [JGy_Gr_M2.Hash070.message,JGy_Gr_M2.Hash070.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast070_0,tail070]
#print axioms numeric070
theorem hash070 : JFp_SHADigest.digest input070=value070 := by
  unfold input070 JFp_SHADigest.digest
  rw [numeric070,JGy_Gr_M2.Hash070.checked]
  rfl
#print axioms hash070
theorem address070 : BinMerkle32Path.nodeInput (children value060 (JGc_TX2_HashBytes.state [12,35,6,54,189,41,166,74,28,227,63,181,204,131,135,75,78,199,125,83,131,232,162,74,16,255,240,44,226,253,152,131]))=input070 := by rfl
#print axioms address070
def tree070 : Tree := .branch tree060 (.supplied (JGc_TX2_HashBytes.state [12,35,6,54,189,41,166,74,28,227,63,181,204,131,135,75,78,199,125,83,131,232,162,74,16,255,240,44,226,253,152,131]))
theorem root070 : root JFp_SHADigest.digest tree070=value070 := by
  rw [tree070,root,root060]
  exact (congrArg JFp_SHADigest.digest address070).trans hash070
#print axioms root070
theorem shape070 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 16384=tree070 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 16384)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape060 f g inputs siblings]
  rw [unoccupied f g 6 16448 (by decide),siblings 6 (by decide) 16448 (by decide)]
  rfl
#print axioms shape070
def input071 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash071.message
def value071 : State := JFp_SHADigest.output JGy_Gr_M2.Hash071.result
theorem cast071_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash071.B00.input).map Fin.val=JGy_Gr_M2.Hash071.B00.input := by rfl
#print axioms cast071_0
theorem tail071 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash071.tail).map Fin.val=JGy_Gr_M2.Hash071.tail := by rfl
#print axioms tail071
theorem numeric071 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash071.message).map Fin.val=JGy_Gr_M2.Hash071.message := by
  simp only [JGy_Gr_M2.Hash071.message,JGy_Gr_M2.Hash071.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast071_0,tail071]
#print axioms numeric071
theorem hash071 : JFp_SHADigest.digest input071=value071 := by
  unfold input071 JFp_SHADigest.digest
  rw [numeric071,JGy_Gr_M2.Hash071.checked]
  rfl
#print axioms hash071
theorem address071 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [34,202,202,246,204,161,168,147,72,248,145,59,46,233,17,80,67,226,203,239,118,214,122,140,141,112,234,72,115,236,35,119]) value061)=input071 := by rfl
#print axioms address071
def tree071 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [34,202,202,246,204,161,168,147,72,248,145,59,46,233,17,80,67,226,203,239,118,214,122,140,141,112,234,72,115,236,35,119])) tree061
theorem root071 : root JFp_SHADigest.digest tree071=value071 := by
  rw [tree071,root,root061]
  exact (congrArg JFp_SHADigest.digest address071).trans hash071
#print axioms root071
theorem shape071 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 23296=tree071 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 23296)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 23296 (by decide),siblings 6 (by decide) 23296 (by decide)]
  rw [shape061 f g inputs siblings]
  rfl
#print axioms shape071
def input072 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash072.message
def value072 : State := JFp_SHADigest.output JGy_Gr_M2.Hash072.result
theorem cast072_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash072.B00.input).map Fin.val=JGy_Gr_M2.Hash072.B00.input := by rfl
#print axioms cast072_0
theorem tail072 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash072.tail).map Fin.val=JGy_Gr_M2.Hash072.tail := by rfl
#print axioms tail072
theorem numeric072 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash072.message).map Fin.val=JGy_Gr_M2.Hash072.message := by
  simp only [JGy_Gr_M2.Hash072.message,JGy_Gr_M2.Hash072.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast072_0,tail072]
#print axioms numeric072
theorem hash072 : JFp_SHADigest.digest input072=value072 := by
  unfold input072 JFp_SHADigest.digest
  rw [numeric072,JGy_Gr_M2.Hash072.checked]
  rfl
#print axioms hash072
theorem address072 : BinMerkle32Path.nodeInput (children value062 (JGc_TX2_HashBytes.state [233,186,25,148,101,33,33,145,191,159,134,50,19,208,18,164,241,22,203,112,242,116,2,159,74,87,212,75,68,12,27,203]))=input072 := by rfl
#print axioms address072
def tree072 : Tree := .branch tree062 (.supplied (JGc_TX2_HashBytes.state [233,186,25,148,101,33,33,145,191,159,134,50,19,208,18,164,241,22,203,112,242,116,2,159,74,87,212,75,68,12,27,203]))
theorem root072 : root JFp_SHADigest.digest tree072=value072 := by
  rw [tree072,root,root062]
  exact (congrArg JFp_SHADigest.digest address072).trans hash072
#print axioms root072
theorem shape072 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 36864=tree072 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 36864)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape062 f g inputs siblings]
  rw [unoccupied f g 6 36928 (by decide),siblings 6 (by decide) 36928 (by decide)]
  rfl
#print axioms shape072
def input073 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash073.message
def value073 : State := JFp_SHADigest.output JGy_Gr_M2.Hash073.result
theorem cast073_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash073.B00.input).map Fin.val=JGy_Gr_M2.Hash073.B00.input := by rfl
#print axioms cast073_0
theorem tail073 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash073.tail).map Fin.val=JGy_Gr_M2.Hash073.tail := by rfl
#print axioms tail073
theorem numeric073 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash073.message).map Fin.val=JGy_Gr_M2.Hash073.message := by
  simp only [JGy_Gr_M2.Hash073.message,JGy_Gr_M2.Hash073.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast073_0,tail073]
#print axioms numeric073
theorem hash073 : JFp_SHADigest.digest input073=value073 := by
  unfold input073 JFp_SHADigest.digest
  rw [numeric073,JGy_Gr_M2.Hash073.checked]
  rfl
#print axioms hash073
theorem address073 : BinMerkle32Path.nodeInput (children value063 (JGc_TX2_HashBytes.state [172,95,38,161,233,39,109,98,162,182,95,62,119,94,97,67,209,214,59,41,199,165,99,92,109,80,89,57,162,40,2,101]))=input073 := by rfl
#print axioms address073
def tree073 : Tree := .branch tree063 (.supplied (JGc_TX2_HashBytes.state [172,95,38,161,233,39,109,98,162,182,95,62,119,94,97,67,209,214,59,41,199,165,99,92,109,80,89,57,162,40,2,101]))
theorem root073 : root JFp_SHADigest.digest tree073=value073 := by
  rw [tree073,root,root063]
  exact (congrArg JFp_SHADigest.digest address073).trans hash073
#print axioms root073
theorem shape073 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 39936=tree073 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 39936)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape063 f g inputs siblings]
  rw [unoccupied f g 6 40000 (by decide),siblings 6 (by decide) 40000 (by decide)]
  rfl
#print axioms shape073
def input074 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash074.message
def value074 : State := JFp_SHADigest.output JGy_Gr_M2.Hash074.result
theorem cast074_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash074.B00.input).map Fin.val=JGy_Gr_M2.Hash074.B00.input := by rfl
#print axioms cast074_0
theorem tail074 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash074.tail).map Fin.val=JGy_Gr_M2.Hash074.tail := by rfl
#print axioms tail074
theorem numeric074 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash074.message).map Fin.val=JGy_Gr_M2.Hash074.message := by
  simp only [JGy_Gr_M2.Hash074.message,JGy_Gr_M2.Hash074.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast074_0,tail074]
#print axioms numeric074
theorem hash074 : JFp_SHADigest.digest input074=value074 := by
  unfold input074 JFp_SHADigest.digest
  rw [numeric074,JGy_Gr_M2.Hash074.checked]
  rfl
#print axioms hash074
theorem address074 : BinMerkle32Path.nodeInput (children value064 (JGc_TX2_HashBytes.state [103,108,72,109,95,12,246,45,50,177,228,166,118,36,249,156,201,210,30,254,219,199,140,75,105,48,211,178,152,240,35,25]))=input074 := by rfl
#print axioms address074
def tree074 : Tree := .branch tree064 (.supplied (JGc_TX2_HashBytes.state [103,108,72,109,95,12,246,45,50,177,228,166,118,36,249,156,201,210,30,254,219,199,140,75,105,48,211,178,152,240,35,25]))
theorem root074 : root JFp_SHADigest.digest tree074=value074 := by
  rw [tree074,root,root064]
  exact (congrArg JFp_SHADigest.digest address074).trans hash074
#print axioms root074
theorem shape074 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 45952=tree074 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 45952)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape064 f g inputs siblings]
  rw [unoccupied f g 6 46016 (by decide),siblings 6 (by decide) 46016 (by decide)]
  rfl
#print axioms shape074
def input075 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash075.message
def value075 : State := JFp_SHADigest.output JGy_Gr_M2.Hash075.result
theorem cast075_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash075.B00.input).map Fin.val=JGy_Gr_M2.Hash075.B00.input := by rfl
#print axioms cast075_0
theorem tail075 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash075.tail).map Fin.val=JGy_Gr_M2.Hash075.tail := by rfl
#print axioms tail075
theorem numeric075 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash075.message).map Fin.val=JGy_Gr_M2.Hash075.message := by
  simp only [JGy_Gr_M2.Hash075.message,JGy_Gr_M2.Hash075.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast075_0,tail075]
#print axioms numeric075
theorem hash075 : JFp_SHADigest.digest input075=value075 := by
  unfold input075 JFp_SHADigest.digest
  rw [numeric075,JGy_Gr_M2.Hash075.checked]
  rfl
#print axioms hash075
theorem address075 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [76,138,139,110,125,144,229,21,210,24,82,54,6,198,0,84,11,57,149,77,118,158,174,117,16,240,50,61,167,224,164,114]) value065)=input075 := by rfl
#print axioms address075
def tree075 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [76,138,139,110,125,144,229,21,210,24,82,54,6,198,0,84,11,57,149,77,118,158,174,117,16,240,50,61,167,224,164,114])) tree065
theorem root075 : root JFp_SHADigest.digest tree075=value075 := by
  rw [tree075,root,root065]
  exact (congrArg JFp_SHADigest.digest address075).trans hash075
#print axioms root075
theorem shape075 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 48000=tree075 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 48000)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 48000 (by decide),siblings 6 (by decide) 48000 (by decide)]
  rw [shape065 f g inputs siblings]
  rfl
#print axioms shape075
def input076 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash076.message
def value076 : State := JFp_SHADigest.output JGy_Gr_M2.Hash076.result
theorem cast076_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash076.B00.input).map Fin.val=JGy_Gr_M2.Hash076.B00.input := by rfl
#print axioms cast076_0
theorem tail076 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash076.tail).map Fin.val=JGy_Gr_M2.Hash076.tail := by rfl
#print axioms tail076
theorem numeric076 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash076.message).map Fin.val=JGy_Gr_M2.Hash076.message := by
  simp only [JGy_Gr_M2.Hash076.message,JGy_Gr_M2.Hash076.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast076_0,tail076]
#print axioms numeric076
theorem hash076 : JFp_SHADigest.digest input076=value076 := by
  unfold input076 JFp_SHADigest.digest
  rw [numeric076,JGy_Gr_M2.Hash076.checked]
  rfl
#print axioms hash076
theorem address076 : BinMerkle32Path.nodeInput (children value066 (JGc_TX2_HashBytes.state [92,18,27,186,69,57,105,145,26,193,234,90,166,206,223,1,124,10,44,87,174,35,213,59,133,136,95,93,181,15,102,76]))=input076 := by rfl
#print axioms address076
def tree076 : Tree := .branch tree066 (.supplied (JGc_TX2_HashBytes.state [92,18,27,186,69,57,105,145,26,193,234,90,166,206,223,1,124,10,44,87,174,35,213,59,133,136,95,93,181,15,102,76]))
theorem root076 : root JFp_SHADigest.digest tree076=value076 := by
  rw [tree076,root,root066]
  exact (congrArg JFp_SHADigest.digest address076).trans hash076
#print axioms root076
theorem shape076 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 48256=tree076 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 48256)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape066 f g inputs siblings]
  rw [unoccupied f g 6 48320 (by decide),siblings 6 (by decide) 48320 (by decide)]
  rfl
#print axioms shape076
def input077 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash077.message
def value077 : State := JFp_SHADigest.output JGy_Gr_M2.Hash077.result
theorem cast077_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash077.B00.input).map Fin.val=JGy_Gr_M2.Hash077.B00.input := by rfl
#print axioms cast077_0
theorem tail077 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash077.tail).map Fin.val=JGy_Gr_M2.Hash077.tail := by rfl
#print axioms tail077
theorem numeric077 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash077.message).map Fin.val=JGy_Gr_M2.Hash077.message := by
  simp only [JGy_Gr_M2.Hash077.message,JGy_Gr_M2.Hash077.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast077_0,tail077]
#print axioms numeric077
theorem hash077 : JFp_SHADigest.digest input077=value077 := by
  unfold input077 JFp_SHADigest.digest
  rw [numeric077,JGy_Gr_M2.Hash077.checked]
  rfl
#print axioms hash077
theorem address077 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [221,19,169,114,80,134,201,224,126,254,210,16,35,216,131,101,98,130,177,176,105,17,245,221,225,119,36,214,154,102,135,54]) value067)=input077 := by rfl
#print axioms address077
def tree077 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [221,19,169,114,80,134,201,224,126,254,210,16,35,216,131,101,98,130,177,176,105,17,245,221,225,119,36,214,154,102,135,54])) tree067
theorem root077 : root JFp_SHADigest.digest tree077=value077 := by
  rw [tree077,root,root067]
  exact (congrArg JFp_SHADigest.digest address077).trans hash077
#print axioms root077
theorem shape077 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 52224=tree077 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 52224)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 6 52224 (by decide),siblings 6 (by decide) 52224 (by decide)]
  rw [shape067 f g inputs siblings]
  rfl
#print axioms shape077
def input078 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash078.message
def value078 : State := JFp_SHADigest.output JGy_Gr_M2.Hash078.result
theorem cast078_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash078.B00.input).map Fin.val=JGy_Gr_M2.Hash078.B00.input := by rfl
#print axioms cast078_0
theorem tail078 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash078.tail).map Fin.val=JGy_Gr_M2.Hash078.tail := by rfl
#print axioms tail078
theorem numeric078 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash078.message).map Fin.val=JGy_Gr_M2.Hash078.message := by
  simp only [JGy_Gr_M2.Hash078.message,JGy_Gr_M2.Hash078.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast078_0,tail078]
#print axioms numeric078
theorem hash078 : JFp_SHADigest.digest input078=value078 := by
  unfold input078 JFp_SHADigest.digest
  rw [numeric078,JGy_Gr_M2.Hash078.checked]
  rfl
#print axioms hash078
theorem address078 : BinMerkle32Path.nodeInput (children value068 (JGc_TX2_HashBytes.state [109,164,95,10,124,67,109,255,131,97,215,20,161,76,7,61,239,85,118,134,154,43,70,21,176,103,66,1,84,203,21,178]))=input078 := by rfl
#print axioms address078
def tree078 : Tree := .branch tree068 (.supplied (JGc_TX2_HashBytes.state [109,164,95,10,124,67,109,255,131,97,215,20,161,76,7,61,239,85,118,134,154,43,70,21,176,103,66,1,84,203,21,178]))
theorem root078 : root JFp_SHADigest.digest tree078=value078 := by
  rw [tree078,root,root068]
  exact (congrArg JFp_SHADigest.digest address078).trans hash078
#print axioms root078
theorem shape078 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 54144=tree078 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 54144)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape068 f g inputs siblings]
  rw [unoccupied f g 6 54208 (by decide),siblings 6 (by decide) 54208 (by decide)]
  rfl
#print axioms shape078
def input079 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash079.message
def value079 : State := JFp_SHADigest.output JGy_Gr_M2.Hash079.result
theorem cast079_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash079.B00.input).map Fin.val=JGy_Gr_M2.Hash079.B00.input := by rfl
#print axioms cast079_0
theorem tail079 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash079.tail).map Fin.val=JGy_Gr_M2.Hash079.tail := by rfl
#print axioms tail079
theorem numeric079 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash079.message).map Fin.val=JGy_Gr_M2.Hash079.message := by
  simp only [JGy_Gr_M2.Hash079.message,JGy_Gr_M2.Hash079.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast079_0,tail079]
#print axioms numeric079
theorem hash079 : JFp_SHADigest.digest input079=value079 := by
  unfold input079 JFp_SHADigest.digest
  rw [numeric079,JGy_Gr_M2.Hash079.checked]
  rfl
#print axioms hash079
theorem address079 : BinMerkle32Path.nodeInput (children value069 (JGc_TX2_HashBytes.state [189,12,56,31,97,219,222,72,85,148,145,20,206,134,123,106,158,78,125,165,158,116,184,132,122,139,219,64,2,74,255,189]))=input079 := by rfl
#print axioms address079
def tree079 : Tree := .branch tree069 (.supplied (JGc_TX2_HashBytes.state [189,12,56,31,97,219,222,72,85,148,145,20,206,134,123,106,158,78,125,165,158,116,184,132,122,139,219,64,2,74,255,189]))
theorem root079 : root JFp_SHADigest.digest tree079=value079 := by
  rw [tree079,root,root069]
  exact (congrArg JFp_SHADigest.digest address079).trans hash079
#print axioms root079
theorem shape079 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 7 61440=tree079 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 7 61440)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape069 f g inputs siblings]
  rw [unoccupied f g 6 61504 (by decide),siblings 6 (by decide) 61504 (by decide)]
  rfl
#print axioms shape079
end AspisR1.JGy_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input080 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash080.message
def value080 : State := JFp_SHADigest.output JGy_Gr_M2.Hash080.result
theorem cast080_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash080.B00.input).map Fin.val=JGy_Gr_M2.Hash080.B00.input := by rfl
#print axioms cast080_0
theorem tail080 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash080.tail).map Fin.val=JGy_Gr_M2.Hash080.tail := by rfl
#print axioms tail080
theorem numeric080 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash080.message).map Fin.val=JGy_Gr_M2.Hash080.message := by
  simp only [JGy_Gr_M2.Hash080.message,JGy_Gr_M2.Hash080.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast080_0,tail080]
#print axioms numeric080
theorem hash080 : JFp_SHADigest.digest input080=value080 := by
  unfold input080 JFp_SHADigest.digest
  rw [numeric080,JGy_Gr_M2.Hash080.checked]
  rfl
#print axioms hash080
theorem address080 : BinMerkle32Path.nodeInput (children value070 (JGc_TX2_HashBytes.state [40,66,57,248,171,64,19,248,144,29,218,123,161,176,117,253,56,239,96,55,49,89,217,26,77,172,100,4,82,114,8,47]))=input080 := by rfl
#print axioms address080
def tree080 : Tree := .branch tree070 (.supplied (JGc_TX2_HashBytes.state [40,66,57,248,171,64,19,248,144,29,218,123,161,176,117,253,56,239,96,55,49,89,217,26,77,172,100,4,82,114,8,47]))
theorem root080 : root JFp_SHADigest.digest tree080=value080 := by
  rw [tree080,root,root070]
  exact (congrArg JFp_SHADigest.digest address080).trans hash080
#print axioms root080
theorem shape080 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 16384=tree080 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 16384)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape070 f g inputs siblings]
  rw [unoccupied f g 7 16512 (by decide),siblings 7 (by decide) 16512 (by decide)]
  rfl
#print axioms shape080
def input081 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash081.message
def value081 : State := JFp_SHADigest.output JGy_Gr_M2.Hash081.result
theorem cast081_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash081.B00.input).map Fin.val=JGy_Gr_M2.Hash081.B00.input := by rfl
#print axioms cast081_0
theorem tail081 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash081.tail).map Fin.val=JGy_Gr_M2.Hash081.tail := by rfl
#print axioms tail081
theorem numeric081 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash081.message).map Fin.val=JGy_Gr_M2.Hash081.message := by
  simp only [JGy_Gr_M2.Hash081.message,JGy_Gr_M2.Hash081.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast081_0,tail081]
#print axioms numeric081
theorem hash081 : JFp_SHADigest.digest input081=value081 := by
  unfold input081 JFp_SHADigest.digest
  rw [numeric081,JGy_Gr_M2.Hash081.checked]
  rfl
#print axioms hash081
theorem address081 : BinMerkle32Path.nodeInput (children value071 (JGc_TX2_HashBytes.state [120,18,210,66,139,22,89,122,216,63,152,111,19,111,250,236,51,117,22,85,177,55,233,164,124,98,214,151,43,78,253,217]))=input081 := by rfl
#print axioms address081
def tree081 : Tree := .branch tree071 (.supplied (JGc_TX2_HashBytes.state [120,18,210,66,139,22,89,122,216,63,152,111,19,111,250,236,51,117,22,85,177,55,233,164,124,98,214,151,43,78,253,217]))
theorem root081 : root JFp_SHADigest.digest tree081=value081 := by
  rw [tree081,root,root071]
  exact (congrArg JFp_SHADigest.digest address081).trans hash081
#print axioms root081
theorem shape081 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 23296=tree081 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 23296)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape071 f g inputs siblings]
  rw [unoccupied f g 7 23424 (by decide),siblings 7 (by decide) 23424 (by decide)]
  rfl
#print axioms shape081
def input082 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash082.message
def value082 : State := JFp_SHADigest.output JGy_Gr_M2.Hash082.result
theorem cast082_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash082.B00.input).map Fin.val=JGy_Gr_M2.Hash082.B00.input := by rfl
#print axioms cast082_0
theorem tail082 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash082.tail).map Fin.val=JGy_Gr_M2.Hash082.tail := by rfl
#print axioms tail082
theorem numeric082 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash082.message).map Fin.val=JGy_Gr_M2.Hash082.message := by
  simp only [JGy_Gr_M2.Hash082.message,JGy_Gr_M2.Hash082.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast082_0,tail082]
#print axioms numeric082
theorem hash082 : JFp_SHADigest.digest input082=value082 := by
  unfold input082 JFp_SHADigest.digest
  rw [numeric082,JGy_Gr_M2.Hash082.checked]
  rfl
#print axioms hash082
theorem address082 : BinMerkle32Path.nodeInput (children value072 (JGc_TX2_HashBytes.state [103,178,124,35,134,30,155,148,34,121,100,244,172,217,64,95,40,79,185,187,244,242,175,24,223,94,11,7,90,165,205,4]))=input082 := by rfl
#print axioms address082
def tree082 : Tree := .branch tree072 (.supplied (JGc_TX2_HashBytes.state [103,178,124,35,134,30,155,148,34,121,100,244,172,217,64,95,40,79,185,187,244,242,175,24,223,94,11,7,90,165,205,4]))
theorem root082 : root JFp_SHADigest.digest tree082=value082 := by
  rw [tree082,root,root072]
  exact (congrArg JFp_SHADigest.digest address082).trans hash082
#print axioms root082
theorem shape082 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 36864=tree082 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 36864)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape072 f g inputs siblings]
  rw [unoccupied f g 7 36992 (by decide),siblings 7 (by decide) 36992 (by decide)]
  rfl
#print axioms shape082
def input083 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash083.message
def value083 : State := JFp_SHADigest.output JGy_Gr_M2.Hash083.result
theorem cast083_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash083.B00.input).map Fin.val=JGy_Gr_M2.Hash083.B00.input := by rfl
#print axioms cast083_0
theorem tail083 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash083.tail).map Fin.val=JGy_Gr_M2.Hash083.tail := by rfl
#print axioms tail083
theorem numeric083 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash083.message).map Fin.val=JGy_Gr_M2.Hash083.message := by
  simp only [JGy_Gr_M2.Hash083.message,JGy_Gr_M2.Hash083.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast083_0,tail083]
#print axioms numeric083
theorem hash083 : JFp_SHADigest.digest input083=value083 := by
  unfold input083 JFp_SHADigest.digest
  rw [numeric083,JGy_Gr_M2.Hash083.checked]
  rfl
#print axioms hash083
theorem address083 : BinMerkle32Path.nodeInput (children value073 (JGc_TX2_HashBytes.state [226,197,181,101,101,106,77,175,222,109,224,228,95,177,222,195,21,159,182,213,81,131,239,8,141,115,209,130,107,39,67,196]))=input083 := by rfl
#print axioms address083
def tree083 : Tree := .branch tree073 (.supplied (JGc_TX2_HashBytes.state [226,197,181,101,101,106,77,175,222,109,224,228,95,177,222,195,21,159,182,213,81,131,239,8,141,115,209,130,107,39,67,196]))
theorem root083 : root JFp_SHADigest.digest tree083=value083 := by
  rw [tree083,root,root073]
  exact (congrArg JFp_SHADigest.digest address083).trans hash083
#print axioms root083
theorem shape083 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 39936=tree083 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 39936)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape073 f g inputs siblings]
  rw [unoccupied f g 7 40064 (by decide),siblings 7 (by decide) 40064 (by decide)]
  rfl
#print axioms shape083
def input084 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash084.message
def value084 : State := JFp_SHADigest.output JGy_Gr_M2.Hash084.result
theorem cast084_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash084.B00.input).map Fin.val=JGy_Gr_M2.Hash084.B00.input := by rfl
#print axioms cast084_0
theorem tail084 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash084.tail).map Fin.val=JGy_Gr_M2.Hash084.tail := by rfl
#print axioms tail084
theorem numeric084 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash084.message).map Fin.val=JGy_Gr_M2.Hash084.message := by
  simp only [JGy_Gr_M2.Hash084.message,JGy_Gr_M2.Hash084.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast084_0,tail084]
#print axioms numeric084
theorem hash084 : JFp_SHADigest.digest input084=value084 := by
  unfold input084 JFp_SHADigest.digest
  rw [numeric084,JGy_Gr_M2.Hash084.checked]
  rfl
#print axioms hash084
theorem address084 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [79,228,52,63,17,238,145,181,34,187,241,201,144,85,1,72,189,253,175,235,150,239,202,216,171,117,100,210,208,107,207,133]) value074)=input084 := by rfl
#print axioms address084
def tree084 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [79,228,52,63,17,238,145,181,34,187,241,201,144,85,1,72,189,253,175,235,150,239,202,216,171,117,100,210,208,107,207,133])) tree074
theorem root084 : root JFp_SHADigest.digest tree084=value084 := by
  rw [tree084,root,root074]
  exact (congrArg JFp_SHADigest.digest address084).trans hash084
#print axioms root084
theorem shape084 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 45824=tree084 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 45824)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 7 45824 (by decide),siblings 7 (by decide) 45824 (by decide)]
  rw [shape074 f g inputs siblings]
  rfl
#print axioms shape084
def input085 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash085.message
def value085 : State := JFp_SHADigest.output JGy_Gr_M2.Hash085.result
theorem cast085_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash085.B00.input).map Fin.val=JGy_Gr_M2.Hash085.B00.input := by rfl
#print axioms cast085_0
theorem tail085 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash085.tail).map Fin.val=JGy_Gr_M2.Hash085.tail := by rfl
#print axioms tail085
theorem numeric085 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash085.message).map Fin.val=JGy_Gr_M2.Hash085.message := by
  simp only [JGy_Gr_M2.Hash085.message,JGy_Gr_M2.Hash085.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast085_0,tail085]
#print axioms numeric085
theorem hash085 : JFp_SHADigest.digest input085=value085 := by
  unfold input085 JFp_SHADigest.digest
  rw [numeric085,JGy_Gr_M2.Hash085.checked]
  rfl
#print axioms hash085
theorem address085 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [86,120,3,16,14,90,106,11,180,182,86,253,48,54,60,51,178,176,131,60,37,248,185,4,109,125,236,97,241,128,96,4]) value075)=input085 := by rfl
#print axioms address085
def tree085 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [86,120,3,16,14,90,106,11,180,182,86,253,48,54,60,51,178,176,131,60,37,248,185,4,109,125,236,97,241,128,96,4])) tree075
theorem root085 : root JFp_SHADigest.digest tree085=value085 := by
  rw [tree085,root,root075]
  exact (congrArg JFp_SHADigest.digest address085).trans hash085
#print axioms root085
theorem shape085 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 47872=tree085 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 47872)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 7 47872 (by decide),siblings 7 (by decide) 47872 (by decide)]
  rw [shape075 f g inputs siblings]
  rfl
#print axioms shape085
def input086 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash086.message
def value086 : State := JFp_SHADigest.output JGy_Gr_M2.Hash086.result
theorem cast086_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash086.B00.input).map Fin.val=JGy_Gr_M2.Hash086.B00.input := by rfl
#print axioms cast086_0
theorem tail086 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash086.tail).map Fin.val=JGy_Gr_M2.Hash086.tail := by rfl
#print axioms tail086
theorem numeric086 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash086.message).map Fin.val=JGy_Gr_M2.Hash086.message := by
  simp only [JGy_Gr_M2.Hash086.message,JGy_Gr_M2.Hash086.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast086_0,tail086]
#print axioms numeric086
theorem hash086 : JFp_SHADigest.digest input086=value086 := by
  unfold input086 JFp_SHADigest.digest
  rw [numeric086,JGy_Gr_M2.Hash086.checked]
  rfl
#print axioms hash086
theorem address086 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [220,66,240,11,224,86,73,210,202,251,58,129,19,14,221,86,179,240,73,49,122,95,40,107,25,132,18,187,64,22,193,243]) value076)=input086 := by rfl
#print axioms address086
def tree086 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [220,66,240,11,224,86,73,210,202,251,58,129,19,14,221,86,179,240,73,49,122,95,40,107,25,132,18,187,64,22,193,243])) tree076
theorem root086 : root JFp_SHADigest.digest tree086=value086 := by
  rw [tree086,root,root076]
  exact (congrArg JFp_SHADigest.digest address086).trans hash086
#print axioms root086
theorem shape086 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 48128=tree086 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 48128)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 7 48128 (by decide),siblings 7 (by decide) 48128 (by decide)]
  rw [shape076 f g inputs siblings]
  rfl
#print axioms shape086
def input087 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash087.message
def value087 : State := JFp_SHADigest.output JGy_Gr_M2.Hash087.result
theorem cast087_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash087.B00.input).map Fin.val=JGy_Gr_M2.Hash087.B00.input := by rfl
#print axioms cast087_0
theorem tail087 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash087.tail).map Fin.val=JGy_Gr_M2.Hash087.tail := by rfl
#print axioms tail087
theorem numeric087 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash087.message).map Fin.val=JGy_Gr_M2.Hash087.message := by
  simp only [JGy_Gr_M2.Hash087.message,JGy_Gr_M2.Hash087.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast087_0,tail087]
#print axioms numeric087
theorem hash087 : JFp_SHADigest.digest input087=value087 := by
  unfold input087 JFp_SHADigest.digest
  rw [numeric087,JGy_Gr_M2.Hash087.checked]
  rfl
#print axioms hash087
theorem address087 : BinMerkle32Path.nodeInput (children value077 (JGc_TX2_HashBytes.state [238,251,240,139,222,162,82,13,5,62,14,101,72,222,153,31,136,216,181,124,9,170,18,210,98,111,201,200,121,154,149,146]))=input087 := by rfl
#print axioms address087
def tree087 : Tree := .branch tree077 (.supplied (JGc_TX2_HashBytes.state [238,251,240,139,222,162,82,13,5,62,14,101,72,222,153,31,136,216,181,124,9,170,18,210,98,111,201,200,121,154,149,146]))
theorem root087 : root JFp_SHADigest.digest tree087=value087 := by
  rw [tree087,root,root077]
  exact (congrArg JFp_SHADigest.digest address087).trans hash087
#print axioms root087
theorem shape087 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 52224=tree087 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 52224)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape077 f g inputs siblings]
  rw [unoccupied f g 7 52352 (by decide),siblings 7 (by decide) 52352 (by decide)]
  rfl
#print axioms shape087
def input088 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash088.message
def value088 : State := JFp_SHADigest.output JGy_Gr_M2.Hash088.result
theorem cast088_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash088.B00.input).map Fin.val=JGy_Gr_M2.Hash088.B00.input := by rfl
#print axioms cast088_0
theorem tail088 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash088.tail).map Fin.val=JGy_Gr_M2.Hash088.tail := by rfl
#print axioms tail088
theorem numeric088 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash088.message).map Fin.val=JGy_Gr_M2.Hash088.message := by
  simp only [JGy_Gr_M2.Hash088.message,JGy_Gr_M2.Hash088.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast088_0,tail088]
#print axioms numeric088
theorem hash088 : JFp_SHADigest.digest input088=value088 := by
  unfold input088 JFp_SHADigest.digest
  rw [numeric088,JGy_Gr_M2.Hash088.checked]
  rfl
#print axioms hash088
theorem address088 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [84,69,130,187,250,41,60,93,211,73,58,43,46,132,20,190,44,37,46,171,236,6,109,126,126,222,174,144,62,90,134,121]) value078)=input088 := by rfl
#print axioms address088
def tree088 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [84,69,130,187,250,41,60,93,211,73,58,43,46,132,20,190,44,37,46,171,236,6,109,126,126,222,174,144,62,90,134,121])) tree078
theorem root088 : root JFp_SHADigest.digest tree088=value088 := by
  rw [tree088,root,root078]
  exact (congrArg JFp_SHADigest.digest address088).trans hash088
#print axioms root088
theorem shape088 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 54016=tree088 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 54016)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 7 54016 (by decide),siblings 7 (by decide) 54016 (by decide)]
  rw [shape078 f g inputs siblings]
  rfl
#print axioms shape088
def input089 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash089.message
def value089 : State := JFp_SHADigest.output JGy_Gr_M2.Hash089.result
theorem cast089_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash089.B00.input).map Fin.val=JGy_Gr_M2.Hash089.B00.input := by rfl
#print axioms cast089_0
theorem tail089 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash089.tail).map Fin.val=JGy_Gr_M2.Hash089.tail := by rfl
#print axioms tail089
theorem numeric089 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash089.message).map Fin.val=JGy_Gr_M2.Hash089.message := by
  simp only [JGy_Gr_M2.Hash089.message,JGy_Gr_M2.Hash089.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast089_0,tail089]
#print axioms numeric089
theorem hash089 : JFp_SHADigest.digest input089=value089 := by
  unfold input089 JFp_SHADigest.digest
  rw [numeric089,JGy_Gr_M2.Hash089.checked]
  rfl
#print axioms hash089
theorem address089 : BinMerkle32Path.nodeInput (children value079 (JGc_TX2_HashBytes.state [220,229,124,220,129,225,225,51,200,62,80,161,62,80,246,77,79,81,125,59,117,195,120,42,167,10,86,19,49,243,144,77]))=input089 := by rfl
#print axioms address089
def tree089 : Tree := .branch tree079 (.supplied (JGc_TX2_HashBytes.state [220,229,124,220,129,225,225,51,200,62,80,161,62,80,246,77,79,81,125,59,117,195,120,42,167,10,86,19,49,243,144,77]))
theorem root089 : root JFp_SHADigest.digest tree089=value089 := by
  rw [tree089,root,root079]
  exact (congrArg JFp_SHADigest.digest address089).trans hash089
#print axioms root089
theorem shape089 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 8 61440=tree089 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 8 61440)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape079 f g inputs siblings]
  rw [unoccupied f g 7 61568 (by decide),siblings 7 (by decide) 61568 (by decide)]
  rfl
#print axioms shape089
end AspisR1.JGy_Gr_M2Roots
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGy_Gr_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input090 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash090.message
def value090 : State := JFp_SHADigest.output JGy_Gr_M2.Hash090.result
theorem cast090_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash090.B00.input).map Fin.val=JGy_Gr_M2.Hash090.B00.input := by rfl
#print axioms cast090_0
theorem tail090 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash090.tail).map Fin.val=JGy_Gr_M2.Hash090.tail := by rfl
#print axioms tail090
theorem numeric090 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash090.message).map Fin.val=JGy_Gr_M2.Hash090.message := by
  simp only [JGy_Gr_M2.Hash090.message,JGy_Gr_M2.Hash090.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast090_0,tail090]
#print axioms numeric090
theorem hash090 : JFp_SHADigest.digest input090=value090 := by
  unfold input090 JFp_SHADigest.digest
  rw [numeric090,JGy_Gr_M2.Hash090.checked]
  rfl
#print axioms hash090
theorem address090 : BinMerkle32Path.nodeInput (children value080 (JGc_TX2_HashBytes.state [129,139,196,209,161,57,255,18,26,252,18,30,104,179,146,146,53,230,56,126,7,69,243,43,190,141,29,119,242,28,130,38]))=input090 := by rfl
#print axioms address090
def tree090 : Tree := .branch tree080 (.supplied (JGc_TX2_HashBytes.state [129,139,196,209,161,57,255,18,26,252,18,30,104,179,146,146,53,230,56,126,7,69,243,43,190,141,29,119,242,28,130,38]))
theorem root090 : root JFp_SHADigest.digest tree090=value090 := by
  rw [tree090,root,root080]
  exact (congrArg JFp_SHADigest.digest address090).trans hash090
#print axioms root090
theorem shape090 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 16384=tree090 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 16384)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape080 f g inputs siblings]
  rw [unoccupied f g 8 16640 (by decide),siblings 8 (by decide) 16640 (by decide)]
  rfl
#print axioms shape090
def input091 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash091.message
def value091 : State := JFp_SHADigest.output JGy_Gr_M2.Hash091.result
theorem cast091_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash091.B00.input).map Fin.val=JGy_Gr_M2.Hash091.B00.input := by rfl
#print axioms cast091_0
theorem tail091 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash091.tail).map Fin.val=JGy_Gr_M2.Hash091.tail := by rfl
#print axioms tail091
theorem numeric091 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash091.message).map Fin.val=JGy_Gr_M2.Hash091.message := by
  simp only [JGy_Gr_M2.Hash091.message,JGy_Gr_M2.Hash091.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast091_0,tail091]
#print axioms numeric091
theorem hash091 : JFp_SHADigest.digest input091=value091 := by
  unfold input091 JFp_SHADigest.digest
  rw [numeric091,JGy_Gr_M2.Hash091.checked]
  rfl
#print axioms hash091
theorem address091 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [117,171,13,240,245,18,102,9,11,246,84,158,171,240,2,164,240,189,242,95,184,129,172,128,21,241,222,68,41,84,235,244]) value081)=input091 := by rfl
#print axioms address091
def tree091 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [117,171,13,240,245,18,102,9,11,246,84,158,171,240,2,164,240,189,242,95,184,129,172,128,21,241,222,68,41,84,235,244])) tree081
theorem root091 : root JFp_SHADigest.digest tree091=value091 := by
  rw [tree091,root,root081]
  exact (congrArg JFp_SHADigest.digest address091).trans hash091
#print axioms root091
theorem shape091 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 23040=tree091 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 23040)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 23040 (by decide),siblings 8 (by decide) 23040 (by decide)]
  rw [shape081 f g inputs siblings]
  rfl
#print axioms shape091
def input092 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash092.message
def value092 : State := JFp_SHADigest.output JGy_Gr_M2.Hash092.result
theorem cast092_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash092.B00.input).map Fin.val=JGy_Gr_M2.Hash092.B00.input := by rfl
#print axioms cast092_0
theorem tail092 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash092.tail).map Fin.val=JGy_Gr_M2.Hash092.tail := by rfl
#print axioms tail092
theorem numeric092 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash092.message).map Fin.val=JGy_Gr_M2.Hash092.message := by
  simp only [JGy_Gr_M2.Hash092.message,JGy_Gr_M2.Hash092.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast092_0,tail092]
#print axioms numeric092
theorem hash092 : JFp_SHADigest.digest input092=value092 := by
  unfold input092 JFp_SHADigest.digest
  rw [numeric092,JGy_Gr_M2.Hash092.checked]
  rfl
#print axioms hash092
theorem address092 : BinMerkle32Path.nodeInput (children value082 (JGc_TX2_HashBytes.state [112,189,186,141,150,13,115,120,9,52,169,201,97,163,116,115,235,94,1,206,49,158,11,31,22,195,133,0,144,140,158,171]))=input092 := by rfl
#print axioms address092
def tree092 : Tree := .branch tree082 (.supplied (JGc_TX2_HashBytes.state [112,189,186,141,150,13,115,120,9,52,169,201,97,163,116,115,235,94,1,206,49,158,11,31,22,195,133,0,144,140,158,171]))
theorem root092 : root JFp_SHADigest.digest tree092=value092 := by
  rw [tree092,root,root082]
  exact (congrArg JFp_SHADigest.digest address092).trans hash092
#print axioms root092
theorem shape092 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 36864=tree092 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 36864)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape082 f g inputs siblings]
  rw [unoccupied f g 8 37120 (by decide),siblings 8 (by decide) 37120 (by decide)]
  rfl
#print axioms shape092
def input093 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash093.message
def value093 : State := JFp_SHADigest.output JGy_Gr_M2.Hash093.result
theorem cast093_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash093.B00.input).map Fin.val=JGy_Gr_M2.Hash093.B00.input := by rfl
#print axioms cast093_0
theorem tail093 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash093.tail).map Fin.val=JGy_Gr_M2.Hash093.tail := by rfl
#print axioms tail093
theorem numeric093 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash093.message).map Fin.val=JGy_Gr_M2.Hash093.message := by
  simp only [JGy_Gr_M2.Hash093.message,JGy_Gr_M2.Hash093.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast093_0,tail093]
#print axioms numeric093
theorem hash093 : JFp_SHADigest.digest input093=value093 := by
  unfold input093 JFp_SHADigest.digest
  rw [numeric093,JGy_Gr_M2.Hash093.checked]
  rfl
#print axioms hash093
theorem address093 : BinMerkle32Path.nodeInput (children value083 (JGc_TX2_HashBytes.state [65,26,79,118,1,189,37,99,244,25,130,70,240,70,77,82,137,79,54,72,155,62,165,187,17,76,147,69,84,119,4,194]))=input093 := by rfl
#print axioms address093
def tree093 : Tree := .branch tree083 (.supplied (JGc_TX2_HashBytes.state [65,26,79,118,1,189,37,99,244,25,130,70,240,70,77,82,137,79,54,72,155,62,165,187,17,76,147,69,84,119,4,194]))
theorem root093 : root JFp_SHADigest.digest tree093=value093 := by
  rw [tree093,root,root083]
  exact (congrArg JFp_SHADigest.digest address093).trans hash093
#print axioms root093
theorem shape093 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 39936=tree093 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 39936)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape083 f g inputs siblings]
  rw [unoccupied f g 8 40192 (by decide),siblings 8 (by decide) 40192 (by decide)]
  rfl
#print axioms shape093
def input094 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash094.message
def value094 : State := JFp_SHADigest.output JGy_Gr_M2.Hash094.result
theorem cast094_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash094.B00.input).map Fin.val=JGy_Gr_M2.Hash094.B00.input := by rfl
#print axioms cast094_0
theorem tail094 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash094.tail).map Fin.val=JGy_Gr_M2.Hash094.tail := by rfl
#print axioms tail094
theorem numeric094 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash094.message).map Fin.val=JGy_Gr_M2.Hash094.message := by
  simp only [JGy_Gr_M2.Hash094.message,JGy_Gr_M2.Hash094.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast094_0,tail094]
#print axioms numeric094
theorem hash094 : JFp_SHADigest.digest input094=value094 := by
  unfold input094 JFp_SHADigest.digest
  rw [numeric094,JGy_Gr_M2.Hash094.checked]
  rfl
#print axioms hash094
theorem address094 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [5,50,44,127,47,107,97,24,250,118,48,94,115,31,165,104,79,252,110,153,14,168,101,168,252,13,13,176,5,235,11,81]) value084)=input094 := by rfl
#print axioms address094
def tree094 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [5,50,44,127,47,107,97,24,250,118,48,94,115,31,165,104,79,252,110,153,14,168,101,168,252,13,13,176,5,235,11,81])) tree084
theorem root094 : root JFp_SHADigest.digest tree094=value094 := by
  rw [tree094,root,root084]
  exact (congrArg JFp_SHADigest.digest address094).trans hash094
#print axioms root094
theorem shape094 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 45568=tree094 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 45568)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 45568 (by decide),siblings 8 (by decide) 45568 (by decide)]
  rw [shape084 f g inputs siblings]
  rfl
#print axioms shape094
def input095 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash095.message
def value095 : State := JFp_SHADigest.output JGy_Gr_M2.Hash095.result
theorem cast095_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash095.B00.input).map Fin.val=JGy_Gr_M2.Hash095.B00.input := by rfl
#print axioms cast095_0
theorem tail095 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash095.tail).map Fin.val=JGy_Gr_M2.Hash095.tail := by rfl
#print axioms tail095
theorem numeric095 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash095.message).map Fin.val=JGy_Gr_M2.Hash095.message := by
  simp only [JGy_Gr_M2.Hash095.message,JGy_Gr_M2.Hash095.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast095_0,tail095]
#print axioms numeric095
theorem hash095 : JFp_SHADigest.digest input095=value095 := by
  unfold input095 JFp_SHADigest.digest
  rw [numeric095,JGy_Gr_M2.Hash095.checked]
  rfl
#print axioms hash095
theorem address095 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [146,141,221,94,160,176,42,173,76,178,63,145,211,201,232,196,75,136,193,192,49,187,63,18,243,80,211,155,61,26,74,208]) value085)=input095 := by rfl
#print axioms address095
def tree095 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [146,141,221,94,160,176,42,173,76,178,63,145,211,201,232,196,75,136,193,192,49,187,63,18,243,80,211,155,61,26,74,208])) tree085
theorem root095 : root JFp_SHADigest.digest tree095=value095 := by
  rw [tree095,root,root085]
  exact (congrArg JFp_SHADigest.digest address095).trans hash095
#print axioms root095
theorem shape095 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 47616=tree095 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 47616)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 47616 (by decide),siblings 8 (by decide) 47616 (by decide)]
  rw [shape085 f g inputs siblings]
  rfl
#print axioms shape095
def input096 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash096.message
def value096 : State := JFp_SHADigest.output JGy_Gr_M2.Hash096.result
theorem cast096_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash096.B00.input).map Fin.val=JGy_Gr_M2.Hash096.B00.input := by rfl
#print axioms cast096_0
theorem tail096 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash096.tail).map Fin.val=JGy_Gr_M2.Hash096.tail := by rfl
#print axioms tail096
theorem numeric096 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash096.message).map Fin.val=JGy_Gr_M2.Hash096.message := by
  simp only [JGy_Gr_M2.Hash096.message,JGy_Gr_M2.Hash096.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast096_0,tail096]
#print axioms numeric096
theorem hash096 : JFp_SHADigest.digest input096=value096 := by
  unfold input096 JFp_SHADigest.digest
  rw [numeric096,JGy_Gr_M2.Hash096.checked]
  rfl
#print axioms hash096
theorem address096 : BinMerkle32Path.nodeInput (children value086 (JGc_TX2_HashBytes.state [58,139,189,211,146,54,137,210,150,131,78,126,15,71,120,13,201,90,22,49,210,172,123,254,222,83,204,237,128,27,176,200]))=input096 := by rfl
#print axioms address096
def tree096 : Tree := .branch tree086 (.supplied (JGc_TX2_HashBytes.state [58,139,189,211,146,54,137,210,150,131,78,126,15,71,120,13,201,90,22,49,210,172,123,254,222,83,204,237,128,27,176,200]))
theorem root096 : root JFp_SHADigest.digest tree096=value096 := by
  rw [tree096,root,root086]
  exact (congrArg JFp_SHADigest.digest address096).trans hash096
#print axioms root096
theorem shape096 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 48128=tree096 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 48128)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape086 f g inputs siblings]
  rw [unoccupied f g 8 48384 (by decide),siblings 8 (by decide) 48384 (by decide)]
  rfl
#print axioms shape096
def input097 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash097.message
def value097 : State := JFp_SHADigest.output JGy_Gr_M2.Hash097.result
theorem cast097_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash097.B00.input).map Fin.val=JGy_Gr_M2.Hash097.B00.input := by rfl
#print axioms cast097_0
theorem tail097 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash097.tail).map Fin.val=JGy_Gr_M2.Hash097.tail := by rfl
#print axioms tail097
theorem numeric097 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash097.message).map Fin.val=JGy_Gr_M2.Hash097.message := by
  simp only [JGy_Gr_M2.Hash097.message,JGy_Gr_M2.Hash097.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast097_0,tail097]
#print axioms numeric097
theorem hash097 : JFp_SHADigest.digest input097=value097 := by
  unfold input097 JFp_SHADigest.digest
  rw [numeric097,JGy_Gr_M2.Hash097.checked]
  rfl
#print axioms hash097
theorem address097 : BinMerkle32Path.nodeInput (children value087 (JGc_TX2_HashBytes.state [154,56,13,62,76,194,157,36,143,253,24,180,172,172,162,80,108,195,243,117,154,221,90,53,117,255,176,94,77,196,103,105]))=input097 := by rfl
#print axioms address097
def tree097 : Tree := .branch tree087 (.supplied (JGc_TX2_HashBytes.state [154,56,13,62,76,194,157,36,143,253,24,180,172,172,162,80,108,195,243,117,154,221,90,53,117,255,176,94,77,196,103,105]))
theorem root097 : root JFp_SHADigest.digest tree097=value097 := by
  rw [tree097,root,root087]
  exact (congrArg JFp_SHADigest.digest address097).trans hash097
#print axioms root097
theorem shape097 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 52224=tree097 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 52224)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape087 f g inputs siblings]
  rw [unoccupied f g 8 52480 (by decide),siblings 8 (by decide) 52480 (by decide)]
  rfl
#print axioms shape097
def input098 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash098.message
def value098 : State := JFp_SHADigest.output JGy_Gr_M2.Hash098.result
theorem cast098_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash098.B00.input).map Fin.val=JGy_Gr_M2.Hash098.B00.input := by rfl
#print axioms cast098_0
theorem tail098 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash098.tail).map Fin.val=JGy_Gr_M2.Hash098.tail := by rfl
#print axioms tail098
theorem numeric098 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash098.message).map Fin.val=JGy_Gr_M2.Hash098.message := by
  simp only [JGy_Gr_M2.Hash098.message,JGy_Gr_M2.Hash098.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast098_0,tail098]
#print axioms numeric098
theorem hash098 : JFp_SHADigest.digest input098=value098 := by
  unfold input098 JFp_SHADigest.digest
  rw [numeric098,JGy_Gr_M2.Hash098.checked]
  rfl
#print axioms hash098
theorem address098 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [83,238,52,1,11,212,139,234,45,234,168,167,214,33,22,250,35,179,143,118,209,205,200,109,206,127,81,82,170,12,47,46]) value088)=input098 := by rfl
#print axioms address098
def tree098 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [83,238,52,1,11,212,139,234,45,234,168,167,214,33,22,250,35,179,143,118,209,205,200,109,206,127,81,82,170,12,47,46])) tree088
theorem root098 : root JFp_SHADigest.digest tree098=value098 := by
  rw [tree098,root,root088]
  exact (congrArg JFp_SHADigest.digest address098).trans hash098
#print axioms root098
theorem shape098 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 53760=tree098 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 53760)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 8 53760 (by decide),siblings 8 (by decide) 53760 (by decide)]
  rw [shape088 f g inputs siblings]
  rfl
#print axioms shape098
def input099 : Bytes := JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash099.message
def value099 : State := JFp_SHADigest.output JGy_Gr_M2.Hash099.result
theorem cast099_0 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash099.B00.input).map Fin.val=JGy_Gr_M2.Hash099.B00.input := by rfl
#print axioms cast099_0
theorem tail099 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash099.tail).map Fin.val=JGy_Gr_M2.Hash099.tail := by rfl
#print axioms tail099
theorem numeric099 : (JGc_TX2_HashBytes.bytes JGy_Gr_M2.Hash099.message).map Fin.val=JGy_Gr_M2.Hash099.message := by
  simp only [JGy_Gr_M2.Hash099.message,JGy_Gr_M2.Hash099.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast099_0,tail099]
#print axioms numeric099
theorem hash099 : JFp_SHADigest.digest input099=value099 := by
  unfold input099 JFp_SHADigest.digest
  rw [numeric099,JGy_Gr_M2.Hash099.checked]
  rfl
#print axioms hash099
theorem address099 : BinMerkle32Path.nodeInput (children value089 (JGc_TX2_HashBytes.state [241,181,167,150,78,64,96,175,242,182,206,109,16,199,77,118,205,21,203,47,68,204,83,194,143,140,213,34,148,113,119,188]))=input099 := by rfl
#print axioms address099
def tree099 : Tree := .branch tree089 (.supplied (JGc_TX2_HashBytes.state [241,181,167,150,78,64,96,175,242,182,206,109,16,199,77,118,205,21,203,47,68,204,83,194,143,140,213,34,148,113,119,188]))
theorem root099 : root JFp_SHADigest.digest tree099=value099 := by
  rw [tree099,root,root089]
  exact (congrArg JFp_SHADigest.digest address099).trans hash099
#print axioms root099
theorem shape099 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 9 61440=tree099 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 9 61440)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape089 f g inputs siblings]
  rw [unoccupied f g 8 61696 (by decide),siblings 8 (by decide) 61696 (by decide)]
  rfl
#print axioms shape099
end AspisR1.JGy_Gr_M2Roots
end
