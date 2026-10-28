import NDO_JGh_TX2_M1Leaves
import NDO_JGf_TX2_M1W004
import NDO_JGf_TX2_M1W005
import NDO_JGf_TX2_M1W006
import NDO_JGf_TX2_M1W007
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input012 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash012.message
def value012 : State := JFp_SHADigest.output JGf_TX2_M1.Hash012.result
theorem cast012_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash012.B00.input).map Fin.val=JGf_TX2_M1.Hash012.B00.input := by rfl
#print axioms cast012_0
theorem tail012 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash012.tail).map Fin.val=JGf_TX2_M1.Hash012.tail := by rfl
#print axioms tail012
theorem numeric012 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash012.message).map Fin.val=JGf_TX2_M1.Hash012.message := by
  simp only [JGf_TX2_M1.Hash012.message,JGf_TX2_M1.Hash012.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast012_0,tail012]
#print axioms numeric012
theorem hash012 : JFp_SHADigest.digest input012=value012 := by
  unfold input012 JFp_SHADigest.digest
  rw [numeric012,JGf_TX2_M1.Hash012.checked]
  rfl
#print axioms hash012
theorem address012 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [85,144,91,2,235,197,103,66,51,60,174,166,181,175,71,13,223,205,150,116,30,144,96,28,14,109,80,202,123,27,160,65]) value011)=input012 := by rfl
#print axioms address012
def tree012 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [85,144,91,2,235,197,103,66,51,60,174,166,181,175,71,13,223,205,150,116,30,144,96,28,14,109,80,202,123,27,160,65])) tree011
theorem root012 : root JFp_SHADigest.digest tree012=value012 := by
  rw [tree012,root,root011]
  exact (congrArg JFp_SHADigest.digest address012).trans hash012
#print axioms root012
theorem shape012 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 14296=tree012 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 14296)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 14296 (by decide),siblings 0 (by decide) 14296 (by decide)]
  rw [shape011 f g inputs siblings]
  rfl
#print axioms shape012
def input013 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash013.message
def value013 : State := JFp_SHADigest.output JGf_TX2_M1.Hash013.result
theorem cast013_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash013.B00.input).map Fin.val=JGf_TX2_M1.Hash013.B00.input := by rfl
#print axioms cast013_0
theorem tail013 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash013.tail).map Fin.val=JGf_TX2_M1.Hash013.tail := by rfl
#print axioms tail013
theorem numeric013 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash013.message).map Fin.val=JGf_TX2_M1.Hash013.message := by
  simp only [JGf_TX2_M1.Hash013.message,JGf_TX2_M1.Hash013.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast013_0,tail013]
#print axioms numeric013
theorem hash013 : JFp_SHADigest.digest input013=value013 := by
  unfold input013 JFp_SHADigest.digest
  rw [numeric013,JGf_TX2_M1.Hash013.checked]
  rfl
#print axioms hash013
theorem address013 : BinMerkle32Path.nodeInput (children value007 (JGc_TX2_HashBytes.state [149,13,90,51,150,41,51,244,252,177,230,155,168,175,140,211,78,82,178,150,84,185,68,233,36,77,141,203,84,230,147,225]))=input013 := by rfl
#print axioms address013
def tree013 : Tree := .branch tree007 (.supplied (JGc_TX2_HashBytes.state [149,13,90,51,150,41,51,244,252,177,230,155,168,175,140,211,78,82,178,150,84,185,68,233,36,77,141,203,84,230,147,225]))
theorem root013 : root JFp_SHADigest.digest tree013=value013 := by
  rw [tree013,root,root007]
  exact (congrArg JFp_SHADigest.digest address013).trans hash013
#print axioms root013
theorem shape013 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 21248=tree013 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 21248)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape007 f g inputs siblings]
  rw [unoccupied f g 0 21249 (by decide),siblings 0 (by decide) 21249 (by decide)]
  rfl
#print axioms shape013
def input014 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash014.message
def value014 : State := JFp_SHADigest.output JGf_TX2_M1.Hash014.result
theorem cast014_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash014.B00.input).map Fin.val=JGf_TX2_M1.Hash014.B00.input := by rfl
#print axioms cast014_0
theorem tail014 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash014.tail).map Fin.val=JGf_TX2_M1.Hash014.tail := by rfl
#print axioms tail014
theorem numeric014 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash014.message).map Fin.val=JGf_TX2_M1.Hash014.message := by
  simp only [JGf_TX2_M1.Hash014.message,JGf_TX2_M1.Hash014.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast014_0,tail014]
#print axioms numeric014
theorem hash014 : JFp_SHADigest.digest input014=value014 := by
  unfold input014 JFp_SHADigest.digest
  rw [numeric014,JGf_TX2_M1.Hash014.checked]
  rfl
#print axioms hash014
theorem address014 : BinMerkle32Path.nodeInput (children value005 (JGc_TX2_HashBytes.state [224,144,132,212,225,224,99,8,111,210,132,110,218,231,238,137,29,57,68,85,95,211,82,225,161,111,6,155,34,106,212,26]))=input014 := by rfl
#print axioms address014
def tree014 : Tree := .branch tree005 (.supplied (JGc_TX2_HashBytes.state [224,144,132,212,225,224,99,8,111,210,132,110,218,231,238,137,29,57,68,85,95,211,82,225,161,111,6,155,34,106,212,26]))
theorem root014 : root JFp_SHADigest.digest tree014=value014 := by
  rw [tree014,root,root005]
  exact (congrArg JFp_SHADigest.digest address014).trans hash014
#print axioms root014
theorem shape014 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 42158=tree014 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 42158)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape005 f g inputs siblings]
  rw [unoccupied f g 0 42159 (by decide),siblings 0 (by decide) 42159 (by decide)]
  rfl
#print axioms shape014
def input015 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash015.message
def value015 : State := JFp_SHADigest.output JGf_TX2_M1.Hash015.result
theorem cast015_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash015.B00.input).map Fin.val=JGf_TX2_M1.Hash015.B00.input := by rfl
#print axioms cast015_0
theorem tail015 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash015.tail).map Fin.val=JGf_TX2_M1.Hash015.tail := by rfl
#print axioms tail015
theorem numeric015 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash015.message).map Fin.val=JGf_TX2_M1.Hash015.message := by
  simp only [JGf_TX2_M1.Hash015.message,JGf_TX2_M1.Hash015.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast015_0,tail015]
#print axioms numeric015
theorem hash015 : JFp_SHADigest.digest input015=value015 := by
  unfold input015 JFp_SHADigest.digest
  rw [numeric015,JGf_TX2_M1.Hash015.checked]
  rfl
#print axioms hash015
theorem address015 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [232,117,91,224,183,62,86,67,216,228,135,232,145,180,30,213,201,219,112,52,8,112,194,249,30,166,102,198,118,58,69,125]) value009)=input015 := by rfl
#print axioms address015
def tree015 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [232,117,91,224,183,62,86,67,216,228,135,232,145,180,30,213,201,219,112,52,8,112,194,249,30,166,102,198,118,58,69,125])) tree009
theorem root015 : root JFp_SHADigest.digest tree015=value015 := by
  rw [tree015,root,root009]
  exact (congrArg JFp_SHADigest.digest address015).trans hash015
#print axioms root015
theorem shape015 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 55376=tree015 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 55376)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 55376 (by decide),siblings 0 (by decide) 55376 (by decide)]
  rw [shape009 f g inputs siblings]
  rfl
#print axioms shape015
def input016 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash016.message
def value016 : State := JFp_SHADigest.output JGf_TX2_M1.Hash016.result
theorem cast016_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash016.B00.input).map Fin.val=JGf_TX2_M1.Hash016.B00.input := by rfl
#print axioms cast016_0
theorem tail016 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash016.tail).map Fin.val=JGf_TX2_M1.Hash016.tail := by rfl
#print axioms tail016
theorem numeric016 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash016.message).map Fin.val=JGf_TX2_M1.Hash016.message := by
  simp only [JGf_TX2_M1.Hash016.message,JGf_TX2_M1.Hash016.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast016_0,tail016]
#print axioms numeric016
theorem hash016 : JFp_SHADigest.digest input016=value016 := by
  unfold input016 JFp_SHADigest.digest
  rw [numeric016,JGf_TX2_M1.Hash016.checked]
  rfl
#print axioms hash016
theorem address016 : BinMerkle32Path.nodeInput (children value008 (JGc_TX2_HashBytes.state [226,81,255,181,125,23,114,120,154,194,73,114,71,141,243,161,190,178,65,52,244,2,243,205,37,138,110,43,85,2,146,15]))=input016 := by rfl
#print axioms address016
def tree016 : Tree := .branch tree008 (.supplied (JGc_TX2_HashBytes.state [226,81,255,181,125,23,114,120,154,194,73,114,71,141,243,161,190,178,65,52,244,2,243,205,37,138,110,43,85,2,146,15]))
theorem root016 : root JFp_SHADigest.digest tree016=value016 := by
  rw [tree016,root,root008]
  exact (congrArg JFp_SHADigest.digest address016).trans hash016
#print axioms root016
theorem shape016 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 63860=tree016 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 63860)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape008 f g inputs siblings]
  rw [unoccupied f g 0 63861 (by decide),siblings 0 (by decide) 63861 (by decide)]
  rfl
#print axioms shape016
def input017 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash017.message
def value017 : State := JFp_SHADigest.output JGf_TX2_M1.Hash017.result
theorem cast017_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash017.B00.input).map Fin.val=JGf_TX2_M1.Hash017.B00.input := by rfl
#print axioms cast017_0
theorem tail017 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash017.tail).map Fin.val=JGf_TX2_M1.Hash017.tail := by rfl
#print axioms tail017
theorem numeric017 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash017.message).map Fin.val=JGf_TX2_M1.Hash017.message := by
  simp only [JGf_TX2_M1.Hash017.message,JGf_TX2_M1.Hash017.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast017_0,tail017]
#print axioms numeric017
theorem hash017 : JFp_SHADigest.digest input017=value017 := by
  unfold input017 JFp_SHADigest.digest
  rw [numeric017,JGf_TX2_M1.Hash017.checked]
  rfl
#print axioms hash017
theorem address017 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [232,218,175,178,220,102,209,130,17,254,196,146,81,129,213,31,99,250,20,149,224,141,2,176,15,149,167,145,180,117,156,75]) value000)=input017 := by rfl
#print axioms address017
def tree017 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [232,218,175,178,220,102,209,130,17,254,196,146,81,129,213,31,99,250,20,149,224,141,2,176,15,149,167,145,180,117,156,75])) tree000
theorem root017 : root JFp_SHADigest.digest tree017=value017 := by
  rw [tree017,root,root000]
  exact (congrArg JFp_SHADigest.digest address017).trans hash017
#print axioms root017
theorem shape017 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 132354=tree017 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 132354)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 132354 (by decide),siblings 0 (by decide) 132354 (by decide)]
  rw [shape000 f g inputs siblings]
  rfl
#print axioms shape017
def input018 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash018.message
def value018 : State := JFp_SHADigest.output JGf_TX2_M1.Hash018.result
theorem cast018_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash018.B00.input).map Fin.val=JGf_TX2_M1.Hash018.B00.input := by rfl
#print axioms cast018_0
theorem tail018 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash018.tail).map Fin.val=JGf_TX2_M1.Hash018.tail := by rfl
#print axioms tail018
theorem numeric018 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash018.message).map Fin.val=JGf_TX2_M1.Hash018.message := by
  simp only [JGf_TX2_M1.Hash018.message,JGf_TX2_M1.Hash018.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast018_0,tail018]
#print axioms numeric018
theorem hash018 : JFp_SHADigest.digest input018=value018 := by
  unfold input018 JFp_SHADigest.digest
  rw [numeric018,JGf_TX2_M1.Hash018.checked]
  rfl
#print axioms hash018
theorem address018 : BinMerkle32Path.nodeInput (children value003 (JGc_TX2_HashBytes.state [159,21,140,88,105,171,13,247,159,60,230,244,184,79,136,184,67,72,142,187,167,203,86,10,207,174,155,232,57,27,5,17]))=input018 := by rfl
#print axioms address018
def tree018 : Tree := .branch tree003 (.supplied (JGc_TX2_HashBytes.state [159,21,140,88,105,171,13,247,159,60,230,244,184,79,136,184,67,72,142,187,167,203,86,10,207,174,155,232,57,27,5,17]))
theorem root018 : root JFp_SHADigest.digest tree018=value018 := by
  rw [tree018,root,root003]
  exact (congrArg JFp_SHADigest.digest address018).trans hash018
#print axioms root018
theorem shape018 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 149624=tree018 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 149624)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape003 f g inputs siblings]
  rw [unoccupied f g 0 149625 (by decide),siblings 0 (by decide) 149625 (by decide)]
  rfl
#print axioms shape018
def input019 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash019.message
def value019 : State := JFp_SHADigest.output JGf_TX2_M1.Hash019.result
theorem cast019_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash019.B00.input).map Fin.val=JGf_TX2_M1.Hash019.B00.input := by rfl
#print axioms cast019_0
theorem tail019 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash019.tail).map Fin.val=JGf_TX2_M1.Hash019.tail := by rfl
#print axioms tail019
theorem numeric019 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash019.message).map Fin.val=JGf_TX2_M1.Hash019.message := by
  simp only [JGf_TX2_M1.Hash019.message,JGf_TX2_M1.Hash019.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast019_0,tail019]
#print axioms numeric019
theorem hash019 : JFp_SHADigest.digest input019=value019 := by
  unfold input019 JFp_SHADigest.digest
  rw [numeric019,JGf_TX2_M1.Hash019.checked]
  rfl
#print axioms hash019
theorem address019 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [34,186,246,47,83,202,131,21,57,208,217,199,30,181,171,77,97,75,188,20,207,46,138,240,247,156,23,222,61,35,60,214]) value004)=input019 := by rfl
#print axioms address019
def tree019 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [34,186,246,47,83,202,131,21,57,208,217,199,30,181,171,77,97,75,188,20,207,46,138,240,247,156,23,222,61,35,60,214])) tree004
theorem root019 : root JFp_SHADigest.digest tree019=value019 := by
  rw [tree019,root,root004]
  exact (congrArg JFp_SHADigest.digest address019).trans hash019
#print axioms root019
theorem shape019 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 166164=tree019 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 166164)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 166164 (by decide),siblings 0 (by decide) 166164 (by decide)]
  rw [shape004 f g inputs siblings]
  rfl
#print axioms shape019
def input020 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash020.message
def value020 : State := JFp_SHADigest.output JGf_TX2_M1.Hash020.result
theorem cast020_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash020.B00.input).map Fin.val=JGf_TX2_M1.Hash020.B00.input := by rfl
#print axioms cast020_0
theorem tail020 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash020.tail).map Fin.val=JGf_TX2_M1.Hash020.tail := by rfl
#print axioms tail020
theorem numeric020 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash020.message).map Fin.val=JGf_TX2_M1.Hash020.message := by
  simp only [JGf_TX2_M1.Hash020.message,JGf_TX2_M1.Hash020.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast020_0,tail020]
#print axioms numeric020
theorem hash020 : JFp_SHADigest.digest input020=value020 := by
  unfold input020 JFp_SHADigest.digest
  rw [numeric020,JGf_TX2_M1.Hash020.checked]
  rfl
#print axioms hash020
theorem address020 : BinMerkle32Path.nodeInput (children value002 (JGc_TX2_HashBytes.state [179,223,163,234,48,23,197,79,198,53,18,64,196,131,189,62,222,137,153,209,166,90,156,57,237,223,203,93,196,234,114,152]))=input020 := by rfl
#print axioms address020
def tree020 : Tree := .branch tree002 (.supplied (JGc_TX2_HashBytes.state [179,223,163,234,48,23,197,79,198,53,18,64,196,131,189,62,222,137,153,209,166,90,156,57,237,223,203,93,196,234,114,152]))
theorem root020 : root JFp_SHADigest.digest tree020=value020 := by
  rw [tree020,root,root002]
  exact (congrArg JFp_SHADigest.digest address020).trans hash020
#print axioms root020
theorem shape020 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 178080=tree020 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 178080)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape002 f g inputs siblings]
  rw [unoccupied f g 0 178081 (by decide),siblings 0 (by decide) 178081 (by decide)]
  rfl
#print axioms shape020
def input021 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash021.message
def value021 : State := JFp_SHADigest.output JGf_TX2_M1.Hash021.result
theorem cast021_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash021.B00.input).map Fin.val=JGf_TX2_M1.Hash021.B00.input := by rfl
#print axioms cast021_0
theorem tail021 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash021.tail).map Fin.val=JGf_TX2_M1.Hash021.tail := by rfl
#print axioms tail021
theorem numeric021 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash021.message).map Fin.val=JGf_TX2_M1.Hash021.message := by
  simp only [JGf_TX2_M1.Hash021.message,JGf_TX2_M1.Hash021.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast021_0,tail021]
#print axioms numeric021
theorem hash021 : JFp_SHADigest.digest input021=value021 := by
  unfold input021 JFp_SHADigest.digest
  rw [numeric021,JGf_TX2_M1.Hash021.checked]
  rfl
#print axioms hash021
theorem address021 : BinMerkle32Path.nodeInput (children value006 (JGc_TX2_HashBytes.state [16,201,98,42,217,180,193,62,50,45,197,179,229,246,60,193,10,149,152,147,211,17,208,86,134,25,85,151,113,180,40,44]))=input021 := by rfl
#print axioms address021
def tree021 : Tree := .branch tree006 (.supplied (JGc_TX2_HashBytes.state [16,201,98,42,217,180,193,62,50,45,197,179,229,246,60,193,10,149,152,147,211,17,208,86,134,25,85,151,113,180,40,44]))
theorem root021 : root JFp_SHADigest.digest tree021=value021 := by
  rw [tree021,root,root006]
  exact (congrArg JFp_SHADigest.digest address021).trans hash021
#print axioms root021
theorem shape021 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 179622=tree021 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 179622)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape006 f g inputs siblings]
  rw [unoccupied f g 0 179623 (by decide),siblings 0 (by decide) 179623 (by decide)]
  rfl
#print axioms shape021
def input022 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash022.message
def value022 : State := JFp_SHADigest.output JGf_TX2_M1.Hash022.result
theorem cast022_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash022.B00.input).map Fin.val=JGf_TX2_M1.Hash022.B00.input := by rfl
#print axioms cast022_0
theorem tail022 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash022.tail).map Fin.val=JGf_TX2_M1.Hash022.tail := by rfl
#print axioms tail022
theorem numeric022 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash022.message).map Fin.val=JGf_TX2_M1.Hash022.message := by
  simp only [JGf_TX2_M1.Hash022.message,JGf_TX2_M1.Hash022.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast022_0,tail022]
#print axioms numeric022
theorem hash022 : JFp_SHADigest.digest input022=value022 := by
  unfold input022 JFp_SHADigest.digest
  rw [numeric022,JGf_TX2_M1.Hash022.checked]
  rfl
#print axioms hash022
theorem address022 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [96,56,13,209,41,6,60,135,83,208,126,60,234,131,233,1,255,248,5,10,214,43,67,200,182,171,54,176,54,113,174,213]) value010)=input022 := by rfl
#print axioms address022
def tree022 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [96,56,13,209,41,6,60,135,83,208,126,60,234,131,233,1,255,248,5,10,214,43,67,200,182,171,54,176,54,113,174,213])) tree010
theorem root022 : root JFp_SHADigest.digest tree022=value022 := by
  rw [tree022,root,root010]
  exact (congrArg JFp_SHADigest.digest address022).trans hash022
#print axioms root022
theorem shape022 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 185636=tree022 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 185636)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [unoccupied f g 0 185636 (by decide),siblings 0 (by decide) 185636 (by decide)]
  rw [shape010 f g inputs siblings]
  rfl
#print axioms shape022
def input023 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash023.message
def value023 : State := JFp_SHADigest.output JGf_TX2_M1.Hash023.result
theorem cast023_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash023.B00.input).map Fin.val=JGf_TX2_M1.Hash023.B00.input := by rfl
#print axioms cast023_0
theorem tail023 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash023.tail).map Fin.val=JGf_TX2_M1.Hash023.tail := by rfl
#print axioms tail023
theorem numeric023 : (JGc_TX2_HashBytes.bytes JGf_TX2_M1.Hash023.message).map Fin.val=JGf_TX2_M1.Hash023.message := by
  simp only [JGf_TX2_M1.Hash023.message,JGf_TX2_M1.Hash023.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast023_0,tail023]
#print axioms numeric023
theorem hash023 : JFp_SHADigest.digest input023=value023 := by
  unfold input023 JFp_SHADigest.digest
  rw [numeric023,JGf_TX2_M1.Hash023.checked]
  rfl
#print axioms hash023
theorem address023 : BinMerkle32Path.nodeInput (children value001 (JGc_TX2_HashBytes.state [28,243,229,146,24,70,89,119,248,161,25,29,238,111,230,52,67,191,127,184,7,237,245,50,78,221,13,165,220,212,138,220]))=input023 := by rfl
#print axioms address023
def tree023 : Tree := .branch tree001 (.supplied (JGc_TX2_HashBytes.state [28,243,229,146,24,70,89,119,248,161,25,29,238,111,230,52,67,191,127,184,7,237,245,50,78,221,13,165,220,212,138,220]))
theorem root023 : root JFp_SHADigest.digest tree023=value023 := by
  rw [tree023,root,root001]
  exact (congrArg JFp_SHADigest.digest address023).trans hash023
#print axioms root023
theorem shape023 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 1 218094=tree023 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 1 218094)]
  simp only [Nat.reducePow,Nat.reduceAdd]
  rw [shape001 f g inputs siblings]
  rw [unoccupied f g 0 218095 (by decide),siblings 0 (by decide) 218095 (by decide)]
  rfl
#print axioms shape023
end AspisR1.JGh_TX2_M1Roots
end
