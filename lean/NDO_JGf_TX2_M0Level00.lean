import NDO_JGf_TX2_M0Leaves
import NDO_JGf_TX2_M0W013
import NDO_JGf_TX2_M0W014
import NDO_JGf_TX2_M0W015
import NDO_JGf_TX2_M0W016
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGf_TX2_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input012 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash012.message
def value012 : State := JFp_SHADigest.output JGf_TX2_M0.Hash012.result
theorem cast012_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash012.B00.input).map Fin.val=JGf_TX2_M0.Hash012.B00.input := by rfl
#print axioms cast012_0
theorem tail012 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash012.tail).map Fin.val=JGf_TX2_M0.Hash012.tail := by rfl
#print axioms tail012
theorem numeric012 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash012.message).map Fin.val=JGf_TX2_M0.Hash012.message := by
  simp only [JGf_TX2_M0.Hash012.message,JGf_TX2_M0.Hash012.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast012_0,tail012]
#print axioms numeric012
theorem hash012 : JFp_SHADigest.digest input012=value012 := by
  unfold input012 JFp_SHADigest.digest
  rw [numeric012,JGf_TX2_M0.Hash012.checked]
  rfl
#print axioms hash012
theorem address012 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [189,248,141,229,232,239,254,233,229,242,34,143,253,180,238,215,115,247,158,182,28,222,73,110,160,168,132,92,222,91,14,30]) value011)=input012 := by rfl
#print axioms address012
def tree012 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [189,248,141,229,232,239,254,233,229,242,34,143,253,180,238,215,115,247,158,182,28,222,73,110,160,168,132,92,222,91,14,30])) tree011
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
def input013 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash013.message
def value013 : State := JFp_SHADigest.output JGf_TX2_M0.Hash013.result
theorem cast013_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash013.B00.input).map Fin.val=JGf_TX2_M0.Hash013.B00.input := by rfl
#print axioms cast013_0
theorem tail013 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash013.tail).map Fin.val=JGf_TX2_M0.Hash013.tail := by rfl
#print axioms tail013
theorem numeric013 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash013.message).map Fin.val=JGf_TX2_M0.Hash013.message := by
  simp only [JGf_TX2_M0.Hash013.message,JGf_TX2_M0.Hash013.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast013_0,tail013]
#print axioms numeric013
theorem hash013 : JFp_SHADigest.digest input013=value013 := by
  unfold input013 JFp_SHADigest.digest
  rw [numeric013,JGf_TX2_M0.Hash013.checked]
  rfl
#print axioms hash013
theorem address013 : BinMerkle32Path.nodeInput (children value007 (JGc_TX2_HashBytes.state [121,251,34,151,204,248,189,232,20,144,172,120,239,171,47,41,7,192,54,227,25,167,11,30,34,111,33,147,122,105,95,91]))=input013 := by rfl
#print axioms address013
def tree013 : Tree := .branch tree007 (.supplied (JGc_TX2_HashBytes.state [121,251,34,151,204,248,189,232,20,144,172,120,239,171,47,41,7,192,54,227,25,167,11,30,34,111,33,147,122,105,95,91]))
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
def input014 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash014.message
def value014 : State := JFp_SHADigest.output JGf_TX2_M0.Hash014.result
theorem cast014_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash014.B00.input).map Fin.val=JGf_TX2_M0.Hash014.B00.input := by rfl
#print axioms cast014_0
theorem tail014 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash014.tail).map Fin.val=JGf_TX2_M0.Hash014.tail := by rfl
#print axioms tail014
theorem numeric014 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash014.message).map Fin.val=JGf_TX2_M0.Hash014.message := by
  simp only [JGf_TX2_M0.Hash014.message,JGf_TX2_M0.Hash014.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast014_0,tail014]
#print axioms numeric014
theorem hash014 : JFp_SHADigest.digest input014=value014 := by
  unfold input014 JFp_SHADigest.digest
  rw [numeric014,JGf_TX2_M0.Hash014.checked]
  rfl
#print axioms hash014
theorem address014 : BinMerkle32Path.nodeInput (children value005 (JGc_TX2_HashBytes.state [226,24,141,171,213,169,205,223,209,245,68,62,123,75,40,22,136,93,163,56,171,160,93,15,187,179,86,223,148,88,54,255]))=input014 := by rfl
#print axioms address014
def tree014 : Tree := .branch tree005 (.supplied (JGc_TX2_HashBytes.state [226,24,141,171,213,169,205,223,209,245,68,62,123,75,40,22,136,93,163,56,171,160,93,15,187,179,86,223,148,88,54,255]))
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
def input015 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash015.message
def value015 : State := JFp_SHADigest.output JGf_TX2_M0.Hash015.result
theorem cast015_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash015.B00.input).map Fin.val=JGf_TX2_M0.Hash015.B00.input := by rfl
#print axioms cast015_0
theorem tail015 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash015.tail).map Fin.val=JGf_TX2_M0.Hash015.tail := by rfl
#print axioms tail015
theorem numeric015 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash015.message).map Fin.val=JGf_TX2_M0.Hash015.message := by
  simp only [JGf_TX2_M0.Hash015.message,JGf_TX2_M0.Hash015.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast015_0,tail015]
#print axioms numeric015
theorem hash015 : JFp_SHADigest.digest input015=value015 := by
  unfold input015 JFp_SHADigest.digest
  rw [numeric015,JGf_TX2_M0.Hash015.checked]
  rfl
#print axioms hash015
theorem address015 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [66,118,36,1,40,42,222,116,108,188,8,180,209,56,15,104,188,119,85,230,118,209,32,11,106,203,92,163,143,74,233,8]) value009)=input015 := by rfl
#print axioms address015
def tree015 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [66,118,36,1,40,42,222,116,108,188,8,180,209,56,15,104,188,119,85,230,118,209,32,11,106,203,92,163,143,74,233,8])) tree009
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
def input016 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash016.message
def value016 : State := JFp_SHADigest.output JGf_TX2_M0.Hash016.result
theorem cast016_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash016.B00.input).map Fin.val=JGf_TX2_M0.Hash016.B00.input := by rfl
#print axioms cast016_0
theorem tail016 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash016.tail).map Fin.val=JGf_TX2_M0.Hash016.tail := by rfl
#print axioms tail016
theorem numeric016 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash016.message).map Fin.val=JGf_TX2_M0.Hash016.message := by
  simp only [JGf_TX2_M0.Hash016.message,JGf_TX2_M0.Hash016.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast016_0,tail016]
#print axioms numeric016
theorem hash016 : JFp_SHADigest.digest input016=value016 := by
  unfold input016 JFp_SHADigest.digest
  rw [numeric016,JGf_TX2_M0.Hash016.checked]
  rfl
#print axioms hash016
theorem address016 : BinMerkle32Path.nodeInput (children value008 (JGc_TX2_HashBytes.state [148,155,24,4,233,10,134,242,4,94,86,3,55,144,143,64,21,197,244,8,32,203,169,93,43,249,244,77,12,22,48,232]))=input016 := by rfl
#print axioms address016
def tree016 : Tree := .branch tree008 (.supplied (JGc_TX2_HashBytes.state [148,155,24,4,233,10,134,242,4,94,86,3,55,144,143,64,21,197,244,8,32,203,169,93,43,249,244,77,12,22,48,232]))
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
def input017 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash017.message
def value017 : State := JFp_SHADigest.output JGf_TX2_M0.Hash017.result
theorem cast017_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash017.B00.input).map Fin.val=JGf_TX2_M0.Hash017.B00.input := by rfl
#print axioms cast017_0
theorem tail017 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash017.tail).map Fin.val=JGf_TX2_M0.Hash017.tail := by rfl
#print axioms tail017
theorem numeric017 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash017.message).map Fin.val=JGf_TX2_M0.Hash017.message := by
  simp only [JGf_TX2_M0.Hash017.message,JGf_TX2_M0.Hash017.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast017_0,tail017]
#print axioms numeric017
theorem hash017 : JFp_SHADigest.digest input017=value017 := by
  unfold input017 JFp_SHADigest.digest
  rw [numeric017,JGf_TX2_M0.Hash017.checked]
  rfl
#print axioms hash017
theorem address017 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [133,81,188,75,67,217,127,245,207,139,14,33,198,21,1,183,88,46,89,97,148,72,10,110,240,165,89,230,110,243,21,149]) value000)=input017 := by rfl
#print axioms address017
def tree017 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [133,81,188,75,67,217,127,245,207,139,14,33,198,21,1,183,88,46,89,97,148,72,10,110,240,165,89,230,110,243,21,149])) tree000
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
def input018 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash018.message
def value018 : State := JFp_SHADigest.output JGf_TX2_M0.Hash018.result
theorem cast018_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash018.B00.input).map Fin.val=JGf_TX2_M0.Hash018.B00.input := by rfl
#print axioms cast018_0
theorem tail018 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash018.tail).map Fin.val=JGf_TX2_M0.Hash018.tail := by rfl
#print axioms tail018
theorem numeric018 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash018.message).map Fin.val=JGf_TX2_M0.Hash018.message := by
  simp only [JGf_TX2_M0.Hash018.message,JGf_TX2_M0.Hash018.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast018_0,tail018]
#print axioms numeric018
theorem hash018 : JFp_SHADigest.digest input018=value018 := by
  unfold input018 JFp_SHADigest.digest
  rw [numeric018,JGf_TX2_M0.Hash018.checked]
  rfl
#print axioms hash018
theorem address018 : BinMerkle32Path.nodeInput (children value003 (JGc_TX2_HashBytes.state [154,30,211,64,221,253,33,44,222,183,203,129,137,147,202,30,36,187,246,13,210,34,93,124,10,83,51,167,148,141,26,0]))=input018 := by rfl
#print axioms address018
def tree018 : Tree := .branch tree003 (.supplied (JGc_TX2_HashBytes.state [154,30,211,64,221,253,33,44,222,183,203,129,137,147,202,30,36,187,246,13,210,34,93,124,10,83,51,167,148,141,26,0]))
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
def input019 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash019.message
def value019 : State := JFp_SHADigest.output JGf_TX2_M0.Hash019.result
theorem cast019_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash019.B00.input).map Fin.val=JGf_TX2_M0.Hash019.B00.input := by rfl
#print axioms cast019_0
theorem tail019 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash019.tail).map Fin.val=JGf_TX2_M0.Hash019.tail := by rfl
#print axioms tail019
theorem numeric019 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash019.message).map Fin.val=JGf_TX2_M0.Hash019.message := by
  simp only [JGf_TX2_M0.Hash019.message,JGf_TX2_M0.Hash019.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast019_0,tail019]
#print axioms numeric019
theorem hash019 : JFp_SHADigest.digest input019=value019 := by
  unfold input019 JFp_SHADigest.digest
  rw [numeric019,JGf_TX2_M0.Hash019.checked]
  rfl
#print axioms hash019
theorem address019 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [32,198,90,69,50,216,55,227,243,115,213,199,174,136,234,163,54,49,47,75,127,15,0,171,207,239,114,238,210,101,243,33]) value004)=input019 := by rfl
#print axioms address019
def tree019 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [32,198,90,69,50,216,55,227,243,115,213,199,174,136,234,163,54,49,47,75,127,15,0,171,207,239,114,238,210,101,243,33])) tree004
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
def input020 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash020.message
def value020 : State := JFp_SHADigest.output JGf_TX2_M0.Hash020.result
theorem cast020_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash020.B00.input).map Fin.val=JGf_TX2_M0.Hash020.B00.input := by rfl
#print axioms cast020_0
theorem tail020 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash020.tail).map Fin.val=JGf_TX2_M0.Hash020.tail := by rfl
#print axioms tail020
theorem numeric020 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash020.message).map Fin.val=JGf_TX2_M0.Hash020.message := by
  simp only [JGf_TX2_M0.Hash020.message,JGf_TX2_M0.Hash020.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast020_0,tail020]
#print axioms numeric020
theorem hash020 : JFp_SHADigest.digest input020=value020 := by
  unfold input020 JFp_SHADigest.digest
  rw [numeric020,JGf_TX2_M0.Hash020.checked]
  rfl
#print axioms hash020
theorem address020 : BinMerkle32Path.nodeInput (children value002 (JGc_TX2_HashBytes.state [234,103,151,200,111,92,71,73,125,108,96,37,87,158,96,155,23,104,213,245,190,48,225,244,170,117,145,136,249,7,136,43]))=input020 := by rfl
#print axioms address020
def tree020 : Tree := .branch tree002 (.supplied (JGc_TX2_HashBytes.state [234,103,151,200,111,92,71,73,125,108,96,37,87,158,96,155,23,104,213,245,190,48,225,244,170,117,145,136,249,7,136,43]))
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
def input021 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash021.message
def value021 : State := JFp_SHADigest.output JGf_TX2_M0.Hash021.result
theorem cast021_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash021.B00.input).map Fin.val=JGf_TX2_M0.Hash021.B00.input := by rfl
#print axioms cast021_0
theorem tail021 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash021.tail).map Fin.val=JGf_TX2_M0.Hash021.tail := by rfl
#print axioms tail021
theorem numeric021 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash021.message).map Fin.val=JGf_TX2_M0.Hash021.message := by
  simp only [JGf_TX2_M0.Hash021.message,JGf_TX2_M0.Hash021.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast021_0,tail021]
#print axioms numeric021
theorem hash021 : JFp_SHADigest.digest input021=value021 := by
  unfold input021 JFp_SHADigest.digest
  rw [numeric021,JGf_TX2_M0.Hash021.checked]
  rfl
#print axioms hash021
theorem address021 : BinMerkle32Path.nodeInput (children value006 (JGc_TX2_HashBytes.state [73,139,26,79,32,250,87,38,215,58,56,39,115,73,199,106,78,78,252,70,254,176,53,155,125,59,121,74,189,238,228,73]))=input021 := by rfl
#print axioms address021
def tree021 : Tree := .branch tree006 (.supplied (JGc_TX2_HashBytes.state [73,139,26,79,32,250,87,38,215,58,56,39,115,73,199,106,78,78,252,70,254,176,53,155,125,59,121,74,189,238,228,73]))
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
def input022 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash022.message
def value022 : State := JFp_SHADigest.output JGf_TX2_M0.Hash022.result
theorem cast022_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash022.B00.input).map Fin.val=JGf_TX2_M0.Hash022.B00.input := by rfl
#print axioms cast022_0
theorem tail022 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash022.tail).map Fin.val=JGf_TX2_M0.Hash022.tail := by rfl
#print axioms tail022
theorem numeric022 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash022.message).map Fin.val=JGf_TX2_M0.Hash022.message := by
  simp only [JGf_TX2_M0.Hash022.message,JGf_TX2_M0.Hash022.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast022_0,tail022]
#print axioms numeric022
theorem hash022 : JFp_SHADigest.digest input022=value022 := by
  unfold input022 JFp_SHADigest.digest
  rw [numeric022,JGf_TX2_M0.Hash022.checked]
  rfl
#print axioms hash022
theorem address022 : BinMerkle32Path.nodeInput (children (JGc_TX2_HashBytes.state [219,235,44,83,194,181,197,200,108,49,49,252,53,227,196,164,245,43,179,245,187,38,84,185,232,200,232,124,197,98,125,188]) value010)=input022 := by rfl
#print axioms address022
def tree022 : Tree := .branch (.supplied (JGc_TX2_HashBytes.state [219,235,44,83,194,181,197,200,108,49,49,252,53,227,196,164,245,43,179,245,187,38,84,185,232,200,232,124,197,98,125,188])) tree010
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
def input023 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash023.message
def value023 : State := JFp_SHADigest.output JGf_TX2_M0.Hash023.result
theorem cast023_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash023.B00.input).map Fin.val=JGf_TX2_M0.Hash023.B00.input := by rfl
#print axioms cast023_0
theorem tail023 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash023.tail).map Fin.val=JGf_TX2_M0.Hash023.tail := by rfl
#print axioms tail023
theorem numeric023 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash023.message).map Fin.val=JGf_TX2_M0.Hash023.message := by
  simp only [JGf_TX2_M0.Hash023.message,JGf_TX2_M0.Hash023.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast023_0,tail023]
#print axioms numeric023
theorem hash023 : JFp_SHADigest.digest input023=value023 := by
  unfold input023 JFp_SHADigest.digest
  rw [numeric023,JGf_TX2_M0.Hash023.checked]
  rfl
#print axioms hash023
theorem address023 : BinMerkle32Path.nodeInput (children value001 (JGc_TX2_HashBytes.state [149,78,203,164,143,37,62,165,229,108,172,236,145,217,217,36,250,242,23,199,180,137,90,249,85,65,225,142,183,54,118,117]))=input023 := by rfl
#print axioms address023
def tree023 : Tree := .branch tree001 (.supplied (JGc_TX2_HashBytes.state [149,78,203,164,143,37,62,165,229,108,172,236,145,217,217,36,250,242,23,199,180,137,90,249,85,65,225,142,183,54,118,117]))
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
end AspisR1.JGf_TX2_M0Roots
end
