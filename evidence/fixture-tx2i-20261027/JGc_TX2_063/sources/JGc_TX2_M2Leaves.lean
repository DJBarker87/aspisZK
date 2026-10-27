import JGc_TX2_M2H000
import JGc_TX2_M2H002
import JGc_TX2_M2H004
import JGc_TX2_M2H006
import JGc_TX2_M2H008
import JGc_TX2_M2H010
import JGc_TX2_HashBytes
import JGc_TX2_M2Layout
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input000 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash000.message
def value000 : State := JFp_SHADigest.output JGc_TX2_M2.Hash000.result
theorem canonical000 : ∀ n∈JGc_TX2_M2.Hash000.message,n<256 := by
  simp [JGc_TX2_M2.Hash000.message,JGc_TX2_M2.Hash000.head,JGc_TX2_M2.Hash000.B00.input,JGc_TX2_M2.Hash000.B01.input,JGc_TX2_M2.Hash000.tail]
#print axioms canonical000
theorem hash000 : JFp_SHADigest.digest input000=value000 := by
  unfold input000 JFp_SHADigest.digest
  rw [JGc_TX2_HashBytes.numeric _ canonical000,JGc_TX2_M2.Hash000.checked]
#print axioms hash000
def tree000 : Tree := .opened input000
theorem root000 : root JFp_SHADigest.digest tree000=value000 := hash000
#print axioms root000
def input001 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash001.message
def value001 : State := JFp_SHADigest.output JGc_TX2_M2.Hash001.result
theorem canonical001 : ∀ n∈JGc_TX2_M2.Hash001.message,n<256 := by
  simp [JGc_TX2_M2.Hash001.message,JGc_TX2_M2.Hash001.head,JGc_TX2_M2.Hash001.B00.input,JGc_TX2_M2.Hash001.B01.input,JGc_TX2_M2.Hash001.tail]
#print axioms canonical001
theorem hash001 : JFp_SHADigest.digest input001=value001 := by
  unfold input001 JFp_SHADigest.digest
  rw [JGc_TX2_HashBytes.numeric _ canonical001,JGc_TX2_M2.Hash001.checked]
#print axioms hash001
def tree001 : Tree := .opened input001
theorem root001 : root JFp_SHADigest.digest tree001=value001 := hash001
#print axioms root001
def input002 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash002.message
def value002 : State := JFp_SHADigest.output JGc_TX2_M2.Hash002.result
theorem canonical002 : ∀ n∈JGc_TX2_M2.Hash002.message,n<256 := by
  simp [JGc_TX2_M2.Hash002.message,JGc_TX2_M2.Hash002.head,JGc_TX2_M2.Hash002.B00.input,JGc_TX2_M2.Hash002.B01.input,JGc_TX2_M2.Hash002.tail]
#print axioms canonical002
theorem hash002 : JFp_SHADigest.digest input002=value002 := by
  unfold input002 JFp_SHADigest.digest
  rw [JGc_TX2_HashBytes.numeric _ canonical002,JGc_TX2_M2.Hash002.checked]
#print axioms hash002
def tree002 : Tree := .opened input002
theorem root002 : root JFp_SHADigest.digest tree002=value002 := hash002
#print axioms root002
def input003 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash003.message
def value003 : State := JFp_SHADigest.output JGc_TX2_M2.Hash003.result
theorem canonical003 : ∀ n∈JGc_TX2_M2.Hash003.message,n<256 := by
  simp [JGc_TX2_M2.Hash003.message,JGc_TX2_M2.Hash003.head,JGc_TX2_M2.Hash003.B00.input,JGc_TX2_M2.Hash003.B01.input,JGc_TX2_M2.Hash003.tail]
#print axioms canonical003
theorem hash003 : JFp_SHADigest.digest input003=value003 := by
  unfold input003 JFp_SHADigest.digest
  rw [JGc_TX2_HashBytes.numeric _ canonical003,JGc_TX2_M2.Hash003.checked]
#print axioms hash003
def tree003 : Tree := .opened input003
theorem root003 : root JFp_SHADigest.digest tree003=value003 := hash003
#print axioms root003
def input004 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash004.message
def value004 : State := JFp_SHADigest.output JGc_TX2_M2.Hash004.result
theorem canonical004 : ∀ n∈JGc_TX2_M2.Hash004.message,n<256 := by
  simp [JGc_TX2_M2.Hash004.message,JGc_TX2_M2.Hash004.head,JGc_TX2_M2.Hash004.B00.input,JGc_TX2_M2.Hash004.B01.input,JGc_TX2_M2.Hash004.tail]
#print axioms canonical004
theorem hash004 : JFp_SHADigest.digest input004=value004 := by
  unfold input004 JFp_SHADigest.digest
  rw [JGc_TX2_HashBytes.numeric _ canonical004,JGc_TX2_M2.Hash004.checked]
#print axioms hash004
def tree004 : Tree := .opened input004
theorem root004 : root JFp_SHADigest.digest tree004=value004 := hash004
#print axioms root004
def input005 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash005.message
def value005 : State := JFp_SHADigest.output JGc_TX2_M2.Hash005.result
theorem canonical005 : ∀ n∈JGc_TX2_M2.Hash005.message,n<256 := by
  simp [JGc_TX2_M2.Hash005.message,JGc_TX2_M2.Hash005.head,JGc_TX2_M2.Hash005.B00.input,JGc_TX2_M2.Hash005.B01.input,JGc_TX2_M2.Hash005.tail]
#print axioms canonical005
theorem hash005 : JFp_SHADigest.digest input005=value005 := by
  unfold input005 JFp_SHADigest.digest
  rw [JGc_TX2_HashBytes.numeric _ canonical005,JGc_TX2_M2.Hash005.checked]
#print axioms hash005
def tree005 : Tree := .opened input005
theorem root005 : root JFp_SHADigest.digest tree005=value005 := hash005
#print axioms root005
def input006 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash006.message
def value006 : State := JFp_SHADigest.output JGc_TX2_M2.Hash006.result
theorem canonical006 : ∀ n∈JGc_TX2_M2.Hash006.message,n<256 := by
  simp [JGc_TX2_M2.Hash006.message,JGc_TX2_M2.Hash006.head,JGc_TX2_M2.Hash006.B00.input,JGc_TX2_M2.Hash006.B01.input,JGc_TX2_M2.Hash006.tail]
#print axioms canonical006
theorem hash006 : JFp_SHADigest.digest input006=value006 := by
  unfold input006 JFp_SHADigest.digest
  rw [JGc_TX2_HashBytes.numeric _ canonical006,JGc_TX2_M2.Hash006.checked]
#print axioms hash006
def tree006 : Tree := .opened input006
theorem root006 : root JFp_SHADigest.digest tree006=value006 := hash006
#print axioms root006
def input007 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash007.message
def value007 : State := JFp_SHADigest.output JGc_TX2_M2.Hash007.result
theorem canonical007 : ∀ n∈JGc_TX2_M2.Hash007.message,n<256 := by
  simp [JGc_TX2_M2.Hash007.message,JGc_TX2_M2.Hash007.head,JGc_TX2_M2.Hash007.B00.input,JGc_TX2_M2.Hash007.B01.input,JGc_TX2_M2.Hash007.tail]
#print axioms canonical007
theorem hash007 : JFp_SHADigest.digest input007=value007 := by
  unfold input007 JFp_SHADigest.digest
  rw [JGc_TX2_HashBytes.numeric _ canonical007,JGc_TX2_M2.Hash007.checked]
#print axioms hash007
def tree007 : Tree := .opened input007
theorem root007 : root JFp_SHADigest.digest tree007=value007 := hash007
#print axioms root007
def input008 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash008.message
def value008 : State := JFp_SHADigest.output JGc_TX2_M2.Hash008.result
theorem canonical008 : ∀ n∈JGc_TX2_M2.Hash008.message,n<256 := by
  simp [JGc_TX2_M2.Hash008.message,JGc_TX2_M2.Hash008.head,JGc_TX2_M2.Hash008.B00.input,JGc_TX2_M2.Hash008.B01.input,JGc_TX2_M2.Hash008.tail]
#print axioms canonical008
theorem hash008 : JFp_SHADigest.digest input008=value008 := by
  unfold input008 JFp_SHADigest.digest
  rw [JGc_TX2_HashBytes.numeric _ canonical008,JGc_TX2_M2.Hash008.checked]
#print axioms hash008
def tree008 : Tree := .opened input008
theorem root008 : root JFp_SHADigest.digest tree008=value008 := hash008
#print axioms root008
def input009 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash009.message
def value009 : State := JFp_SHADigest.output JGc_TX2_M2.Hash009.result
theorem canonical009 : ∀ n∈JGc_TX2_M2.Hash009.message,n<256 := by
  simp [JGc_TX2_M2.Hash009.message,JGc_TX2_M2.Hash009.head,JGc_TX2_M2.Hash009.B00.input,JGc_TX2_M2.Hash009.B01.input,JGc_TX2_M2.Hash009.tail]
#print axioms canonical009
theorem hash009 : JFp_SHADigest.digest input009=value009 := by
  unfold input009 JFp_SHADigest.digest
  rw [JGc_TX2_HashBytes.numeric _ canonical009,JGc_TX2_M2.Hash009.checked]
#print axioms hash009
def tree009 : Tree := .opened input009
theorem root009 : root JFp_SHADigest.digest tree009=value009 := hash009
#print axioms root009
def input010 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash010.message
def value010 : State := JFp_SHADigest.output JGc_TX2_M2.Hash010.result
theorem canonical010 : ∀ n∈JGc_TX2_M2.Hash010.message,n<256 := by
  simp [JGc_TX2_M2.Hash010.message,JGc_TX2_M2.Hash010.head,JGc_TX2_M2.Hash010.B00.input,JGc_TX2_M2.Hash010.B01.input,JGc_TX2_M2.Hash010.tail]
#print axioms canonical010
theorem hash010 : JFp_SHADigest.digest input010=value010 := by
  unfold input010 JFp_SHADigest.digest
  rw [JGc_TX2_HashBytes.numeric _ canonical010,JGc_TX2_M2.Hash010.checked]
#print axioms hash010
def tree010 : Tree := .opened input010
theorem root010 : root JFp_SHADigest.digest tree010=value010 := hash010
#print axioms root010
def input011 : Bytes := JGc_TX2_HashBytes.bytes JGc_TX2_M2.Hash011.message
def value011 : State := JFp_SHADigest.output JGc_TX2_M2.Hash011.result
theorem canonical011 : ∀ n∈JGc_TX2_M2.Hash011.message,n<256 := by
  simp [JGc_TX2_M2.Hash011.message,JGc_TX2_M2.Hash011.head,JGc_TX2_M2.Hash011.B00.input,JGc_TX2_M2.Hash011.B01.input,JGc_TX2_M2.Hash011.tail]
#print axioms canonical011
theorem hash011 : JFp_SHADigest.digest input011=value011 := by
  unfold input011 JFp_SHADigest.digest
  rw [JGc_TX2_HashBytes.numeric _ canonical011,JGc_TX2_M2.Hash011.checked]
#print axioms hash011
def tree011 : Tree := .opened input011
theorem root011 : root JFp_SHADigest.digest tree011=value011 := hash011
#print axioms root011
def inputAt (base : Nat) : Bytes := match base with
  | 33088 => input000
  | 54523 => input001
  | 44520 => input002
  | 37406 => input003
  | 41541 => input004
  | 10539 => input005
  | 44905 => input006
  | 5312 => input007
  | 15965 => input008
  | 13844 => input009
  | 46409 => input010
  | 3574 => input011
  | _ => []
def InputLaw (f : Nat → Bytes) : Prop := ∀ b,b∈indices → f b=inputAt b
theorem shape000 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 33088=tree000 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 33088),inputs 33088 (by decide)]
  rfl
#print axioms shape000
theorem shape001 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 54523=tree001 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 54523),inputs 54523 (by decide)]
  rfl
#print axioms shape001
theorem shape002 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 44520=tree002 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 44520),inputs 44520 (by decide)]
  rfl
#print axioms shape002
theorem shape003 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 37406=tree003 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 37406),inputs 37406 (by decide)]
  rfl
#print axioms shape003
theorem shape004 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 41541=tree004 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 41541),inputs 41541 (by decide)]
  rfl
#print axioms shape004
theorem shape005 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 10539=tree005 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 10539),inputs 10539 (by decide)]
  rfl
#print axioms shape005
theorem shape006 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 44905=tree006 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 44905),inputs 44905 (by decide)]
  rfl
#print axioms shape006
theorem shape007 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 5312=tree007 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 5312),inputs 5312 (by decide)]
  rfl
#print axioms shape007
theorem shape008 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 15965=tree008 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 15965),inputs 15965 (by decide)]
  rfl
#print axioms shape008
theorem shape009 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 13844=tree009 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 13844),inputs 13844 (by decide)]
  rfl
#print axioms shape009
theorem shape010 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 46409=tree010 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 46409),inputs 46409 (by decide)]
  rfl
#print axioms shape010
theorem shape011 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 3574=tree011 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 3574),inputs 3574 (by decide)]
  rfl
#print axioms shape011
end AspisR1.JGc_TX2_M2Roots
end
