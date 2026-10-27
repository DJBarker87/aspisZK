import JGr_M1C000
import JGr_M1C000
import JGr_M1C000
import JGr_M1C000
import JGr_M1C001
import JGr_M1C001
import JGr_M1C001
import JGr_M1C001
import JGr_M1C002
import JGr_M1C002
import JGc_TX2_ByteAppend
import JGc_TX2_HashBytes
import JGr_M1Layout
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGr_M1Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input000 : Bytes := JGc_TX2_HashBytes.bytes JGr_M1.Hash000.message
def value000 : State := JFp_SHADigest.output JGr_M1.Hash000.result
theorem cast000_0 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash000.B00.input).map Fin.val=JGr_M1.Hash000.B00.input := by rfl
#print axioms cast000_0
theorem cast000_1 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash000.B01.input).map Fin.val=JGr_M1.Hash000.B01.input := by rfl
#print axioms cast000_1
theorem tail000 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash000.tail).map Fin.val=JGr_M1.Hash000.tail := by rfl
#print axioms tail000
theorem numeric000 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash000.message).map Fin.val=JGr_M1.Hash000.message := by
  simp only [JGr_M1.Hash000.message,JGr_M1.Hash000.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast000_0,cast000_1,tail000]
#print axioms numeric000
theorem hash000 : JFp_SHADigest.digest input000=value000 := by
  unfold input000 JFp_SHADigest.digest
  rw [numeric000,JGr_M1.Hash000.checked]
  rfl
#print axioms hash000
def tree000 : Tree := .opened input000
theorem root000 : root JFp_SHADigest.digest tree000=value000 := hash000
#print axioms root000
def input001 : Bytes := JGc_TX2_HashBytes.bytes JGr_M1.Hash001.message
def value001 : State := JFp_SHADigest.output JGr_M1.Hash001.result
theorem cast001_0 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash001.B00.input).map Fin.val=JGr_M1.Hash001.B00.input := by rfl
#print axioms cast001_0
theorem cast001_1 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash001.B01.input).map Fin.val=JGr_M1.Hash001.B01.input := by rfl
#print axioms cast001_1
theorem tail001 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash001.tail).map Fin.val=JGr_M1.Hash001.tail := by rfl
#print axioms tail001
theorem numeric001 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash001.message).map Fin.val=JGr_M1.Hash001.message := by
  simp only [JGr_M1.Hash001.message,JGr_M1.Hash001.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast001_0,cast001_1,tail001]
#print axioms numeric001
theorem hash001 : JFp_SHADigest.digest input001=value001 := by
  unfold input001 JFp_SHADigest.digest
  rw [numeric001,JGr_M1.Hash001.checked]
  rfl
#print axioms hash001
def tree001 : Tree := .opened input001
theorem root001 : root JFp_SHADigest.digest tree001=value001 := hash001
#print axioms root001
def input002 : Bytes := JGc_TX2_HashBytes.bytes JGr_M1.Hash002.message
def value002 : State := JFp_SHADigest.output JGr_M1.Hash002.result
theorem cast002_0 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash002.B00.input).map Fin.val=JGr_M1.Hash002.B00.input := by rfl
#print axioms cast002_0
theorem cast002_1 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash002.B01.input).map Fin.val=JGr_M1.Hash002.B01.input := by rfl
#print axioms cast002_1
theorem tail002 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash002.tail).map Fin.val=JGr_M1.Hash002.tail := by rfl
#print axioms tail002
theorem numeric002 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash002.message).map Fin.val=JGr_M1.Hash002.message := by
  simp only [JGr_M1.Hash002.message,JGr_M1.Hash002.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast002_0,cast002_1,tail002]
#print axioms numeric002
theorem hash002 : JFp_SHADigest.digest input002=value002 := by
  unfold input002 JFp_SHADigest.digest
  rw [numeric002,JGr_M1.Hash002.checked]
  rfl
#print axioms hash002
def tree002 : Tree := .opened input002
theorem root002 : root JFp_SHADigest.digest tree002=value002 := hash002
#print axioms root002
def input003 : Bytes := JGc_TX2_HashBytes.bytes JGr_M1.Hash003.message
def value003 : State := JFp_SHADigest.output JGr_M1.Hash003.result
theorem cast003_0 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash003.B00.input).map Fin.val=JGr_M1.Hash003.B00.input := by rfl
#print axioms cast003_0
theorem cast003_1 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash003.B01.input).map Fin.val=JGr_M1.Hash003.B01.input := by rfl
#print axioms cast003_1
theorem tail003 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash003.tail).map Fin.val=JGr_M1.Hash003.tail := by rfl
#print axioms tail003
theorem numeric003 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash003.message).map Fin.val=JGr_M1.Hash003.message := by
  simp only [JGr_M1.Hash003.message,JGr_M1.Hash003.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast003_0,cast003_1,tail003]
#print axioms numeric003
theorem hash003 : JFp_SHADigest.digest input003=value003 := by
  unfold input003 JFp_SHADigest.digest
  rw [numeric003,JGr_M1.Hash003.checked]
  rfl
#print axioms hash003
def tree003 : Tree := .opened input003
theorem root003 : root JFp_SHADigest.digest tree003=value003 := hash003
#print axioms root003
def input004 : Bytes := JGc_TX2_HashBytes.bytes JGr_M1.Hash004.message
def value004 : State := JFp_SHADigest.output JGr_M1.Hash004.result
theorem cast004_0 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash004.B00.input).map Fin.val=JGr_M1.Hash004.B00.input := by rfl
#print axioms cast004_0
theorem cast004_1 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash004.B01.input).map Fin.val=JGr_M1.Hash004.B01.input := by rfl
#print axioms cast004_1
theorem tail004 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash004.tail).map Fin.val=JGr_M1.Hash004.tail := by rfl
#print axioms tail004
theorem numeric004 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash004.message).map Fin.val=JGr_M1.Hash004.message := by
  simp only [JGr_M1.Hash004.message,JGr_M1.Hash004.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast004_0,cast004_1,tail004]
#print axioms numeric004
theorem hash004 : JFp_SHADigest.digest input004=value004 := by
  unfold input004 JFp_SHADigest.digest
  rw [numeric004,JGr_M1.Hash004.checked]
  rfl
#print axioms hash004
def tree004 : Tree := .opened input004
theorem root004 : root JFp_SHADigest.digest tree004=value004 := hash004
#print axioms root004
def input005 : Bytes := JGc_TX2_HashBytes.bytes JGr_M1.Hash005.message
def value005 : State := JFp_SHADigest.output JGr_M1.Hash005.result
theorem cast005_0 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash005.B00.input).map Fin.val=JGr_M1.Hash005.B00.input := by rfl
#print axioms cast005_0
theorem cast005_1 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash005.B01.input).map Fin.val=JGr_M1.Hash005.B01.input := by rfl
#print axioms cast005_1
theorem tail005 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash005.tail).map Fin.val=JGr_M1.Hash005.tail := by rfl
#print axioms tail005
theorem numeric005 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash005.message).map Fin.val=JGr_M1.Hash005.message := by
  simp only [JGr_M1.Hash005.message,JGr_M1.Hash005.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast005_0,cast005_1,tail005]
#print axioms numeric005
theorem hash005 : JFp_SHADigest.digest input005=value005 := by
  unfold input005 JFp_SHADigest.digest
  rw [numeric005,JGr_M1.Hash005.checked]
  rfl
#print axioms hash005
def tree005 : Tree := .opened input005
theorem root005 : root JFp_SHADigest.digest tree005=value005 := hash005
#print axioms root005
def input006 : Bytes := JGc_TX2_HashBytes.bytes JGr_M1.Hash006.message
def value006 : State := JFp_SHADigest.output JGr_M1.Hash006.result
theorem cast006_0 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash006.B00.input).map Fin.val=JGr_M1.Hash006.B00.input := by rfl
#print axioms cast006_0
theorem cast006_1 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash006.B01.input).map Fin.val=JGr_M1.Hash006.B01.input := by rfl
#print axioms cast006_1
theorem tail006 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash006.tail).map Fin.val=JGr_M1.Hash006.tail := by rfl
#print axioms tail006
theorem numeric006 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash006.message).map Fin.val=JGr_M1.Hash006.message := by
  simp only [JGr_M1.Hash006.message,JGr_M1.Hash006.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast006_0,cast006_1,tail006]
#print axioms numeric006
theorem hash006 : JFp_SHADigest.digest input006=value006 := by
  unfold input006 JFp_SHADigest.digest
  rw [numeric006,JGr_M1.Hash006.checked]
  rfl
#print axioms hash006
def tree006 : Tree := .opened input006
theorem root006 : root JFp_SHADigest.digest tree006=value006 := hash006
#print axioms root006
def input007 : Bytes := JGc_TX2_HashBytes.bytes JGr_M1.Hash007.message
def value007 : State := JFp_SHADigest.output JGr_M1.Hash007.result
theorem cast007_0 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash007.B00.input).map Fin.val=JGr_M1.Hash007.B00.input := by rfl
#print axioms cast007_0
theorem cast007_1 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash007.B01.input).map Fin.val=JGr_M1.Hash007.B01.input := by rfl
#print axioms cast007_1
theorem tail007 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash007.tail).map Fin.val=JGr_M1.Hash007.tail := by rfl
#print axioms tail007
theorem numeric007 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash007.message).map Fin.val=JGr_M1.Hash007.message := by
  simp only [JGr_M1.Hash007.message,JGr_M1.Hash007.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast007_0,cast007_1,tail007]
#print axioms numeric007
theorem hash007 : JFp_SHADigest.digest input007=value007 := by
  unfold input007 JFp_SHADigest.digest
  rw [numeric007,JGr_M1.Hash007.checked]
  rfl
#print axioms hash007
def tree007 : Tree := .opened input007
theorem root007 : root JFp_SHADigest.digest tree007=value007 := hash007
#print axioms root007
def input008 : Bytes := JGc_TX2_HashBytes.bytes JGr_M1.Hash008.message
def value008 : State := JFp_SHADigest.output JGr_M1.Hash008.result
theorem cast008_0 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash008.B00.input).map Fin.val=JGr_M1.Hash008.B00.input := by rfl
#print axioms cast008_0
theorem cast008_1 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash008.B01.input).map Fin.val=JGr_M1.Hash008.B01.input := by rfl
#print axioms cast008_1
theorem tail008 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash008.tail).map Fin.val=JGr_M1.Hash008.tail := by rfl
#print axioms tail008
theorem numeric008 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash008.message).map Fin.val=JGr_M1.Hash008.message := by
  simp only [JGr_M1.Hash008.message,JGr_M1.Hash008.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast008_0,cast008_1,tail008]
#print axioms numeric008
theorem hash008 : JFp_SHADigest.digest input008=value008 := by
  unfold input008 JFp_SHADigest.digest
  rw [numeric008,JGr_M1.Hash008.checked]
  rfl
#print axioms hash008
def tree008 : Tree := .opened input008
theorem root008 : root JFp_SHADigest.digest tree008=value008 := hash008
#print axioms root008
def input009 : Bytes := JGc_TX2_HashBytes.bytes JGr_M1.Hash009.message
def value009 : State := JFp_SHADigest.output JGr_M1.Hash009.result
theorem cast009_0 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash009.B00.input).map Fin.val=JGr_M1.Hash009.B00.input := by rfl
#print axioms cast009_0
theorem cast009_1 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash009.B01.input).map Fin.val=JGr_M1.Hash009.B01.input := by rfl
#print axioms cast009_1
theorem tail009 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash009.tail).map Fin.val=JGr_M1.Hash009.tail := by rfl
#print axioms tail009
theorem numeric009 : (JGc_TX2_HashBytes.bytes JGr_M1.Hash009.message).map Fin.val=JGr_M1.Hash009.message := by
  simp only [JGr_M1.Hash009.message,JGr_M1.Hash009.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast009_0,cast009_1,tail009]
#print axioms numeric009
theorem hash009 : JFp_SHADigest.digest input009=value009 := by
  unfold input009 JFp_SHADigest.digest
  rw [numeric009,JGr_M1.Hash009.checked]
  rfl
#print axioms hash009
def tree009 : Tree := .opened input009
theorem root009 : root JFp_SHADigest.digest tree009=value009 := hash009
#print axioms root009
def inputAt (base : Nat) : Bytes := match base with
  | 93499 => input000
  | 147529 => input001
  | 216823 => input002
  | 245899 => input003
  | 209371 => input004
  | 192317 => input005
  | 65593 => input006
  | 183859 => input007
  | 193093 => input008
  | 159813 => input009
  | _ => []
def InputLaw (f : Nat → Bytes) : Prop := ∀ b,b∈indices → f b=inputAt b
theorem shape000 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 93499=tree000 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 93499),inputs 93499 (by decide)]
  rfl
#print axioms shape000
theorem shape001 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 147529=tree001 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 147529),inputs 147529 (by decide)]
  rfl
#print axioms shape001
theorem shape002 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 216823=tree002 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 216823),inputs 216823 (by decide)]
  rfl
#print axioms shape002
theorem shape003 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 245899=tree003 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 245899),inputs 245899 (by decide)]
  rfl
#print axioms shape003
theorem shape004 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 209371=tree004 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 209371),inputs 209371 (by decide)]
  rfl
#print axioms shape004
theorem shape005 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 192317=tree005 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 192317),inputs 192317 (by decide)]
  rfl
#print axioms shape005
theorem shape006 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 65593=tree006 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 65593),inputs 65593 (by decide)]
  rfl
#print axioms shape006
theorem shape007 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 183859=tree007 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 183859),inputs 183859 (by decide)]
  rfl
#print axioms shape007
theorem shape008 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 193093=tree008 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 193093),inputs 193093 (by decide)]
  rfl
#print axioms shape008
theorem shape009 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 159813=tree009 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 159813),inputs 159813 (by decide)]
  rfl
#print axioms shape009
end AspisR1.JGr_M1Roots
end
