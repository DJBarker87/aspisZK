import NDO_JGf_TX2_M0W001
import NDO_JGf_TX2_M0W002
import NDO_JGf_TX2_M0W003
import NDO_JGf_TX2_M0W004
import NDO_JGf_TX2_M0W005
import NDO_JGf_TX2_M0W006
import NDO_JGf_TX2_M0W007
import NDO_JGf_TX2_M0W008
import NDO_JGf_TX2_M0W010
import NDO_JGf_TX2_M0W011
import NDO_JGf_TX2_M0W012
import NDO_JGf_TX2_M0W013
import NDO_JGc_TX2_ByteAppend
import NDO_JGc_TX2_HashBytes
import NDO_JGf_TX2_M0Layout
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGf_TX2_M0Roots
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiTree
def input000 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash000.message
def value000 : State := JFp_SHADigest.output JGf_TX2_M0.Hash000.result
theorem cast000_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash000.B00.input).map Fin.val=JGf_TX2_M0.Hash000.B00.input := by rfl
#print axioms cast000_0
theorem cast000_1 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash000.B01.input).map Fin.val=JGf_TX2_M0.Hash000.B01.input := by rfl
#print axioms cast000_1
theorem cast000_2 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash000.B02.input).map Fin.val=JGf_TX2_M0.Hash000.B02.input := by rfl
#print axioms cast000_2
theorem cast000_3 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash000.B03.input).map Fin.val=JGf_TX2_M0.Hash000.B03.input := by rfl
#print axioms cast000_3
theorem cast000_4 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash000.B04.input).map Fin.val=JGf_TX2_M0.Hash000.B04.input := by rfl
#print axioms cast000_4
theorem cast000_5 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash000.B05.input).map Fin.val=JGf_TX2_M0.Hash000.B05.input := by rfl
#print axioms cast000_5
theorem cast000_6 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash000.B06.input).map Fin.val=JGf_TX2_M0.Hash000.B06.input := by rfl
#print axioms cast000_6
theorem cast000_7 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash000.B07.input).map Fin.val=JGf_TX2_M0.Hash000.B07.input := by rfl
#print axioms cast000_7
theorem tail000 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash000.tail).map Fin.val=JGf_TX2_M0.Hash000.tail := by rfl
#print axioms tail000
theorem numeric000 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash000.message).map Fin.val=JGf_TX2_M0.Hash000.message := by
  simp only [JGf_TX2_M0.Hash000.message,JGf_TX2_M0.Hash000.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast000_0,cast000_1,cast000_2,cast000_3,cast000_4,cast000_5,cast000_6,cast000_7,tail000]
#print axioms numeric000
theorem hash000 : JFp_SHADigest.digest input000=value000 := by
  unfold input000 JFp_SHADigest.digest
  rw [numeric000,JGf_TX2_M0.Hash000.checked]
  rfl
#print axioms hash000
def tree000 : Tree := .opened input000
theorem root000 : root JFp_SHADigest.digest tree000=value000 := hash000
#print axioms root000
def input001 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash001.message
def value001 : State := JFp_SHADigest.output JGf_TX2_M0.Hash001.result
theorem cast001_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash001.B00.input).map Fin.val=JGf_TX2_M0.Hash001.B00.input := by rfl
#print axioms cast001_0
theorem cast001_1 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash001.B01.input).map Fin.val=JGf_TX2_M0.Hash001.B01.input := by rfl
#print axioms cast001_1
theorem cast001_2 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash001.B02.input).map Fin.val=JGf_TX2_M0.Hash001.B02.input := by rfl
#print axioms cast001_2
theorem cast001_3 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash001.B03.input).map Fin.val=JGf_TX2_M0.Hash001.B03.input := by rfl
#print axioms cast001_3
theorem cast001_4 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash001.B04.input).map Fin.val=JGf_TX2_M0.Hash001.B04.input := by rfl
#print axioms cast001_4
theorem cast001_5 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash001.B05.input).map Fin.val=JGf_TX2_M0.Hash001.B05.input := by rfl
#print axioms cast001_5
theorem cast001_6 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash001.B06.input).map Fin.val=JGf_TX2_M0.Hash001.B06.input := by rfl
#print axioms cast001_6
theorem cast001_7 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash001.B07.input).map Fin.val=JGf_TX2_M0.Hash001.B07.input := by rfl
#print axioms cast001_7
theorem tail001 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash001.tail).map Fin.val=JGf_TX2_M0.Hash001.tail := by rfl
#print axioms tail001
theorem numeric001 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash001.message).map Fin.val=JGf_TX2_M0.Hash001.message := by
  simp only [JGf_TX2_M0.Hash001.message,JGf_TX2_M0.Hash001.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast001_0,cast001_1,cast001_2,cast001_3,cast001_4,cast001_5,cast001_6,cast001_7,tail001]
#print axioms numeric001
theorem hash001 : JFp_SHADigest.digest input001=value001 := by
  unfold input001 JFp_SHADigest.digest
  rw [numeric001,JGf_TX2_M0.Hash001.checked]
  rfl
#print axioms hash001
def tree001 : Tree := .opened input001
theorem root001 : root JFp_SHADigest.digest tree001=value001 := hash001
#print axioms root001
def input002 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash002.message
def value002 : State := JFp_SHADigest.output JGf_TX2_M0.Hash002.result
theorem cast002_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash002.B00.input).map Fin.val=JGf_TX2_M0.Hash002.B00.input := by rfl
#print axioms cast002_0
theorem cast002_1 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash002.B01.input).map Fin.val=JGf_TX2_M0.Hash002.B01.input := by rfl
#print axioms cast002_1
theorem cast002_2 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash002.B02.input).map Fin.val=JGf_TX2_M0.Hash002.B02.input := by rfl
#print axioms cast002_2
theorem cast002_3 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash002.B03.input).map Fin.val=JGf_TX2_M0.Hash002.B03.input := by rfl
#print axioms cast002_3
theorem cast002_4 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash002.B04.input).map Fin.val=JGf_TX2_M0.Hash002.B04.input := by rfl
#print axioms cast002_4
theorem cast002_5 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash002.B05.input).map Fin.val=JGf_TX2_M0.Hash002.B05.input := by rfl
#print axioms cast002_5
theorem cast002_6 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash002.B06.input).map Fin.val=JGf_TX2_M0.Hash002.B06.input := by rfl
#print axioms cast002_6
theorem cast002_7 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash002.B07.input).map Fin.val=JGf_TX2_M0.Hash002.B07.input := by rfl
#print axioms cast002_7
theorem tail002 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash002.tail).map Fin.val=JGf_TX2_M0.Hash002.tail := by rfl
#print axioms tail002
theorem numeric002 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash002.message).map Fin.val=JGf_TX2_M0.Hash002.message := by
  simp only [JGf_TX2_M0.Hash002.message,JGf_TX2_M0.Hash002.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast002_0,cast002_1,cast002_2,cast002_3,cast002_4,cast002_5,cast002_6,cast002_7,tail002]
#print axioms numeric002
theorem hash002 : JFp_SHADigest.digest input002=value002 := by
  unfold input002 JFp_SHADigest.digest
  rw [numeric002,JGf_TX2_M0.Hash002.checked]
  rfl
#print axioms hash002
def tree002 : Tree := .opened input002
theorem root002 : root JFp_SHADigest.digest tree002=value002 := hash002
#print axioms root002
def input003 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash003.message
def value003 : State := JFp_SHADigest.output JGf_TX2_M0.Hash003.result
theorem cast003_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash003.B00.input).map Fin.val=JGf_TX2_M0.Hash003.B00.input := by rfl
#print axioms cast003_0
theorem cast003_1 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash003.B01.input).map Fin.val=JGf_TX2_M0.Hash003.B01.input := by rfl
#print axioms cast003_1
theorem cast003_2 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash003.B02.input).map Fin.val=JGf_TX2_M0.Hash003.B02.input := by rfl
#print axioms cast003_2
theorem cast003_3 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash003.B03.input).map Fin.val=JGf_TX2_M0.Hash003.B03.input := by rfl
#print axioms cast003_3
theorem cast003_4 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash003.B04.input).map Fin.val=JGf_TX2_M0.Hash003.B04.input := by rfl
#print axioms cast003_4
theorem cast003_5 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash003.B05.input).map Fin.val=JGf_TX2_M0.Hash003.B05.input := by rfl
#print axioms cast003_5
theorem cast003_6 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash003.B06.input).map Fin.val=JGf_TX2_M0.Hash003.B06.input := by rfl
#print axioms cast003_6
theorem cast003_7 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash003.B07.input).map Fin.val=JGf_TX2_M0.Hash003.B07.input := by rfl
#print axioms cast003_7
theorem tail003 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash003.tail).map Fin.val=JGf_TX2_M0.Hash003.tail := by rfl
#print axioms tail003
theorem numeric003 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash003.message).map Fin.val=JGf_TX2_M0.Hash003.message := by
  simp only [JGf_TX2_M0.Hash003.message,JGf_TX2_M0.Hash003.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast003_0,cast003_1,cast003_2,cast003_3,cast003_4,cast003_5,cast003_6,cast003_7,tail003]
#print axioms numeric003
theorem hash003 : JFp_SHADigest.digest input003=value003 := by
  unfold input003 JFp_SHADigest.digest
  rw [numeric003,JGf_TX2_M0.Hash003.checked]
  rfl
#print axioms hash003
def tree003 : Tree := .opened input003
theorem root003 : root JFp_SHADigest.digest tree003=value003 := hash003
#print axioms root003
def input004 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash004.message
def value004 : State := JFp_SHADigest.output JGf_TX2_M0.Hash004.result
theorem cast004_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash004.B00.input).map Fin.val=JGf_TX2_M0.Hash004.B00.input := by rfl
#print axioms cast004_0
theorem cast004_1 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash004.B01.input).map Fin.val=JGf_TX2_M0.Hash004.B01.input := by rfl
#print axioms cast004_1
theorem cast004_2 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash004.B02.input).map Fin.val=JGf_TX2_M0.Hash004.B02.input := by rfl
#print axioms cast004_2
theorem cast004_3 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash004.B03.input).map Fin.val=JGf_TX2_M0.Hash004.B03.input := by rfl
#print axioms cast004_3
theorem cast004_4 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash004.B04.input).map Fin.val=JGf_TX2_M0.Hash004.B04.input := by rfl
#print axioms cast004_4
theorem cast004_5 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash004.B05.input).map Fin.val=JGf_TX2_M0.Hash004.B05.input := by rfl
#print axioms cast004_5
theorem cast004_6 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash004.B06.input).map Fin.val=JGf_TX2_M0.Hash004.B06.input := by rfl
#print axioms cast004_6
theorem cast004_7 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash004.B07.input).map Fin.val=JGf_TX2_M0.Hash004.B07.input := by rfl
#print axioms cast004_7
theorem tail004 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash004.tail).map Fin.val=JGf_TX2_M0.Hash004.tail := by rfl
#print axioms tail004
theorem numeric004 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash004.message).map Fin.val=JGf_TX2_M0.Hash004.message := by
  simp only [JGf_TX2_M0.Hash004.message,JGf_TX2_M0.Hash004.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast004_0,cast004_1,cast004_2,cast004_3,cast004_4,cast004_5,cast004_6,cast004_7,tail004]
#print axioms numeric004
theorem hash004 : JFp_SHADigest.digest input004=value004 := by
  unfold input004 JFp_SHADigest.digest
  rw [numeric004,JGf_TX2_M0.Hash004.checked]
  rfl
#print axioms hash004
def tree004 : Tree := .opened input004
theorem root004 : root JFp_SHADigest.digest tree004=value004 := hash004
#print axioms root004
def input005 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash005.message
def value005 : State := JFp_SHADigest.output JGf_TX2_M0.Hash005.result
theorem cast005_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash005.B00.input).map Fin.val=JGf_TX2_M0.Hash005.B00.input := by rfl
#print axioms cast005_0
theorem cast005_1 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash005.B01.input).map Fin.val=JGf_TX2_M0.Hash005.B01.input := by rfl
#print axioms cast005_1
theorem cast005_2 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash005.B02.input).map Fin.val=JGf_TX2_M0.Hash005.B02.input := by rfl
#print axioms cast005_2
theorem cast005_3 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash005.B03.input).map Fin.val=JGf_TX2_M0.Hash005.B03.input := by rfl
#print axioms cast005_3
theorem cast005_4 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash005.B04.input).map Fin.val=JGf_TX2_M0.Hash005.B04.input := by rfl
#print axioms cast005_4
theorem cast005_5 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash005.B05.input).map Fin.val=JGf_TX2_M0.Hash005.B05.input := by rfl
#print axioms cast005_5
theorem cast005_6 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash005.B06.input).map Fin.val=JGf_TX2_M0.Hash005.B06.input := by rfl
#print axioms cast005_6
theorem cast005_7 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash005.B07.input).map Fin.val=JGf_TX2_M0.Hash005.B07.input := by rfl
#print axioms cast005_7
theorem tail005 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash005.tail).map Fin.val=JGf_TX2_M0.Hash005.tail := by rfl
#print axioms tail005
theorem numeric005 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash005.message).map Fin.val=JGf_TX2_M0.Hash005.message := by
  simp only [JGf_TX2_M0.Hash005.message,JGf_TX2_M0.Hash005.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast005_0,cast005_1,cast005_2,cast005_3,cast005_4,cast005_5,cast005_6,cast005_7,tail005]
#print axioms numeric005
theorem hash005 : JFp_SHADigest.digest input005=value005 := by
  unfold input005 JFp_SHADigest.digest
  rw [numeric005,JGf_TX2_M0.Hash005.checked]
  rfl
#print axioms hash005
def tree005 : Tree := .opened input005
theorem root005 : root JFp_SHADigest.digest tree005=value005 := hash005
#print axioms root005
def input006 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash006.message
def value006 : State := JFp_SHADigest.output JGf_TX2_M0.Hash006.result
theorem cast006_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash006.B00.input).map Fin.val=JGf_TX2_M0.Hash006.B00.input := by rfl
#print axioms cast006_0
theorem cast006_1 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash006.B01.input).map Fin.val=JGf_TX2_M0.Hash006.B01.input := by rfl
#print axioms cast006_1
theorem cast006_2 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash006.B02.input).map Fin.val=JGf_TX2_M0.Hash006.B02.input := by rfl
#print axioms cast006_2
theorem cast006_3 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash006.B03.input).map Fin.val=JGf_TX2_M0.Hash006.B03.input := by rfl
#print axioms cast006_3
theorem cast006_4 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash006.B04.input).map Fin.val=JGf_TX2_M0.Hash006.B04.input := by rfl
#print axioms cast006_4
theorem cast006_5 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash006.B05.input).map Fin.val=JGf_TX2_M0.Hash006.B05.input := by rfl
#print axioms cast006_5
theorem cast006_6 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash006.B06.input).map Fin.val=JGf_TX2_M0.Hash006.B06.input := by rfl
#print axioms cast006_6
theorem cast006_7 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash006.B07.input).map Fin.val=JGf_TX2_M0.Hash006.B07.input := by rfl
#print axioms cast006_7
theorem tail006 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash006.tail).map Fin.val=JGf_TX2_M0.Hash006.tail := by rfl
#print axioms tail006
theorem numeric006 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash006.message).map Fin.val=JGf_TX2_M0.Hash006.message := by
  simp only [JGf_TX2_M0.Hash006.message,JGf_TX2_M0.Hash006.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast006_0,cast006_1,cast006_2,cast006_3,cast006_4,cast006_5,cast006_6,cast006_7,tail006]
#print axioms numeric006
theorem hash006 : JFp_SHADigest.digest input006=value006 := by
  unfold input006 JFp_SHADigest.digest
  rw [numeric006,JGf_TX2_M0.Hash006.checked]
  rfl
#print axioms hash006
def tree006 : Tree := .opened input006
theorem root006 : root JFp_SHADigest.digest tree006=value006 := hash006
#print axioms root006
def input007 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash007.message
def value007 : State := JFp_SHADigest.output JGf_TX2_M0.Hash007.result
theorem cast007_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash007.B00.input).map Fin.val=JGf_TX2_M0.Hash007.B00.input := by rfl
#print axioms cast007_0
theorem cast007_1 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash007.B01.input).map Fin.val=JGf_TX2_M0.Hash007.B01.input := by rfl
#print axioms cast007_1
theorem cast007_2 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash007.B02.input).map Fin.val=JGf_TX2_M0.Hash007.B02.input := by rfl
#print axioms cast007_2
theorem cast007_3 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash007.B03.input).map Fin.val=JGf_TX2_M0.Hash007.B03.input := by rfl
#print axioms cast007_3
theorem cast007_4 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash007.B04.input).map Fin.val=JGf_TX2_M0.Hash007.B04.input := by rfl
#print axioms cast007_4
theorem cast007_5 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash007.B05.input).map Fin.val=JGf_TX2_M0.Hash007.B05.input := by rfl
#print axioms cast007_5
theorem cast007_6 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash007.B06.input).map Fin.val=JGf_TX2_M0.Hash007.B06.input := by rfl
#print axioms cast007_6
theorem cast007_7 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash007.B07.input).map Fin.val=JGf_TX2_M0.Hash007.B07.input := by rfl
#print axioms cast007_7
theorem tail007 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash007.tail).map Fin.val=JGf_TX2_M0.Hash007.tail := by rfl
#print axioms tail007
theorem numeric007 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash007.message).map Fin.val=JGf_TX2_M0.Hash007.message := by
  simp only [JGf_TX2_M0.Hash007.message,JGf_TX2_M0.Hash007.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast007_0,cast007_1,cast007_2,cast007_3,cast007_4,cast007_5,cast007_6,cast007_7,tail007]
#print axioms numeric007
theorem hash007 : JFp_SHADigest.digest input007=value007 := by
  unfold input007 JFp_SHADigest.digest
  rw [numeric007,JGf_TX2_M0.Hash007.checked]
  rfl
#print axioms hash007
def tree007 : Tree := .opened input007
theorem root007 : root JFp_SHADigest.digest tree007=value007 := hash007
#print axioms root007
def input008 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash008.message
def value008 : State := JFp_SHADigest.output JGf_TX2_M0.Hash008.result
theorem cast008_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash008.B00.input).map Fin.val=JGf_TX2_M0.Hash008.B00.input := by rfl
#print axioms cast008_0
theorem cast008_1 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash008.B01.input).map Fin.val=JGf_TX2_M0.Hash008.B01.input := by rfl
#print axioms cast008_1
theorem cast008_2 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash008.B02.input).map Fin.val=JGf_TX2_M0.Hash008.B02.input := by rfl
#print axioms cast008_2
theorem cast008_3 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash008.B03.input).map Fin.val=JGf_TX2_M0.Hash008.B03.input := by rfl
#print axioms cast008_3
theorem cast008_4 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash008.B04.input).map Fin.val=JGf_TX2_M0.Hash008.B04.input := by rfl
#print axioms cast008_4
theorem cast008_5 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash008.B05.input).map Fin.val=JGf_TX2_M0.Hash008.B05.input := by rfl
#print axioms cast008_5
theorem cast008_6 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash008.B06.input).map Fin.val=JGf_TX2_M0.Hash008.B06.input := by rfl
#print axioms cast008_6
theorem cast008_7 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash008.B07.input).map Fin.val=JGf_TX2_M0.Hash008.B07.input := by rfl
#print axioms cast008_7
theorem tail008 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash008.tail).map Fin.val=JGf_TX2_M0.Hash008.tail := by rfl
#print axioms tail008
theorem numeric008 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash008.message).map Fin.val=JGf_TX2_M0.Hash008.message := by
  simp only [JGf_TX2_M0.Hash008.message,JGf_TX2_M0.Hash008.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast008_0,cast008_1,cast008_2,cast008_3,cast008_4,cast008_5,cast008_6,cast008_7,tail008]
#print axioms numeric008
theorem hash008 : JFp_SHADigest.digest input008=value008 := by
  unfold input008 JFp_SHADigest.digest
  rw [numeric008,JGf_TX2_M0.Hash008.checked]
  rfl
#print axioms hash008
def tree008 : Tree := .opened input008
theorem root008 : root JFp_SHADigest.digest tree008=value008 := hash008
#print axioms root008
def input009 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash009.message
def value009 : State := JFp_SHADigest.output JGf_TX2_M0.Hash009.result
theorem cast009_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash009.B00.input).map Fin.val=JGf_TX2_M0.Hash009.B00.input := by rfl
#print axioms cast009_0
theorem cast009_1 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash009.B01.input).map Fin.val=JGf_TX2_M0.Hash009.B01.input := by rfl
#print axioms cast009_1
theorem cast009_2 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash009.B02.input).map Fin.val=JGf_TX2_M0.Hash009.B02.input := by rfl
#print axioms cast009_2
theorem cast009_3 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash009.B03.input).map Fin.val=JGf_TX2_M0.Hash009.B03.input := by rfl
#print axioms cast009_3
theorem cast009_4 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash009.B04.input).map Fin.val=JGf_TX2_M0.Hash009.B04.input := by rfl
#print axioms cast009_4
theorem cast009_5 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash009.B05.input).map Fin.val=JGf_TX2_M0.Hash009.B05.input := by rfl
#print axioms cast009_5
theorem cast009_6 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash009.B06.input).map Fin.val=JGf_TX2_M0.Hash009.B06.input := by rfl
#print axioms cast009_6
theorem cast009_7 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash009.B07.input).map Fin.val=JGf_TX2_M0.Hash009.B07.input := by rfl
#print axioms cast009_7
theorem tail009 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash009.tail).map Fin.val=JGf_TX2_M0.Hash009.tail := by rfl
#print axioms tail009
theorem numeric009 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash009.message).map Fin.val=JGf_TX2_M0.Hash009.message := by
  simp only [JGf_TX2_M0.Hash009.message,JGf_TX2_M0.Hash009.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast009_0,cast009_1,cast009_2,cast009_3,cast009_4,cast009_5,cast009_6,cast009_7,tail009]
#print axioms numeric009
theorem hash009 : JFp_SHADigest.digest input009=value009 := by
  unfold input009 JFp_SHADigest.digest
  rw [numeric009,JGf_TX2_M0.Hash009.checked]
  rfl
#print axioms hash009
def tree009 : Tree := .opened input009
theorem root009 : root JFp_SHADigest.digest tree009=value009 := hash009
#print axioms root009
def input010 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash010.message
def value010 : State := JFp_SHADigest.output JGf_TX2_M0.Hash010.result
theorem cast010_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash010.B00.input).map Fin.val=JGf_TX2_M0.Hash010.B00.input := by rfl
#print axioms cast010_0
theorem cast010_1 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash010.B01.input).map Fin.val=JGf_TX2_M0.Hash010.B01.input := by rfl
#print axioms cast010_1
theorem cast010_2 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash010.B02.input).map Fin.val=JGf_TX2_M0.Hash010.B02.input := by rfl
#print axioms cast010_2
theorem cast010_3 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash010.B03.input).map Fin.val=JGf_TX2_M0.Hash010.B03.input := by rfl
#print axioms cast010_3
theorem cast010_4 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash010.B04.input).map Fin.val=JGf_TX2_M0.Hash010.B04.input := by rfl
#print axioms cast010_4
theorem cast010_5 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash010.B05.input).map Fin.val=JGf_TX2_M0.Hash010.B05.input := by rfl
#print axioms cast010_5
theorem cast010_6 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash010.B06.input).map Fin.val=JGf_TX2_M0.Hash010.B06.input := by rfl
#print axioms cast010_6
theorem cast010_7 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash010.B07.input).map Fin.val=JGf_TX2_M0.Hash010.B07.input := by rfl
#print axioms cast010_7
theorem tail010 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash010.tail).map Fin.val=JGf_TX2_M0.Hash010.tail := by rfl
#print axioms tail010
theorem numeric010 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash010.message).map Fin.val=JGf_TX2_M0.Hash010.message := by
  simp only [JGf_TX2_M0.Hash010.message,JGf_TX2_M0.Hash010.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast010_0,cast010_1,cast010_2,cast010_3,cast010_4,cast010_5,cast010_6,cast010_7,tail010]
#print axioms numeric010
theorem hash010 : JFp_SHADigest.digest input010=value010 := by
  unfold input010 JFp_SHADigest.digest
  rw [numeric010,JGf_TX2_M0.Hash010.checked]
  rfl
#print axioms hash010
def tree010 : Tree := .opened input010
theorem root010 : root JFp_SHADigest.digest tree010=value010 := hash010
#print axioms root010
def input011 : Bytes := JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash011.message
def value011 : State := JFp_SHADigest.output JGf_TX2_M0.Hash011.result
theorem cast011_0 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash011.B00.input).map Fin.val=JGf_TX2_M0.Hash011.B00.input := by rfl
#print axioms cast011_0
theorem cast011_1 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash011.B01.input).map Fin.val=JGf_TX2_M0.Hash011.B01.input := by rfl
#print axioms cast011_1
theorem cast011_2 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash011.B02.input).map Fin.val=JGf_TX2_M0.Hash011.B02.input := by rfl
#print axioms cast011_2
theorem cast011_3 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash011.B03.input).map Fin.val=JGf_TX2_M0.Hash011.B03.input := by rfl
#print axioms cast011_3
theorem cast011_4 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash011.B04.input).map Fin.val=JGf_TX2_M0.Hash011.B04.input := by rfl
#print axioms cast011_4
theorem cast011_5 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash011.B05.input).map Fin.val=JGf_TX2_M0.Hash011.B05.input := by rfl
#print axioms cast011_5
theorem cast011_6 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash011.B06.input).map Fin.val=JGf_TX2_M0.Hash011.B06.input := by rfl
#print axioms cast011_6
theorem cast011_7 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash011.B07.input).map Fin.val=JGf_TX2_M0.Hash011.B07.input := by rfl
#print axioms cast011_7
theorem tail011 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash011.tail).map Fin.val=JGf_TX2_M0.Hash011.tail := by rfl
#print axioms tail011
theorem numeric011 : (JGc_TX2_HashBytes.bytes JGf_TX2_M0.Hash011.message).map Fin.val=JGf_TX2_M0.Hash011.message := by
  simp only [JGf_TX2_M0.Hash011.message,JGf_TX2_M0.Hash011.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,cast011_0,cast011_1,cast011_2,cast011_3,cast011_4,cast011_5,cast011_6,cast011_7,tail011]
#print axioms numeric011
theorem hash011 : JFp_SHADigest.digest input011=value011 := by
  unfold input011 JFp_SHADigest.digest
  rw [numeric011,JGf_TX2_M0.Hash011.checked]
  rfl
#print axioms hash011
def tree011 : Tree := .opened input011
theorem root011 : root JFp_SHADigest.digest tree011=value011 := hash011
#print axioms root011
def inputAt (base : Nat) : Bytes := match base with
  | 132355 => input000
  | 218094 => input001
  | 178080 => input002
  | 149624 => input003
  | 166165 => input004
  | 42158 => input005
  | 179622 => input006
  | 21248 => input007
  | 63860 => input008
  | 55377 => input009
  | 185637 => input010
  | 14297 => input011
  | _ => []
def InputLaw (f : Nat → Bytes) : Prop := ∀ b,b∈indices → f b=inputAt b
theorem shape000 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 132355=tree000 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 132355),inputs 132355 (by decide)]
  rfl
#print axioms shape000
theorem shape001 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 218094=tree001 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 218094),inputs 218094 (by decide)]
  rfl
#print axioms shape001
theorem shape002 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 178080=tree002 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 178080),inputs 178080 (by decide)]
  rfl
#print axioms shape002
theorem shape003 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 149624=tree003 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 149624),inputs 149624 (by decide)]
  rfl
#print axioms shape003
theorem shape004 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 166165=tree004 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 166165),inputs 166165 (by decide)]
  rfl
#print axioms shape004
theorem shape005 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 42158=tree005 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 42158),inputs 42158 (by decide)]
  rfl
#print axioms shape005
theorem shape006 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 179622=tree006 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 179622),inputs 179622 (by decide)]
  rfl
#print axioms shape006
theorem shape007 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 21248=tree007 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 21248),inputs 21248 (by decide)]
  rfl
#print axioms shape007
theorem shape008 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 63860=tree008 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 63860),inputs 63860 (by decide)]
  rfl
#print axioms shape008
theorem shape009 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 55377=tree009 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 55377),inputs 55377 (by decide)]
  rfl
#print axioms shape009
theorem shape010 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 185637=tree010 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 185637),inputs 185637 (by decide)]
  rfl
#print axioms shape010
theorem shape011 (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 14297=tree011 := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 14297),inputs 14297 (by decide)]
  rfl
#print axioms shape011
end AspisR1.JGf_TX2_M0Roots
end
