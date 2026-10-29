import R1Z.PV_OWNB_Kind00
import R1Z.PV_OWNB_Kind01
import R1Z.PV_OWNB_Kind02
import R1Z.PV_OWNB_Kind03
import R1Z.PV_OWNB_Kind04
import R1Z.PV_OWNB_Kind05
import R1Z.PV_OWNB_Kind06
import R1Z.PV_OWNB_Kind07
import R1Z.PV_OWNB_Kind08
import R1Z.PV_OWNB_Kind09
import R1Z.PV_OWNB_Kind10
import R1Z.PV_OWNB_Kind11
import R1Z.PV_OWNB_Kind12
import R1Z.PV_OWNB_Kind13
import R1Z.PV_OWNB_Kind14
import R1Z.PV_OWNB_Kind15
import R1Z.PV_OWNB_Kind16
import R1Z.PV_OWNB_Kind17
import R1Z.PV_OWNB_Kind18
import R1Z.PV_OWNB_Kind19
import R1Z.PV_OWNB_Kind20
import R1Z.PV_OWNB_Padding
set_option autoImplicit false
namespace R1Z.PV_OWNB_KindAgreement
open PV_OWN_Link PV_OWNB_KindCodec PV_OWNB_Padding
/-- Active-byte agreement suffices; inactive bytes may contain arbitrary data. -/
theorem read (k : Kind) (raw : PV_OWN_Bytes.Bytes) (h:Agrees (encode k) raw) :
 decode raw=some k := by
 cases k with
 | spongeCarry a b =>
  apply PV_OWNB_Kind00.read
  exact h 0 (0:UInt8) (by simp [encode,tag,first,second])
  exact h 1 a (by simp [encode,tag,first,second])
  exact h 2 b (by simp [encode,tag,first,second])
 | ownerOutput =>
  apply PV_OWNB_Kind01.read
  exact h 0 (1:UInt8) (by simp [encode,tag,first,second])
 | nullifierKey =>
  apply PV_OWNB_Kind02.read
  exact h 0 (2:UInt8) (by simp [encode,tag,first,second])
 | inputSaltHead =>
  apply PV_OWNB_Kind03.read
  exact h 0 (3:UInt8) (by simp [encode,tag,first,second])
 | inputSaltTail =>
  apply PV_OWNB_Kind04.read
  exact h 0 (4:UInt8) (by simp [encode,tag,first,second])
 | privatePathCurrent a =>
  apply PV_OWNB_Kind05.read
  exact h 0 (5:UInt8) (by simp [encode,tag,first,second])
  exact h 1 a (by simp [encode,tag,first,second])
 | privatePathLeft a =>
  apply PV_OWNB_Kind06.read
  exact h 0 (6:UInt8) (by simp [encode,tag,first,second])
  exact h 1 a (by simp [encode,tag,first,second])
 | privatePathRight a =>
  apply PV_OWNB_Kind07.read
  exact h 0 (7:UInt8) (by simp [encode,tag,first,second])
  exact h 1 a (by simp [encode,tag,first,second])
 | valueSource a =>
  apply PV_OWNB_Kind08.read
  exact h 0 (8:UInt8) (by simp [encode,tag,first,second])
  exact h 1 a (by simp [encode,tag,first,second])
 | conservationInput =>
  apply PV_OWNB_Kind09.read
  exact h 0 (9:UInt8) (by simp [encode,tag,first,second])
 | conservationRecipient =>
  apply PV_OWNB_Kind10.read
  exact h 0 (10:UInt8) (by simp [encode,tag,first,second])
 | conservationChange =>
  apply PV_OWNB_Kind11.read
  exact h 0 (11:UInt8) (by simp [encode,tag,first,second])
 | conservationPartial =>
  apply PV_OWNB_Kind12.read
  exact h 0 (12:UInt8) (by simp [encode,tag,first,second])
 | inputSecondCommitment =>
  apply PV_OWNB_Kind13.read
  exact h 0 (13:UInt8) (by simp [encode,tag,first,second])
 | inputSelectedSide =>
  apply PV_OWNB_Kind14.read
  exact h 0 (14:UInt8) (by simp [encode,tag,first,second])
 | outputSecondCommitment =>
  apply PV_OWNB_Kind15.read
  exact h 0 (15:UInt8) (by simp [encode,tag,first,second])
 | outputPairFirst =>
  apply PV_OWNB_Kind16.read
  exact h 0 (16:UInt8) (by simp [encode,tag,first,second])
 | outputPairFirstWithdrawal =>
  apply PV_OWNB_Kind17.read
  exact h 0 (17:UInt8) (by simp [encode,tag,first,second])
 | outputPairSecond =>
  apply PV_OWNB_Kind18.read
  exact h 0 (18:UInt8) (by simp [encode,tag,first,second])
 | appendCurrentLeft a =>
  apply PV_OWNB_Kind19.read
  exact h 0 (19:UInt8) (by simp [encode,tag,first,second])
  exact h 1 a (by simp [encode,tag,first,second])
 | appendCurrentRight a =>
  apply PV_OWNB_Kind20.read
  exact h 0 (20:UInt8) (by simp [encode,tag,first,second])
  exact h 1 a (by simp [encode,tag,first,second])

theorem unique (a b : Kind) (raw : PV_OWN_Bytes.Bytes)
 (ha:Agrees (encode a) raw) (hb:Agrees (encode b) raw) : a=b := by
 exact Option.some.inj ((read a raw ha).symm.trans (read b raw hb))
#print axioms read
#print axioms unique
end R1Z.PV_OWNB_KindAgreement
