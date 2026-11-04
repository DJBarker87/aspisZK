import NFC_ReceiverModel
import NFC_CalleeDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFC_StepAssociation
open Aeneas Aeneas.Std Result NEV_DotCarrier NFC_TailTrace NFC_ReceiverModel
/-- Every actual canonical call has a reply represented by the native local
oracle. Its word reply is chosen FROM that actual output, not independently. -/
theorem exact (before : Acc) (value : NE) (scalar : NQ)
    (hv : canonE value) (hx : canonQ scalar) (small : before.count.val<3) :
    ∃ after, FIo_Native.fast_pairing.EbyKDot.push before value scalar=ok (.Ok (),after) ∧
      overwrite before (words after)=after := by
  obtain ⟨after,call,count⟩:=NFC_CalleeDomains.total before value scalar hv hx (by omega)
  exact ⟨after,call,represents before after small count⟩

theorem packet {q : Array U8 608#usize} {g : NEV_DotInputs.Coefficients} {slot : Usize} {out : NE}
    (p : NFC_TailPacket.Packet q g slot out) :
    overwrite p.state0 (words p.state1)=p.state1 ∧
    overwrite p.state1 (words p.state2)=p.state2 ∧
    overwrite p.state2 (words p.state3)=p.state3 := by
  obtain ⟨c0,c1,c2,c3⟩:=NFC_PacketDomains.counts p
  exact ⟨represents _ _ (by omega) (by omega),represents _ _ (by omega) (by omega),
    represents _ _ (by omega) (by omega)⟩
#print axioms exact
#print axioms packet
end AspisR1.NFC_StepAssociation
end
