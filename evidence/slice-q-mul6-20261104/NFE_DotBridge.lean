import NFE_NFC_WrapperPacket
import NEV_DotResult
import NFE_NEI_PublicDotFinishValues

set_option autoImplicit false
noncomputable section
namespace AspisR1.NFE_DotBridge
open Aeneas Aeneas.Std Result NEV_DotCarrier

/-- Derived inner domains and receiver association on the same extracted call.
The only extra data predicate is the root coefficient domain; no inner success
or independently selected child result is a premise. This is a source bridge,
not an assertion of native heap or ELF interpretation. -/
theorem one (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
    (slot : Usize) (out : NE) (canonical : NEV_DotInputs.Canonical g)
    (run : NEG_DotsTypes.fast_dots.four_dots_one q g slot=ok out) :
    ∃ p : NFE_NFC_MainPacket.Packet q g slot out,
      canonE p.head ∧ canonE p.tail ∧ canonE out ∧
      canonE p.tailPacket.args0.1 ∧ canonQ p.tailPacket.args0.2 ∧
      canonE p.tailPacket.args1.1 ∧ canonQ p.tailPacket.args1.2 ∧
      canonE p.tailPacket.args2.1 ∧ canonQ p.tailPacket.args2.2 ∧
      p.tailPacket.state0.count.val<3 ∧ p.tailPacket.state1.count.val<3 ∧
      p.tailPacket.state2.count.val<3 ∧
      NFE_NFC_ReceiverModel.overwrite p.tailPacket.state0
        (NFE_NFC_ReceiverModel.words p.tailPacket.state1)=p.tailPacket.state1 ∧
      NFE_NFC_ReceiverModel.overwrite p.tailPacket.state1
        (NFE_NFC_ReceiverModel.words p.tailPacket.state2)=p.tailPacket.state2 ∧
      NFE_NFC_ReceiverModel.overwrite p.tailPacket.state2
        (NFE_NFC_ReceiverModel.words p.tailPacket.state3)=p.tailPacket.state3 := by
  rw [NEV_DotResult.source] at run
  obtain ⟨p⟩ := NFE_NFC_MainPacket.of_run q g slot out run
  obtain ⟨head,tail,result,_⟩ := NFE_NFC_MainPacket.domains p
  obtain ⟨a,b,c,d,e,f⟩ := NFE_NFC_PacketDomains.inputs p.tailPacket canonical
  obtain ⟨n0,n1,n2⟩ := NFE_NFC_PacketDomains.native_counts p.tailPacket
  obtain ⟨s0,s1,s2⟩ := NFE_NFC_StepAssociation.packet p.tailPacket
  exact ⟨p,head,tail,result,a,b,c,d,e,f,n0,n1,n2,s0,s1,s2⟩

/-- The exposed packet is equivalent to the original complete extracted
successful result. Its construction never assumes a packet's existence. -/
theorem one_iff (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
    (slot : Usize) (out : NE) :
    NEG_DotsTypes.fast_dots.four_dots_one q g slot=ok out ↔
      Nonempty (NFE_NFC_MainPacket.Packet q g slot out) := by
  rw [NEV_DotResult.source]
  constructor
  · exact NFE_NFC_MainPacket.of_run q g slot out
  · rintro ⟨p⟩
    exact NFE_NFC_MainPacket.replay p

#print axioms one
#print axioms one_iff
end AspisR1.NFE_DotBridge
end
