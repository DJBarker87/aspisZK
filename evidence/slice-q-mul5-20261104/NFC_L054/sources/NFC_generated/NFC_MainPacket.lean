import NFC_FinalCalls
import NFC_DotDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFC_MainPacket
open Aeneas Aeneas.Std Result NEV_DotCarrier NFC_TailTrace NFC_ReceiverModel

structure Packet (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients) (slot : Usize) (out : NE) where
  limbs : Array U64 8#usize
  head : NE
  tail : NE
  loop : FIp_NativeDots.fast_dots.four_dots_one_loop0 (NFA_Iterator.value 0) q g slot
    (Array.repeat 8#usize 0#u64)=ok limbs
  bound : NFA_FoldEight.Bound limbs 7
  finish : NFA_SuffixFactor.scalarFinish limbs=ok head
  tailPacket : NFC_TailPacket.Packet q g slot tail
  add : FIo_Native.aspis_core.field.wide_exact.WideExact.add head tail=ok out

theorem of_run (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients) (slot : Usize) (out : NE)
    (run : FIp_NativeDots.fast_dots.four_dots_one q g slot=ok out) : Nonempty (Packet q g slot out) := by
  obtain ⟨limbs,head,tail,loop,bound,finish,tailRun,add⟩:=NFA_DotCuts.accepted q g slot out run
  obtain ⟨packet⟩:=NFC_TailPacket.of_run q g slot tail tailRun
  exact ⟨⟨limbs,head,tail,loop,bound,finish,packet,add⟩⟩

theorem replay {q : Array U8 608#usize} {g : NEV_DotInputs.Coefficients} {slot : Usize} {out : NE}
    (packet : Packet q g slot out) : FIp_NativeDots.fast_dots.four_dots_one q g slot=ok out := by
  rw [NFA_SuffixFactor.body]
  simp only [NFA_Iterator.initial,bind_tc_ok,packet.loop,packet.finish,
    NFC_TailPacket.replay packet.tailPacket,packet.add]

/-- Derived SAME-chain domain certificate for the full actual main body. -/
theorem domains {q : Array U8 608#usize} {g : NEV_DotInputs.Coefficients} {slot : Usize} {out : NE}
    (packet : Packet q g slot out) (canonical : NEV_DotInputs.Canonical g) :
    canonE packet.head ∧ canonE packet.tail ∧ canonE out ∧
      NFC_ChainAssociation.chain packet.tailPacket.state0 (words packet.tailPacket.state1)
        (words packet.tailPacket.state2) (words packet.tailPacket.state3)=packet.tailPacket.state3 := by
  have h:=NFC_HeadDomain.canonical packet.limbs packet.head packet.finish
  have t:=NFC_PacketDomains.finish packet.tailPacket
  exact ⟨h,t,NFC_AddDomain.canonical _ _ _ h t packet.add,NFC_ChainAssociation.actual packet.tailPacket⟩
#print axioms of_run
#print axioms replay
#print axioms domains
end AspisR1.NFC_MainPacket
end
