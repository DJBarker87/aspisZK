import NFE_NFC_TailAssociation
import NFE_NFC_PushCut
import NFE_NFC_FirstGeometry
import NFE_NFC_LaterGeometry
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFE_NFC_TailPacket
open Aeneas Aeneas.Std Result NEV_DotCarrier NFE_NFC_TailSources

/-- Source cuts indexed by one fixed input and returned value. Construction is
proved below from that run; this record is never assumed as caller success. -/
structure Packet (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients) (slot : Usize) (out : NE) where
  state0 : NFE_NFC_TailTrace.Acc
  state1 : NFE_NFC_TailTrace.Acc
  state2 : NFE_NFC_TailTrace.Acc
  state3 : NFE_NFC_TailTrace.Acc
  args0 : NE×NQ
  args1 : NE×NQ
  args2 : NE×NQ
  base : Usize
  new : FIo_Native.fast_pairing.EbyKDot.new=ok state0
  first : NFE_NFC_TailSources.first q g slot=ok args0
  call0 : push state0 args0=ok state1
  baseEq : slot*32#usize=ok base
  later0 : later q g base 0#usize=ok args1
  call1 : push state1 args1=ok state2
  later1 : later q g base 1#usize=ok args2
  call2 : push state2 args2=ok state3
  finish : FIo_Native.fast_pairing.EbyKDot.finish state3=ok out

theorem of_run (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients) (slot : Usize) (out : NE)
    (run : NFE_NFA_SuffixFactor.tail q g slot=ok out) : Nonempty (Packet q g slot out) := by
  rw [NFE_NFC_TailAssociation.source] at run
  unfold body at run
  obtain ⟨s0,new,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨a0,first,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨s1,p0,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨base,baseEq,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨a1,l0,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨s2,p1,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨a2,l1,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨s3,p2,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  exact ⟨⟨s0,s1,s2,s3,a0,a1,a2,base,new,first,p0,baseEq,l0,p1,l1,p2,run⟩⟩

/-- Converse keeps this certificate honest: its cuts reproduce the SAME
full tail result, rather than admitting independently selected child runs. -/
theorem replay {q : Array U8 608#usize} {g : NEV_DotInputs.Coefficients} {slot : Usize} {out : NE}
    (packet : Packet q g slot out) : NFE_NFA_SuffixFactor.tail q g slot=ok out := by
  rw [NFE_NFC_TailAssociation.source]
  simp only [body,packet.new,packet.first,packet.call0,packet.baseEq,packet.later0,
    packet.call1,packet.later1,packet.call2,packet.finish,bind_tc_ok]

#print axioms of_run
#print axioms replay
end AspisR1.NFE_NFC_TailPacket
end
