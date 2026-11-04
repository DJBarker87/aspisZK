import NFE_NFC_StepAssociation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFE_NFC_ChainAssociation
open Aeneas Aeneas.Std Result NEV_DotCarrier NFE_NFC_TailTrace NFE_NFC_ReceiverModel

def chain (initial : Acc) (a b c : Array U64 8#usize) : Acc :=
  overwrite (overwrite (overwrite initial a) b) c

/-- The three arbitrary native replies can be instantiated simultaneously
from the SAME actual receiver chain. -/
theorem actual {q : Array U8 608#usize} {g : NEV_DotInputs.Coefficients} {slot : Usize} {out : NE}
    (p : NFE_NFC_TailPacket.Packet q g slot out) :
    chain p.state0 (words p.state1) (words p.state2) (words p.state3)=p.state3 := by
  obtain ⟨a,b,c⟩:=NFE_NFC_StepAssociation.packet p
  simp only [chain,a,b,c]

theorem finish {q : Array U8 608#usize} {g : NEV_DotInputs.Coefficients} {slot : Usize} {out : NE}
    (p : NFE_NFC_TailPacket.Packet q g slot out) :
    FIo_Native.fast_pairing.EbyKDot.finish
      (chain p.state0 (words p.state1) (words p.state2) (words p.state3))=ok out := by
  rw [actual p]
  exact p.finish

/-- Fixed receiver initialization also agrees at every native word position. -/
theorem zero (state : Acc) (run : FIo_Native.fast_pairing.EbyKDot.new=ok state) :
    words state=Array.repeat 8#usize 0#u64 := by
  unfold FIo_Native.fast_pairing.EbyKDot.new FIo_Native.fast_pairing.canonical.Dot.new at run
  simp only [bind_tc_ok] at run
  cases run
  rfl
#print axioms actual
#print axioms finish
#print axioms zero
end AspisR1.NFE_NFC_ChainAssociation
end
