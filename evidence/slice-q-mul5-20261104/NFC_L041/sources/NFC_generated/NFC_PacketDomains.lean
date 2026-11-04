import NFC_TailPacket
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFC_PacketDomains
open Aeneas Aeneas.Std Result NEV_DotCarrier NFC_TailPacket

theorem counts {q : Array U8 608#usize} {g : NEV_DotInputs.Coefficients} {slot : Usize} {out : NE}
    (p : Packet q g slot out) : p.state0.count.val=0 ∧ p.state1.count.val=1 ∧
      p.state2.count.val=2 ∧ p.state3.count.val=3 := by
  have c0:=NFC_TailState.new_count p.state0 p.new
  have c1:=NFC_PushCut.count p.state0 p.state1 p.args0 (by omega) p.call0
  have c2:=NFC_PushCut.count p.state1 p.state2 p.args1 (by omega) p.call1
  have c3:=NFC_PushCut.count p.state2 p.state3 p.args2 (by omega) p.call2
  exact ⟨c0,by omega,by omega,by omega⟩

theorem inputs {q : Array U8 608#usize} {g : NEV_DotInputs.Coefficients} {slot : Usize} {out : NE}
    (p : Packet q g slot out) (canonical : NEV_DotInputs.Canonical g) :
    canonE p.args0.1 ∧ canonQ p.args0.2 ∧ canonE p.args1.1 ∧ canonQ p.args1.2 ∧
      canonE p.args2.1 ∧ canonQ p.args2.2 := by
  have a:=NFC_FirstSource.domains q g slot canonical p.args0.1 p.args0.2 p.first
  have b:=NFC_LaterSource.domains q g p.base 0#usize (by decide) canonical p.args1.1 p.args1.2 p.later0
  have c:=NFC_LaterSource.domains q g p.base 1#usize (by decide) canonical p.args2.1 p.args2.2 p.later1
  exact ⟨a.1,a.2,b.1,b.2,c.1,c.2⟩

theorem finish {q : Array U8 608#usize} {g : NEV_DotInputs.Coefficients} {slot : Usize} {out : NE}
    (p : Packet q g slot out) : canonE out := NFC_TailState.finish_canonical p.state3 out p.finish

/-- Count domains needed by the native arbitrary-position window follow
without an extra bound or independently supplied child success. -/
theorem native_counts {q : Array U8 608#usize} {g : NEV_DotInputs.Coefficients} {slot : Usize} {out : NE}
    (p : Packet q g slot out) : p.state0.count.val<3 ∧ p.state1.count.val<3 ∧ p.state2.count.val<3 := by
  obtain ⟨a,b,c,_⟩:=counts p
  omega
#print axioms counts
#print axioms inputs
#print axioms finish
#print axioms native_counts
end AspisR1.NFC_PacketDomains
end
