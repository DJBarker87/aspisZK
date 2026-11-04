import NFP_QueryCuts
import Port3_PushFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_HeadDomain
open Aeneas Aeneas.Std Result AspisR1Stage2 NFP_QueryCuts
open Port3_NativeQueryBody Port3_PushFrame
/-- A successful prefix supplies the SAME opening and child result. This is
an elimination theorem, not a hypothesis selecting a successful child. -/
theorem reached (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array E 29#usize)
 (u : Usize) (q : Slice U8) (dots : Dots)
 (h : head ops proof p a g = ok (u,q,dots)) :
 ∃ index, Array.index_usize p.queries a.next = ok index ∧
  lift (UScalar.cast .Usize index) = ok u ∧
  ops.op11 proof a.next = ok q ∧ ops.op20 q g = ok dots := by
 unfold head at h
 obtain ⟨index,hi,h⟩ := bind_success _ _ _ h
 obtain ⟨cast,hcast,h⟩ := bind_success _ _ _ h
 obtain ⟨opening,hopening,h⟩ := bind_success _ _ _ h
 obtain ⟨reply,hreply,h⟩ := bind_success _ _ _ h
 cases Result.ok.inj h
 exact ⟨index,hi,hcast,hopening,hreply⟩
#print axioms reached
end AspisR1.NFP_HeadDomain
end
