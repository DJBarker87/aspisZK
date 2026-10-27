import JFy_SquareTotal
import FIq_Native04
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_Pow5
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon decode)

theorem source (x : field.QM31) (hx : Canon x) :
    ∃ out,state_only_poseidon.pow5 x=ok out ∧ Canon out ∧ decode out=decode x^5 := by
  obtain ⟨square,hs,hsc,hsv⟩ := JFy_SquareTotal.source x hx
  obtain ⟨fourth,hf,hfc,hfv⟩ := JFy_SquareTotal.source square hsc
  obtain ⟨out,ho,hoc,hov⟩ := JFy_FieldTotal.mul fourth x hfc hx
  refine ⟨out,?_,hoc,?_⟩
  · unfold state_only_poseidon.pow5
    rw [hs,bind_tc_ok,hf,bind_tc_ok,ho]
  · rw [hov,hfv,hsv]
    ring
#print axioms source
end AspisR1.JFy_Pow5
end
