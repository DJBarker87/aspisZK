import NDO_JGj_InternalTotal
import RPv_JFy_Specs
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_InternalRoundTotal
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FJb_MatrixGroupStep (State)
theorem source (s : State) (c : NQ) (hs : FIw_ArrayValue.canonical s) (hc : Canon c) :
    ∃ out,state_only_poseidon.internal_round s c=ok out ∧ FIw_ArrayValue.canonical out := by
  obtain ⟨x,rx,cx⟩ := JFy_ArrayTotal.read s 0#usize (by decide) hs
  obtain ⟨a,ra,ca,_⟩ := FIv_PreparedTotal.add x c cx hc
  obtain ⟨q,rq,cq,_⟩ := JFy_Pow5.source a ca
  obtain ⟨s1,rs,cs⟩ := JFy_ArrayTotal.update s 0#usize q (by decide) hs cq
  obtain ⟨out,ro,co⟩ := JGj_InternalTotal.source s1 cs
  exact ⟨out,by simp only [state_only_poseidon.internal_round,rx,ra,rq,rs,ro,bind_tc_ok],co⟩
#print axioms source
end AspisR1.JGj_InternalRoundTotal
end
