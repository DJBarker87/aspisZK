import NDO_JGj_InternalZeroEquation
import NDO_JGj_ZeroLiftedSymbolic
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_InternalZeroStable
open Aeneas Aeneas.Std Result FIq_Native
open JGj_RawBounds
open FJb_TailCell (cell)
theorem source (a : Raw) (w : Words) (i : Usize) (hi : i.val<(4#usize).val)
    (ha : Bound a (61*P)) (hw : Canonical w) :
    ∃ out,JGj_InternalZeroEquation.Callback.call_mut (a,w) i=ok (out,(a,w)) := by
  let x := cell a ⟨i.val,hi⟩
  let y := cell w ⟨i.val,hi⟩
  have rx : Array.index_usize a i=ok x := RawPoseidonExternalRowReads.array_index_usize_ok a i hi
  have ry : Array.index_usize w i=ok y := RawPoseidonExternalRowReads.array_index_usize_ok w i hi
  obtain ⟨out,ro⟩ := JGj_ZeroSubtract.success x y (ha _) (hw _)
  have lifted : JGj_ZeroLiftedSymbolic.source x y=ok out := (JGj_ZeroLiftedSymbolic.factor x y).trans ro
  have paired : (do let out ← JGj_ZeroLiftedSymbolic.source x y;ok ((out,(a,w)) : U64 × state_only_poseidon.internal_linear_lazy.closure_1))=ok (out,(a,w)) := by rw [lifted,bind_tc_ok];rfl
  refine ⟨out,?_⟩
  rw [JGj_InternalZeroEquation.source,rx,bind_tc_ok]
  simp only [ry,bind_tc_ok]
  simpa only [JGj_ZeroLiftedSymbolic.source,bind_assoc_eq,state_only_poseidon.internal_linear_lazy.closure_1] using paired
#print axioms source
end AspisR1.JGj_InternalZeroStable
end
