import NDO_JGj_RawBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_InternalFullSum
open Aeneas Aeneas.Std Result FIq_Native
open JGj_RawBounds
open FJb_TailCell (cell)
abbrev Full := state_only_poseidon.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
abbrev Zero := state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64
theorem full (a : Raw) (w : Words) (i : Usize) (hi : i.val<(4#usize).val)
    (ha : Bound a (61*P)) (hw : Canonical w) :
    ∃ out,Full.call_mut (a,w) i=ok (out,(a,w)) ∧ out.val<62*P := by
  let x := cell a ⟨i.val,hi⟩
  let y := cell w ⟨i.val,hi⟩
  have rx : Array.index_usize a i=ok x := RawPoseidonExternalRowReads.array_index_usize_ok a i hi
  have ry : Array.index_usize w i=ok y := RawPoseidonExternalRowReads.array_index_usize_ok w i hi
  have bx : x.val<61*P := ha _
  have by0 : y.val<P := hw _
  have lim : 62*P<2^64 := by norm_num [P,AspisV8R17.RawReducer.P]
  obtain ⟨out,ro,vo⟩ := ExtractedMaskReducerOps.add_success x (FJb_WideSum4.wide y) (by rw [FJb_WideSum4.wide_val];omega)
  have roNative : (x+FJb_WideSum4.wide y : Result U64)=ok out := ro
  refine ⟨out,?_,?_⟩
  · change (do let x ← Array.index_usize a i;let y ← Array.index_usize w i;let out ← x+FJb_WideSum4.wide y;ok (out,(a,w)))=ok (out,(a,w))
    rw [rx,bind_tc_ok,ry,bind_tc_ok,roNative,bind_tc_ok]
  · rw [vo,FJb_WideSum4.wide_val]
    omega
#print axioms full
end AspisR1.JGj_InternalFullSum
end
