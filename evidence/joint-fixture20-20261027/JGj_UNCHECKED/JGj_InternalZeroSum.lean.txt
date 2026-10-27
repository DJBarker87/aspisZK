import JGj_RawBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_InternalZeroSum
open Aeneas Aeneas.Std Result FIq_Native
open JGj_RawBounds
open FJb_TailCell (cell)
abbrev Full := state_only_poseidon.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
abbrev Zero := state_only_poseidon.internal_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64
theorem zero (a : Raw) (w : Words) (i : Usize) (hi : i.val<(4#usize).val)
    (ha : Bound a (61*P)) (hw : Canonical w) :
    ∃ out,Zero.call_mut (a,w) i=ok (out,(a,w)) := by
  let x := cell a ⟨i.val,hi⟩
  let y := cell w ⟨i.val,hi⟩
  have rx : Array.index_usize a i=ok x := RawPoseidonExternalRowReads.array_index_usize_ok a i hi
  have ry : Array.index_usize w i=ok y := RawPoseidonExternalRowReads.array_index_usize_ok w i hi
  have bx : x.val<61*P := ha _
  have by0 : y.val<P := hw _
  have vp : (FJb_WideSum4.wide field.P).val=P := by
    rw [FJb_WideSum4.wide_val]
    norm_num [field.P,P,AspisV8R17.RawReducer.P]
  have lim : 62*P<2^64 := by norm_num [P,AspisV8R17.RawReducer.P]
  obtain ⟨withP,rp,vp0⟩ := ExtractedMaskReducerOps.add_success x (FJb_WideSum4.wide field.P) (by rw [vp];omega)
  have safe : (FJb_WideSum4.wide y).val≤withP.val := by rw [FJb_WideSum4.wide_val,vp0,vp];omega
  obtain ⟨out,ro,_⟩ := ExtractedMaskReducerOps.sub_success withP (FJb_WideSum4.wide y) safe
  have rpNative : (x+FJb_WideSum4.wide field.P : Result U64)=ok withP := rp
  have roNative : (withP-FJb_WideSum4.wide y : Result U64)=ok out := ro
  refine ⟨out,?_⟩
  change (do let x ← Array.index_usize a i;let p ← x+FJb_WideSum4.wide field.P;let y ← Array.index_usize w i;let out ← p-FJb_WideSum4.wide y;ok (out,(a,w)))=ok (out,(a,w))
  rw [rx,bind_tc_ok,rpNative,bind_tc_ok,ry,bind_tc_ok,roNative,bind_tc_ok]
#print axioms zero
end AspisR1.JGj_InternalZeroSum
end
