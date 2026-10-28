import NDO_JGj_InternalShift
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_InternalLaneCall
open Aeneas Aeneas.Std Result FIq_Native
open JGj_RawBounds
open FJb_TailCell (cell)
abbrev Callback := state_only_poseidon.internal_linear_lazy.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU64
theorem source (a : Raw) (w : Words) (lane limb : Usize)
    (hl : 1≤lane.val) (hh : lane.val<16) (hi : limb.val<(4#usize).val)
    (ha : Bound a (62*P)) (hw : Canonical w) :
    ∃ out,Callback.call_mut (a,w,lane) limb=ok (out,(a,w,lane)) := by
  let x := cell a ⟨limb.val,hi⟩
  let y := cell w ⟨limb.val,hi⟩
  have rx : Array.index_usize a limb=ok x := RawPoseidonExternalRowReads.array_index_usize_ok a limb hi
  have ry : Array.index_usize w limb=ok y := RawPoseidonExternalRowReads.array_index_usize_ok w limb hi
  obtain ⟨delta,shift,rd,rs,bs⟩ := JGj_InternalShift.read lane hl hh
  obtain ⟨shifted,rt,bt⟩ := JGj_InternalShift.word y shift (hw _) bs
  have bx : x.val<62*P := ha _
  have lim : 62*P+2^47<2^64 := by norm_num [P,AspisV8R17.RawReducer.P]
  obtain ⟨out,ro,_⟩ := ExtractedMaskReducerOps.add_success x shifted (by omega)
  have roNative : (x+shifted : Result U64)=ok out := ro
  refine ⟨out,?_⟩
  change (do
    let x ← Array.index_usize a limb
    let y ← Array.index_usize w limb
    let delta ← lane-1#usize
    let shift ← Array.index_usize state_only_poseidon.internal_linear_lazy.SHIFTS delta
    let t ← FJb_WideSum4.wide y <<< shift
    let out ← x+t
    ok (out,(a,w,lane)))=ok (out,(a,w,lane))
  rw [rx,bind_tc_ok,ry,bind_tc_ok,rd,bind_tc_ok,rs,bind_tc_ok,rt,bind_tc_ok,roNative,bind_tc_ok]
#print axioms source
end AspisR1.JGj_InternalLaneCall
end
