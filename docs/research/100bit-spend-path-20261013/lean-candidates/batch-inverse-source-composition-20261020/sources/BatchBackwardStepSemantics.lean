import BatchBackwardRangeFacts
import R17CurrentM31Semantics
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1BatchBackward.Proof
open R17CurrentM31Semantics alloc.vec
abbrev Mul := U32 → U32 → Result U32

def RefinesMul (mul : Mul) : Prop := ∀ a b z, mul a b = .ok z →
  decode z = decode a * decode b

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

private theorem index_success (v : Vec U32) (i : Usize) (x : U32)
    (hi : i.val < v.val.length)
    (h : Vec.index (core.slice.index.SliceIndexUsizeSlice U32) v i = .ok x) :
    x = v.val[i.val] := by
  rw [Vec.index_slice_index] at h
  obtain ⟨out,ho,hv⟩ := WP.spec_imp_exists (Vec.index_usize_spec v i hi)
  have he : out = x := Result.ok.inj (ho.symm.trans h)
  simpa only [he] using hv

private theorem index_mut_success (v : Vec U32) (i : Usize)
    (out : U32 × (U32 → Vec U32)) (hi : i.val < v.val.length)
    (h : Vec.index_mut (core.slice.index.SliceIndexUsizeSlice U32) v i = .ok out) :
    out.2 = v.set i := by
  rw [Vec.index_mut_slice_index] at h
  obtain ⟨r,ho,hv⟩ := WP.spec_imp_exists (Vec.index_mut_usize_spec v i hi)
  have he : r = out := Result.ok.inj (ho.symm.trans h)
  simpa only [he] using hv.2

theorem backward_body_step (mul : Mul) (hr : RefinesMul mul)
    (flat pref state : Vec U32) (suffix : U32) (iter : ReverseRange)
    (out : ControlFlow (ReverseRange × U32 × Vec U32) (Vec U32))
    (hstart : iter.iter.start = 0#usize) (hpos : 0 < iter.iter.end.val)
    (hflat : iter.iter.end.val ≤ flat.val.length)
    (hpref : iter.iter.end.val ≤ pref.val.length)
    (hstate : iter.iter.end.val ≤ state.val.length)
    (h : backward_loop.body mul flat pref iter suffix state = .ok out) :
    ∃ suffix1 written,
      let j := Usize.wrapping_sub iter.iter.end 1#usize
      ∃ hjp : j.val < pref.val.length, ∃ hjf : j.val < flat.val.length,
      out = .cont (⟨{iter.iter with «end»:=j}⟩,suffix1,state.set j written) ∧
      decode written = decode suffix * decode (pref.val[j.val]'hjp) ∧
      decode suffix1 = decode suffix * decode (flat.val[j.val]'hjf) := by
  have hstep : iter.iter.start.val < iter.iter.end.val := by rw [hstart]; exact hpos
  have hnext := reverse_next_step iter hstep
  let j := Usize.wrapping_sub iter.iter.end 1#usize
  have hj : j.val = iter.iter.end.val - 1 := wrapping_sub_one_val _ (by omega)
  have hjf : j.val < flat.val.length := by omega
  have hjp : j.val < pref.val.length := by omega
  have hjs : j.val < state.val.length := by omega
  unfold backward_loop.body at h
  rw [hnext] at h
  simp only [bind_tc_ok] at h
  rcases bind_ok_inv h with ⟨p,hread,h⟩
  rcases bind_ok_inv h with ⟨written,hmul,h⟩
  rcases bind_ok_inv h with ⟨setter,hset,h⟩
  rcases setter with ⟨old,back⟩
  rcases bind_ok_inv h with ⟨x,hreadflat,h⟩
  rcases bind_ok_inv h with ⟨suffix1,hmulflat,h⟩
  have hb : back = state.set j := index_mut_success state j (old,back) hjs hset
  refine ⟨suffix1,written,hjp,hjf,?_,?_,?_⟩
  · rw [←Result.ok.inj h,hb]
  · rw [hr suffix p written hmul,index_success pref j p hjp hread]
  · rw [hr suffix x suffix1 hmulflat,index_success flat j x hjf hreadflat]

#print axioms backward_body_step
end AspisR1BatchBackward.Proof
