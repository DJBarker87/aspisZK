import BatchBackwardEntrypoint
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1BatchBackward.Proof
open R17CurrentM31Semantics alloc.vec

def CanonicalVec (v : Vec U32) : Prop := ∀ x ∈ v.val, x.val < 2147483647

theorem set_canonical (v : Vec U32) (j : Usize) (x : U32)
    (hv : CanonicalVec v) (hx : x.val < 2147483647) : CanonicalVec (v.set j x) := by
  intro a ha
  change a ∈ v.val.set j.val x at ha
  rcases List.mem_or_eq_of_mem_set ha with h | h
  · exact hv a h
  · subst a
    exact hx

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

private theorem index_mut_success (v : Vec U32) (i : Usize)
    (out : U32 × (U32 → Vec U32)) (hi : i.val < v.val.length)
    (h : Vec.index_mut (core.slice.index.SliceIndexUsizeSlice U32) v i = .ok out) :
    out.2 = v.set i := by
  rw [Vec.index_mut_slice_index] at h
  obtain ⟨r,ho,hv⟩ := WP.spec_imp_exists (Vec.index_mut_usize_spec v i hi)
  have he : r = out := Result.ok.inj (ho.symm.trans h)
  simpa only [he] using hv.2

theorem backward_body_canonical (flat pref state : Vec U32) (suffix : U32) (iter : ReverseRange)
    (out : ControlFlow (ReverseRange × U32 × Vec U32) (Vec U32))
    (hstart : iter.iter.start = 0#usize) (hpos : 0 < iter.iter.end.val)
    (hbound : iter.iter.end.val ≤ state.val.length) (hcanon : CanonicalVec state)
    (h : backward_loop.body currentMul flat pref iter suffix state = .ok out) :
    ∃ suffix1 state1,
      let j := Usize.wrapping_sub iter.iter.end 1#usize
      out = .cont (⟨{iter.iter with «end»:=j}⟩,suffix1,state1) ∧
      CanonicalVec state1 ∧ state1.val.length = state.val.length := by
  have hstep : iter.iter.start.val < iter.iter.end.val := by rw [hstart]; exact hpos
  have hn := reverse_next_step iter hstep
  let j := Usize.wrapping_sub iter.iter.end 1#usize
  have hj : j.val = iter.iter.end.val - 1 := wrapping_sub_one_val _ (by omega)
  have hjs : j.val < state.val.length := by omega
  unfold backward_loop.body at h
  rw [hn] at h
  simp only [bind_tc_ok] at h
  rcases bind_ok_inv h with ⟨p,_,h⟩
  rcases bind_ok_inv h with ⟨w,hmul,h⟩
  rcases bind_ok_inv h with ⟨setter,hset,h⟩
  rcases setter with ⟨old,back⟩
  rcases bind_ok_inv h with ⟨x,_,h⟩
  rcases bind_ok_inv h with ⟨suffix1,_,h⟩
  have hb : back = state.set j := index_mut_success state j (old,back) hjs hset
  obtain ⟨z,hz,_,hzc⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod suffix p
  have hez : z = w := Result.ok.inj (hz.symm.trans hmul)
  have hw : w.val < 2147483647 := by simpa only [hez] using hzc
  refine ⟨suffix1,state.set j w,?_,set_canonical state j w hcanon hw,set_length state j w⟩
  rw [←Result.ok.inj h,hb]

#print axioms set_canonical
#print axioms backward_body_canonical
end AspisR1BatchBackward.Proof
