import CuSavingsGeometryRow
set_option autoImplicit false
namespace AspisR1.CuSavingsGeometryCache
open Aeneas Aeneas.Std Result ControlFlow AspisR1GeometryCandidate7
open CuSavingsGeometryRow
abbrev M := field.M31

private theorem bind_ok {A B : Type} (m : Result A) (k : A→Result B) (out : B)
    (h : (m >>= k)=.ok out) : ∃ value,m=.ok value ∧ k value=.ok out := by
  cases m with
  | fail error => cases h
  | div => cases h
  | ok value => exact ⟨value,rfl,h⟩

def Good (slice : Slice U32) (i : Nat) (cache : alloc.vec.Vec M) : Prop :=
  cache.val.length=i ∧ ∀ j, j < i → Origin (slice.val.getD j 0#u32) (cache.val.getD j 0#u32)

theorem good_push (slice : Slice U32) (i : Nat) (cache next : alloc.vec.Vec M) (z : M)
    (hg : Good slice i cache) (hz : Origin (slice.val.getD i 0#u32) z)
    (hnext : next.val=cache.val++[z]) : Good slice (i+1) next := by
  rcases hg with ⟨hlen,hgood⟩
  constructor
  · simp [hnext,hlen]
  · intro j hj
    by_cases hji : j < i
    · have hjlen : j < cache.val.length := by omega
      simpa [hnext,List.getD,List.getElem?_append_left hjlen] using hgood j hji
    · have hji : j=i := by omega
      subst j
      simpa [hnext,List.getD_append,hlen] using hz

theorem unroll (iter : core.slice.iter.Iter U32) (cache flat : alloc.vec.Vec M) :
    new.front_loop iter cache flat = (do
      let flow ← new.front_loop.body iter cache flat
      match flow with
      | .done out => .ok out
      | .cont (iter1,cache1,flat1) => new.front_loop iter1 cache1 flat1) := by
  unfold new.front_loop
  rw [loop]
  dsimp only
  cases h : new.front_loop.body iter cache flat with
  | fail e => simp only [h,bind_tc_fail]
  | div => simp only [h,bind_tc_div]
  | ok flow => cases flow <;> simp only [h,bind_tc_ok] <;> rfl

/-- Conditional on an actual complete source-loop success, every cached row
has its actual source origin. The loop's iterator and push are executed. -/
theorem loop_success (slice : Slice U32) (fuel i : Nat)
    (cache flat : alloc.vec.Vec M) (out : new.Front)
    (hlen : slice.val.length≤22) (hi : i≤slice.val.length)
    (hf : slice.val.length-i=fuel) (hg : Good slice i cache)
    (h : new.front_loop ⟨slice,i⟩ cache flat=.ok (.Ok out)) :
    Good slice slice.val.length out.line_z_values := by
  induction fuel generalizing i cache flat with
  | zero =>
    have he : i=slice.val.length := by omega
    have hn : core.slice.iter.IteratorSliceIter.next (⟨slice,i⟩ : core.slice.iter.Iter U32)=
        .ok (none,⟨slice,i⟩) := by
      unfold core.slice.iter.IteratorSliceIter.next
      change (if h:i<slice.val.length then Result.ok (some (slice.val[i]'h),(⟨slice,i+1⟩ : core.slice.iter.Iter U32)) else Result.ok (none,⟨slice,i⟩))=_
      rw [dif_neg (by omega)]
    rw [unroll] at h
    simp only [new.front_loop.body,hn,bind_tc_ok,uncurry_apply_pair] at h
    have ho := core.result.Result.Ok.inj (Result.ok.inj h)
    cases ho
    simpa only [he] using hg
  | succ fuel ih =>
    have hlt : i<slice.val.length := by omega
    have hn : core.slice.iter.IteratorSliceIter.next (⟨slice,i⟩ : core.slice.iter.Iter U32)=
        .ok (some (slice.val[i]'hlt),⟨slice,i+1⟩) := by
      unfold core.slice.iter.IteratorSliceIter.next
      change (if h:i<slice.val.length then Result.ok (some (slice.val[i]'h),(⟨slice,i+1⟩ : core.slice.iter.Iter U32)) else Result.ok (none,⟨slice,i⟩))=_
      rw [dif_pos hlt]
    rw [unroll] at h
    simp only [new.front_loop.body,hn,bind_tc_ok,uncurry_apply_pair,bind_assoc_eq] at h
    obtain ⟨r,hr,h⟩ := bind_ok _ _ _ h
    cases r with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at h
      cases h
    | Ok pair =>
      rcases pair with ⟨values,z⟩
      have hz := (row_origin (slice.val[i]'hlt) values z hr).1
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_assoc_eq,bind_tc_ok,lift] at h
      change (((do
        let flat1 ← alloc.vec.Vec.extend_from_slice field.M31.Insts.CoreCloneClone flat values.to_slice
        let cache1 ← alloc.vec.Vec.push cache z
        .ok (.cont ((⟨slice,i+1⟩ : core.slice.iter.Iter U32),cache1,flat1))) :
        Result (ControlFlow (core.slice.iter.Iter U32 × alloc.vec.Vec M × alloc.vec.Vec M)
          (core.result.Result new.Front verifier.Error))) >>=
        fun flow => match flow with
        | .done result => .ok result
        | .cont (iter1,cache1,flat1) => new.front_loop iter1 cache1 flat1)=.ok (.Ok out) at h
      simp only [bind_assoc_eq,bind_tc_ok] at h
      obtain ⟨flat1,hext,h⟩ := bind_ok _ _ _ h
      obtain ⟨cache1,hpush,h⟩ := bind_ok _ _ _ h
      have hmax : cache.val.length<Usize.max := by
        have hlarge : 22≤Usize.max := by scalar_tac
        have hc := hg.1
        omega
      obtain ⟨expected,hexpected,hval⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec cache z hmax)
      have hc : expected=cache1 := Result.ok.inj (hexpected.symm.trans hpush)
      have hcache : cache1.val=cache.val++[z] := by simpa only [hc] using hval
      have hz' : Origin (slice.val.getD i 0#u32) z := by simpa [List.getD,List.getElem?_eq_getElem hlt] using hz
      exact ih (i+1) cache1 flat1 (by omega) (by omega) (good_push slice i cache cache1 z hg hz' hcache) h

private theorem slice_shape (queries : Array U32 22#usize) (start finish : Usize)
    (slice : Slice U32)
    (h : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice U32)) queries {start,«end»:=finish}=.ok slice) :
    slice.val=queries.val.slice start.val finish.val := by
  rw [Array.index_SliceIndexRangeUsizeSlice] at h
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index at h
  split at h
  · exact (congrArg Subtype.val (Result.ok.inj h)).symm
  · cases h

/-- The actual successful complete cache constructor establishes its own
bounds, length, and the origin of every stored query node. -/
theorem source_success (queries : Array U32 22#usize) (start finish : Usize)
    (out : new.Front) (h : new.front queries start finish=.ok (.Ok out)) :
    start.val≤finish.val ∧ finish.val≤22 ∧
      out.line_z_values.val.length=finish.val-start.val ∧
      ∀ j, j < out.line_z_values.val.length →
        Origin (queries.val.getD (start.val+j) 0#u32) (out.line_z_values.val.getD j 0#u32) := by
  have h22 : queries.val.length=22 := by scalar_tac
  unfold new.front at h
  simp only [lift,bind_tc_ok] at h
  by_cases hs : start>finish
  · simp only [if_pos hs] at h
    cases h
  · simp only [if_neg hs] at h
    have hstart : start.val≤finish.val := by change ¬finish.val<start.val at hs;omega
    by_cases he : finish>Slice.len (Array.to_slice queries)
    · simp only [if_pos he] at h
      cases h
    · simp only [if_neg he] at h
      have hend : finish.val≤22 := by
        change ¬queries.val.length<finish.val at he
        omega
      obtain ⟨count,hcount,h⟩ := bind_ok _ _ _ h
      obtain ⟨capacity,hcapacity,h⟩ := bind_ok _ _ _ h
      obtain ⟨slice,hslice,h⟩ := bind_ok _ _ _ h
      simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,bind_tc_ok] at h
      have hshape := slice_shape queries start finish slice hslice
      have hlen : slice.val.length=finish.val-start.val := by
        rw [hshape,List.slice_length,h22]
        omega
      have hbound : slice.val.length≤22 := by omega
      have hi : Good slice 0 (alloc.vec.Vec.with_capacity M count) := by
        simp [Good,alloc.vec.Vec.with_capacity]
      have hg := loop_success slice slice.val.length 0
        (alloc.vec.Vec.with_capacity M count) (alloc.vec.Vec.with_capacity M capacity)
        out hbound (Nat.zero_le _) (Nat.sub_zero _) hi h
      refine ⟨hstart,hend,hg.1.trans hlen,?_⟩
      intro j hj
      have hjlen : j<slice.val.length := by simpa only [hg.1] using hj
      have hsource := hg.2 j hjlen
      have hp : (queries.val.slice start.val finish.val).getD j 0#u32=
          queries.val.getD (start.val+j) 0#u32 := by
        simp only [List.getD]
        rw [List.getElem?_slice start.val finish.val j queries.val (by omega)]
      simpa only [hshape,hp] using hsource

#print axioms good_push
#print axioms loop_success
#print axioms source_success
end AspisR1.CuSavingsGeometryCache
