import CuSavingsGeometryRow
set_option autoImplicit false
namespace AspisR1.CuSavingsGeometryFront
open Aeneas Aeneas.Std Result ControlFlow AspisR1GeometryCandidate7
open CuSavingsGeometryNode CuSavingsGeometryRow
abbrev Iter := core.slice.iter.Iter U32
abbrev Common := alloc.vec.Vec M × Nat
abbrev Rows := alloc.vec.Vec (Array M 5#usize)

def oldView (front : old.Front) : Common := (front.flat,front.denominators.val.length)
def newView (front : new.Front) : Common := (front.flat,front.line_z_values.val.length)
def observe {T : Type} (view : T→Common) (run : Result (core.result.Result T verifier.Error)) :
    Result (core.result.Result Common verifier.Error) := do
  let result ← run
  match result with
  | .Err error => .ok (.Err error)
  | .Ok value => .ok (.Ok (view value))

private theorem unroll {S T : Type} (body : S→Result (ControlFlow S (core.result.Result T verifier.Error)))
    (view : T→Common) (state : S) :
    observe view (loop body state) = (do
      let flow ← body state
      match flow with
      | .done value => observe view (.ok value)
      | .cont next => observe view (loop body next)) := by
  rw [loop]
  cases body state with
  | fail error => rfl
  | div => rfl
  | ok flow => cases flow <;> rfl

theorem push_success {T : Type} (values : alloc.vec.Vec T) (value : T)
    (h : values.val.length<22) :
    ∃ out,alloc.vec.Vec.push values value=.ok out ∧ out.val=values.val++[value] := by
  exact WP.spec_imp_exists (alloc.vec.Vec.push_spec values value (by scalar_tac))

theorem loops_equivalence (fuel : Nat) (iter : Iter) (rows : Rows)
    (cache flat : alloc.vec.Vec M) (ho : rows.val.length=iter.i)
    (hn : cache.val.length=iter.i) (hb : iter.slice.val.length≤22)
    (hi : iter.i≤ iter.slice.val.length) (hf : iter.slice.val.length-iter.i=fuel) :
    observe newView (new.front_loop iter cache flat)=
      observe oldView (old.front_loop iter rows flat) := by
  induction fuel generalizing iter rows cache flat with
  | zero =>
    have hge : ¬ iter.i< iter.slice.val.length := by omega
    have hnext : core.slice.iter.IteratorSliceIter.next iter=.ok (none,iter) := by
      unfold core.slice.iter.IteratorSliceIter.next
      simpa only [dif_neg (show ¬ iter.i< iter.slice.len from hge)]
    unfold new.front_loop old.front_loop
    rw [unroll,unroll]
    simp only [new.front_loop.body,old.front_loop.body,hnext,bind_tc_ok,uncurry_apply_pair,
      observe,newView,oldView,hn,ho]
  | succ fuel ih =>
    have hlt : iter.i< iter.slice.val.length := by omega
    let query := iter.slice.val[iter.i]'hlt
    let after : Iter := {iter with i:=iter.i+1}
    have hnext : core.slice.iter.IteratorSliceIter.next iter=.ok (some query,after) := by
      unfold core.slice.iter.IteratorSliceIter.next
      simp only [dif_pos (show iter.i< iter.slice.len from hlt),Slice.getElem_Nat_eq,query,after]
    unfold new.front_loop old.front_loop
    rw [unroll,unroll]
    simp only [new.front_loop.body,old.front_loop.body,hnext,bind_tc_ok,uncurry_apply_pair,
      row_equivalence]
    cases hr : new.row query with
    | fail error => simp only [hr,bind_tc_fail]
    | div => simp only [hr,bind_tc_div]
    | ok result =>
      try rw [hr]
      cases result with
      | Err error => rfl
      | Ok pair =>
        rcases pair with ⟨values,z⟩
        simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,uncurry_apply_pair,bind_assoc_eq]
        apply (bind_eq_iff (lift (Array.to_slice values)) _ _).mpr
        intro slice _
        apply (bind_eq_iff (alloc.vec.Vec.extend_from_slice field.M31.Insts.CoreCloneClone flat slice) _ _).mpr
        intro flat1 _
        obtain ⟨cache1,hcache,hcacheval⟩ := push_success cache z (by omega)
        obtain ⟨rows1,hrows,hrowsval⟩ := push_success rows values (by omega)
        simp only [hcache,hrows,bind_tc_ok]
        exact ih after rows1 cache1 flat1
          (by simp only [hrowsval,List.length_append,List.length_singleton,ho,after])
          (by simp only [hcacheval,List.length_append,List.length_singleton,hn,after])
          hb (by simp only [after];omega) (by simp only [after];omega)


private theorem slice_bound (queries : Array U32 22#usize) (start finish : Usize)
    (slice : Slice U32)
    (h : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice U32)) queries {start,«end»:=finish}=.ok slice) :
    slice.val.length≤22 := by
  rw [Array.index_SliceIndexRangeUsizeSlice] at h
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index at h
  split at h
  · have he := congrArg Subtype.val (Result.ok.inj h)
    change queries.val.slice start.val finish.val=slice.val at he
    rw [← he,List.slice_length]
    have hlen : queries.val.length=22 := by scalar_tac
    exact Nat.le_trans (Nat.min_le_right _ _) (by omega)
  · cases h

/-- Original row storage and new cached-z storage produce the same flat
inversion input and row count, preserving every checked failure/divergence. -/
theorem source_equivalence (queries : Array U32 22#usize) (start finish : Usize) :
    observe newView (new.front queries start finish)=
      observe oldView (old.front queries start finish) := by
  unfold new.front old.front
  simp only [lift,bind_tc_ok]
  by_cases hs : start>finish
  · simp only [if_pos hs,observe,bind_tc_ok]
  · simp only [if_neg hs]
    by_cases he : finish>Slice.len (Array.to_slice queries)
    · simp only [if_pos he,observe,bind_tc_ok]
    · simp only [if_neg he,observe,bind_assoc_eq]
      apply (bind_eq_iff (finish-start : Result Usize) _ _).mpr
      intro count _
      apply (bind_eq_iff (count*5#usize : Result Usize) _ _).mpr
      intro capacity _
      apply (bind_eq_iff (core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice U32)) queries {start,«end»:=finish}) _ _).mpr
      intro slice hslice
      simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,bind_tc_ok]
      change observe newView (new.front_loop {slice,i:=0} (alloc.vec.Vec.with_capacity M count)
          (alloc.vec.Vec.with_capacity M capacity))=
        observe oldView (old.front_loop {slice,i:=0}
          (alloc.vec.Vec.with_capacity (Array M 5#usize) count) (alloc.vec.Vec.with_capacity M capacity))
      exact loops_equivalence slice.val.length _ _ _ _ rfl rfl
        (slice_bound queries start finish slice hslice) (Nat.zero_le _) (Nat.sub_zero _)

/-- The unchanged inversion tail may be any common computation of precisely
its original inputs: flat denominators and row count. -/
theorem inversion_context {T : Type} (queries : Array U32 22#usize) (start finish : Usize)
    (tail : Common→Result T) (error : verifier.Error→Result T) :
    (do let result ← new.front queries start finish
        match result with | .Err e => error e | .Ok front => tail (newView front))=
    (do let result ← old.front queries start finish
        match result with | .Err e => error e | .Ok front => tail (oldView front)) := by
  have bind_view {F : Type} (view : F→Common) (run : Result (core.result.Result F verifier.Error)) :
      (do let result ← run
          match result with | .Err e => error e | .Ok front => tail (view front))=
      (do let result ← observe view run
          match result with | .Err e => error e | .Ok front => tail front) := by
    cases run with
    | fail e => rfl
    | div => rfl
    | ok value => cases value <;> rfl
  rw [bind_view newView,bind_view oldView,source_equivalence]

#print axioms source_equivalence
#print axioms inversion_context
#print axioms push_success
#print axioms loops_equivalence
end AspisR1.CuSavingsGeometryFront
