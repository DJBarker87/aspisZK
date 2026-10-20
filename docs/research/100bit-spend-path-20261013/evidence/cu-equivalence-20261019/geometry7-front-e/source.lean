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
      simpa only [dif_pos (show iter.i< iter.slice.len from hlt)]
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

#print axioms push_success
#print axioms loops_equivalence
end AspisR1.CuSavingsGeometryFront
