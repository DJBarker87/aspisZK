import JFv_TX2_GeometryOps
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_Terminal
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeGeometryBody

theorem source {C : Type} (err : C) (seed : Ops C)
    (start : Usize) (it : core.slice.iter.Iter U32) (zs flat : alloc.vec.Vec U32)
    (ending : it.i=it.slice.val.length) (count : zs.val.length≤22)
    (size : flat.val.length=5*zs.val.length) (positive : 0<zs.val.length)
    (nonzero : ∀ x∈flat.val,S7JoinBasisMachine.decode x≠0) :
    ∃ out : verifier.QueryGeometry,
      verifier.QueryGeometry.for_range_loop0.body (JFv_TX2_GeometryOps.install err seed)
        start it zs flat=ok (done (.Ok out)) ∧
      out.start=start ∧ out.line_z=zs ∧ out.inverses.val.length=zs.val.length := by
  let ops := JFv_TX2_GeometryOps.install err seed
  obtain ⟨resized,resize,hresize⟩ := WP.spec_imp_exists (alloc.vec.Vec.resize_spec
    core.marker.CopyU32.cloneInst (alloc.vec.Vec.with_capacity U32 (alloc.vec.Vec.len flat))
    (alloc.vec.Vec.len flat) 0#u32 (by rfl))
  have rsize : resized.val.length=flat.val.length := by
    rw [hresize,List.resize_length,alloc.vec.Vec.len_val]
  obtain ⟨inverse,invert,len,values⟩ := Port4C_GeometryInverse.total ops rfl rfl
    (SAQ_Inverse.source_eq_reference) flat resized (by omega) rsize nonzero
  unfold Port4C_GeometryInverse.pipeline at invert
  obtain ⟨pair,hpref,invert⟩ := Port3_PushFrame.bind_success _ _ _ invert
  rcases pair with ⟨pref,prod⟩
  obtain ⟨suffix,hsuffix,hback⟩ := Port3_PushFrame.bind_success _ _ _ invert
  obtain ⟨groups,collect,contents,glen⟩ := Port4C_CollectLoop.total
    (Port4C_GeometryInverse.install (SAQ_Constructor.install err seed)) inverse
    (alloc.vec.Vec.len zs) count (by simpa only [alloc.vec.Vec.len_val] using len.trans size)
  let out : verifier.QueryGeometry := ⟨start,groups,zs⟩
  refine ⟨out,?_,rfl,rfl,?_⟩
  · have next : core.slice.iter.IteratorSliceIter.next it=ok (none,it) := by
      unfold core.slice.iter.IteratorSliceIter.next
      split
      · rename_i active
        change it.i < it.slice.val.length at active
        omega
      · rfl
    have empty : ops.op4 Global flat=ok false := by
      change ok flat.val.isEmpty=ok false
      have hn : flat.val≠[] := by intro h;rw [h] at size;simp only [List.length_nil] at size;omega
      rw [List.isEmpty_eq_false_iff.mpr hn]
    unfold verifier.QueryGeometry.for_range_loop0.body
    rw [next,bind_tc_ok,empty,bind_tc_ok]
    simp only [Bool.false_eq_true,if_false]
    change (do
      let (pref,prod) ← Port4C_GeometryInverse.prefixCall ops flat.deref
      let suffix ← ops.op11 prod
      let zeros ← alloc.vec.Vec.resize core.marker.CopyU32.cloneInst
        (alloc.vec.Vec.with_capacity U32 (alloc.vec.Vec.len flat)) (alloc.vec.Vec.len flat) 0#u32
      let rev ← ok (Port4C_Reverse.reverse (alloc.vec.Vec.len flat))
      let inv ← verifier.QueryGeometry.for_range_loop0_loop0 ops rev flat pref suffix zeros
      let gr ← Port4C_CollectLoop.collect
        (Port4C_GeometryInverse.install (SAQ_Constructor.install err seed)) inv (alloc.vec.Vec.len zs)
      ok (done (core.result.Result.Ok (⟨start,gr,zs⟩ : verifier.QueryGeometry))))=_
    rw [resize]
    simp only [bind_tc_ok]
    rw [hpref,bind_tc_ok,hsuffix,bind_tc_ok,hback,bind_tc_ok,collect,bind_tc_ok]
  · simpa only [alloc.vec.Vec.len_val] using glen
#print axioms source
end AspisR1.JFv_TX2_Terminal
end
