import Port4C_GeometryInverse
import Port4C_CollectLoop

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_GeometryTerminal
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeGeometryBody
open Port3_PushFrame (bind_success)
variable {CoreError : Type}

def install (ops : Ops CoreError) : Ops CoreError :=
  Port4C_CollectStd.install (Port4C_GeometryInverse.install ops)

/-- The successful terminal branch uses the SAME resized buffer, prefix,
inverse, backwards traversal and collector. Field nonzero is a separate
obligation; a raw zero test alone is insufficient. -/
theorem terminal (ops : Ops CoreError)
    (multiply : ops.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : ops.op7=ok (1#u32))
    (inverseLeaf : ops.op11=Port4C_InverseExecution.inverse_owned)
    (start : Usize) (iter : core.slice.iter.Iter U32)
    (zs flat : alloc.vec.Vec U32) (out : verifier.QueryGeometry)
    (ending : iter.i=iter.slice.val.length)
    (count : zs.val.length≤22) (size : flat.val.length=5*zs.val.length)
    (positive : 0<zs.val.length)
    (nonzero : ∀ x ∈ flat.val, S7JoinBasisMachine.decode x≠0)
    (accepted : verifier.QueryGeometry.for_range_loop0.body (install ops)
      start iter zs flat=ok (done (.Ok out))) :
    ∃ inverse,
      out.start=start ∧ out.line_z=zs ∧
      inverse.val.length=flat.val.length ∧
      (∀ j, j<flat.val.length →
        S7JoinBasisMachine.decode (Port4C_BatchInverse.cell inverse.val j)=
          (S7JoinBasisMachine.decode (Port4C_BatchInverse.cell flat.val j))⁻¹) ∧
      out.inverses.val=(List.range zs.val.length).map (Port4C_CollectLoop.record inverse) := by
  have next : core.slice.iter.IteratorSliceIter.next iter=ok (none,iter) := by
    unfold core.slice.iter.IteratorSliceIter.next
    split
    · rename_i active; have sz := Slice.len_val iter.slice; omega
    · rfl
  unfold verifier.QueryGeometry.for_range_loop0.body at accepted
  rw [next,bind_tc_ok] at accepted
  have empty : (install ops).op4 Global flat=ok false := by
    change ok flat.val.isEmpty=ok false
    have hn : flat.val≠[] := by intro h; rw [h] at size; simp only [List.length_nil] at size; omega
    simp only [List.isEmpty_eq_false_iff.mpr hn]
  rw [empty,bind_tc_ok] at accepted
  simp only [Bool.false_eq_true,if_false] at accepted
  obtain ⟨pref,hpref,accepted⟩ := bind_success _ _ _ accepted
  rcases pref with ⟨prefixes,product⟩
  obtain ⟨suffix,hsuffix,accepted⟩ := bind_success _ _ _ accepted
  obtain ⟨zero,hzero,accepted⟩ := bind_success _ _ _ accepted
  obtain ⟨resized,hresize,accepted⟩ := bind_success _ _ _ accepted
  obtain ⟨rev,hrev,accepted⟩ := bind_success _ _ _ accepted
  obtain ⟨inverse,hback,accepted⟩ := bind_success _ _ _ accepted
  obtain ⟨mapped,hmap,accepted⟩ := bind_success _ _ _ accepted
  obtain ⟨groups,hcollect,accepted⟩ := bind_success _ _ _ accepted
  cases Result.ok.inj accepted
  have resizeSize : resized.val.length=flat.val.length := by
    change alloc.vec.Vec.resize core.marker.CopyU32.cloneInst
      (alloc.vec.Vec.with_capacity U32 (alloc.vec.Vec.len flat))
      (alloc.vec.Vec.len flat) zero=ok resized at hresize
    unfold alloc.vec.Vec.resize at hresize
    split at hresize
    · cases Result.ok.inj hresize
      simp only [List.length_resize,alloc.vec.Vec.len_val]
    · obtain ⟨xs,hxs,hresize⟩ := bind_success _ _ _ hresize
      cases Result.ok.inj hresize
      simp only [List.length_resize,alloc.vec.Vec.len_val]
  have pipeline : Port4C_GeometryInverse.pipeline (install ops) flat resized=ok inverse := by
    unfold Port4C_GeometryInverse.pipeline
    have hpref1 : Port4C_GeometryInverse.prefixCall (install ops) flat.deref=ok (prefixes,product) := hpref
    rw [hpref1,bind_tc_ok]
    dsimp only
    rw [hsuffix,bind_tc_ok]
    have sameRev : rev=Port4C_Reverse.reverse (alloc.vec.Vec.len flat) := (Result.ok.inj hrev).symm
    rw [←sameRev]
    exact hback
  obtain ⟨inv,run,len,values⟩ := Port4C_GeometryInverse.total (install ops)
    multiply one inverseLeaf flat resized (by omega) resizeSize nonzero
  have same : inv=inverse := Result.ok.inj (run.symm.trans pipeline)
  subst inv
  obtain ⟨collected,collectRun,contents,groupLen⟩ := Port4C_CollectLoop.total
    (Port4C_GeometryInverse.install ops) inverse (alloc.vec.Vec.len zs) count (by simpa only [alloc.vec.Vec.len_val] using len.trans size)
  have mappedEq : mapped=⟨{start:=0#usize,«end»:=alloc.vec.Vec.len zs},inverse⟩ :=
    (Result.ok.inj hmap).symm
  subst mapped
  have sameGroups : collected=groups := Result.ok.inj (collectRun.symm.trans hcollect)
  subst collected
  exact ⟨inverse,rfl,rfl,len,values,contents⟩

#print axioms terminal
end AspisR1.Port5Q1_GeometryTerminal
end
