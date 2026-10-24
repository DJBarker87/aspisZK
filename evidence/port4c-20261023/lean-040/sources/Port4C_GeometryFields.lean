import Port4C_GeometryLoop

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_GeometryFields
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeGeometryBody
variable {CoreError : Type}
abbrev M := aspis_core.field.M31

theorem selection_fields (queries : Array U32 22#usize) (start end1 : Usize)
    (slice : Slice U32) (ordered : start.val≤end1.val) (within : end1.val≤22)
    (h : Port4C_GeometryRange.selected queries start end1=ok slice) :
    slice.val=(queries.val.drop start.val).take (end1.val-start.val) ∧
    slice.val.length=end1.val-start.val := by
  obtain ⟨out,run,contents,length⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
      ⟨start,end1⟩ (Array.to_slice queries) ordered (by change end1.val≤queries.val.length; rw [queries.property]; exact within))
  have same : out=slice := Result.ok.inj (run.symm.trans h)
  subst out
  refine ⟨?_,length⟩
  change slice.val=queries.val.extract start.val end1.val at contents
  simpa only [List.extract_eq_drop_take] using contents

/-- Complete native gather fields and SAME terminal inversion/grouping input.
No raw-size, line_z-length or zero-test premise is supplied by the caller. -/
theorem accepted (ops : Ops CoreError) (queries : Array U32 22#usize)
    (start end1 : Usize) (out : verifier.QueryGeometry)
    (h : Port3_GeometryStage.geometry (Port4C_GeometryStd.install ops)
      queries start end1=ok (.Ok out)) :
    ∃ flat terminal,
      start.val≤end1.val ∧ end1.val≤22 ∧ out.start=start ∧
      out.line_z.val.length=end1.val-start.val ∧
      flat.val.length=5*(end1.val-start.val) ∧
      (∀ x ∈ flat.val, x≠0#u32) ∧
      verifier.QueryGeometry.for_range_loop0.body (Port4C_GeometryStd.install ops)
        start terminal out.line_z flat=ok (done (.Ok out)) ∧
      terminal.i=terminal.slice.val.length := by
  obtain ⟨slice,order,bound,hs,run⟩ := Port4C_GeometryRange.accepted_range
    (Port4C_GeometryStd.install ops) queries start end1 out h
  have selected := selection_fields queries start end1 slice order bound hs
  obtain ⟨zs,flat,terminal,hstart,hline,hzl,hfl,hnz,ht,hslice,hi⟩ :=
    Port4C_GeometryLoop.accepted ops start ⟨slice,0⟩ (alloc.vec.Vec.new M)
      (alloc.vec.Vec.new M) out slice.val.length (by simp) (by simp) run
  refine ⟨flat,terminal,order,bound,hstart,?_,?_,hnz,?_,?_⟩
  · rw [hline]
    simpa only [alloc.vec.Vec.new,List.length_nil,Nat.zero_add,selected.2] using hzl
  · simpa only [alloc.vec.Vec.new,List.length_nil,Nat.zero_add,selected.2] using hfl
  · rw [hline]; exact ht
  · rw [hslice]; exact hi

/-- Both actual ranges yield the real line_z size and the nonzero inversion
inputs of size50 /60 respectively. -/
theorem both_sizes (ops : Ops CoreError) (queries : Array U32 22#usize)
    (first second : verifier.QueryGeometry)
    (h0 : Port3_GeometryStage.geometry (Port4C_GeometryStd.install ops)
      queries 0#usize 10#usize=ok (.Ok first))
    (h1 : Port3_GeometryStage.geometry (Port4C_GeometryStd.install ops)
      queries 10#usize 22#usize=ok (.Ok second)) :
    first.start=0#usize ∧ first.line_z.val.length=10 ∧
    second.start=10#usize ∧ second.line_z.val.length=12 := by
  obtain ⟨_,_,_,_,hs0,hz0,_⟩ := accepted ops queries 0#usize 10#usize first h0
  obtain ⟨_,_,_,_,hs1,hz1,_⟩ := accepted ops queries 10#usize 22#usize second h1
  exact ⟨hs0,hz0,hs1,hz1⟩

#print axioms selection_fields
#print axioms accepted
#print axioms both_sizes
end AspisR1.Port4C_GeometryFields
end
