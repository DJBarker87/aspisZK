import Port4C_GeometryStd

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_GeometryRange
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeGeometryBody
variable {CoreError : Type}
abbrev M := aspis_core.field.M31

def selected (queries : Array U32 22#usize) (start end1 : Usize) : Result (Slice U32) :=
  core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U32))
    queries {start,«end»:=end1}

/-- Capacity reservations are the existing std/runtime model's empty vectors;
all native gathering/inversion/grouping instructions remain in the loop. -/
theorem native_range (ops : Ops CoreError) (queries : Array U32 22#usize)
    (start end1 : Usize) (order : start.val≤end1.val) (bound : end1.val≤22) :
    verifier.QueryGeometry.for_range ops queries start end1 = do
      let slice ← selected queries start end1
      verifier.QueryGeometry.for_range_loop0 ops ⟨slice,0⟩ start
        (alloc.vec.Vec.new M) (alloc.vec.Vec.new M) := by
  have ordered : ¬start>end1 := by change ¬start.val>end1.val; omega
  have bounded : ¬end1>Slice.len (Array.to_slice queries) := by
    change ¬end1.val>(Slice.len (Array.to_slice queries)).val
    rw [Port3_GeometryStage.queries_length]
    omega
  unfold verifier.QueryGeometry.for_range
  rw [if_neg ordered]
  simp only [lift,bind_tc_ok]
  rw [if_neg bounded]
  rfl

theorem accepted_range (ops : Ops CoreError) (queries : Array U32 22#usize)
    (start end1 : Usize) (out : verifier.QueryGeometry)
    (h : Port3_GeometryStage.geometry ops queries start end1=ok (.Ok out)) :
    ∃ slice,
      start.val≤end1.val ∧ end1.val≤22 ∧ selected queries start end1=ok slice ∧
      verifier.QueryGeometry.for_range_loop0 ops ⟨slice,0⟩ start
        (alloc.vec.Vec.new M) (alloc.vec.Vec.new M)=ok (.Ok out) := by
  have guards := Port3_GeometryStage.accepted_range ops queries start end1 out h
  have native := (Port3_QueryInstall.success_iff _ _).mp h
  rw [native_range ops queries start end1 guards.1 guards.2] at native
  obtain ⟨slice,hs,hloop⟩ := Port3_PushFrame.bind_success _ _ _ native
  exact ⟨slice,guards.1,guards.2,hs,hloop⟩

/-- Both actual source ranges, without evaluating any geometry table. -/
theorem both_ranges (ops : Ops CoreError) (queries : Array U32 22#usize) :
    verifier.QueryGeometry.for_range ops queries 0#usize 10#usize =
      (do let slice ← selected queries 0#usize 10#usize
          verifier.QueryGeometry.for_range_loop0 ops ⟨slice,0⟩ 0#usize
            (alloc.vec.Vec.new M) (alloc.vec.Vec.new M)) ∧
    verifier.QueryGeometry.for_range ops queries 10#usize 22#usize =
      (do let slice ← selected queries 10#usize 22#usize
          verifier.QueryGeometry.for_range_loop0 ops ⟨slice,0⟩ 10#usize
            (alloc.vec.Vec.new M) (alloc.vec.Vec.new M)) := by
  exact ⟨native_range ops queries 0#usize 10#usize (by decide) (by decide),
    native_range ops queries 10#usize 22#usize (by decide) (by decide)⟩

#print axioms native_range
#print axioms accepted_range
#print axioms both_ranges
end AspisR1.Port4C_GeometryRange
end
