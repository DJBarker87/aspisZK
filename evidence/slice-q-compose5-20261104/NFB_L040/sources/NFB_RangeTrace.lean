import NFB_GatherChain
set_option autoImplicit false
noncomputable section
namespace NFB_RangeTrace
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NEW_GeometryRawInterface NEW_GeometryDictionary NFB_GatherTrace
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

def Deployed (start finish : Usize) : Prop :=
 (start=0#usize ∧ finish=10#usize) ∨ (start=10#usize ∧ finish=22#usize)

theorem bounds (start finish : Usize) (scope : Deployed start finish) :
 start.val≤finish.val ∧ finish.val≤22 ∧
 (finish.val-start.val=10 ∨ finish.val-start.val=12) := by
 rcases scope with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide

/-- The actual selected query view is a precise window of the SAME original
array, with no fixed-query fixture or accepted-root premise. -/
theorem selected (queries : Array U32 22#usize) (start finish : Usize)
    (order : start.val≤finish.val) (bound : finish.val≤22) :
 ∃ slice : Slice U32,
  Port4C_GeometryRange.selected queries start finish=ok slice ∧
  slice.val=(queries.val.drop start.val).take (finish.val-start.val) ∧
  slice.val.length=finish.val-start.val := by
 obtain ⟨slice,read,contents,length⟩ := WP.spec_imp_exists
   (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
     (⟨start,finish⟩ : core.ops.range.Range Usize) (Array.to_slice queries) order
     (by change finish.val≤queries.val.length;rw [queries.property];exact bound))
 refine ⟨slice,read,?_,length⟩
 change slice.val=queries.val.extract start.val finish.val at contents
 simpa only [List.extract_eq_drop_take] using contents

/-- Root association for every raw query array. Trace existence and both
initial empty buffers come from the SAME actual-emitted Result. No inner
trace, child success, domain dictionary, or whole-buffer answer is supplied. -/
theorem complete (queries : Array U32 22#usize) (start finish : Usize)
    (order : start.val≤finish.val) (bound : finish.val≤22) :
 ∃ slice : Slice U32,
  Port4C_GeometryRange.selected queries start finish=ok slice ∧
  slice.val=(queries.val.drop start.val).take (finish.val-start.val) ∧
  slice.val.length=finish.val-start.val ∧
  Trace start ⟨slice,0⟩ (alloc.vec.Vec.new U32) (alloc.vec.Vec.new U32)
   (resultMap answer (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish)) := by
 obtain ⟨slice,read,contents,length⟩ := selected queries start finish order bound
 have root : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range adopted queries start finish=
     run start ⟨slice,0⟩ (alloc.vec.Vec.new U32) (alloc.vec.Vec.new U32) := by
  rw [Port4C_GeometryRange.native_range adopted queries start finish order bound,read,bind_tc_ok]
  rfl
 refine ⟨slice,read,contents,length,?_⟩
 rw [NEW_GeometryComplete.complete_raw,root]
 exact NFB_GatherTrace.complete start ⟨slice,0⟩ (alloc.vec.Vec.new U32)
   (alloc.vec.Vec.new U32) (finish.val-start.val) (by simp only;omega)

#print axioms bounds
#print axioms selected
#print axioms complete
end NFB_RangeTrace
end
