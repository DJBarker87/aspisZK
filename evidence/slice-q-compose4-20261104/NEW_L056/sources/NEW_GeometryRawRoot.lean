import NEW_GeometryRawBody
set_option autoImplicit false
namespace NEW_GeometryRawRoot
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NEW_GeometryRawInterface NEW_GeometryRawBody
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

def body (start : Usize) (s : State) :=
  let (it,lines,flat) := s
  NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0.body start it lines flat

theorem complete_loop (start : Usize) (iter : core.slice.iter.Iter U32)
    (lines flat : alloc.vec.Vec U32) :
    resultMap answer (NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0 iter start lines flat) =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0 ops iter start lines flat := by
  unfold NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0
  change resultMap answer (loop (body start) (iter,lines,flat)) = _
  rw [NEW_LoopMap.complete (body start) answer answerBack answer_roundtrip answer_reverse]
  congr 1
  funext s
  rcases s with ⟨it,ls,fl⟩
  exact step start it ls fl

/-- Full emitted actual root: every rejection, failure and divergence as well
as every lane of the successful geometry; no acceptance premise. -/
theorem complete (queries : Array U32 22#usize) (start finish : Usize) :
    resultMap answer (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish) =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range ops queries start finish := by
  unfold NEW_GeometryActual.verifier.QueryGeometry.for_range
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range
  repeat' first
  | rfl
  | simp only [apply_ite,resultMap_bind,NEW_LoopMap.map_ok,answer,geometry,error,complete_loop]
  | (apply bind_congr; intro)
  | split

#print axioms body
#print axioms complete_loop
#print axioms complete
end NEW_GeometryRawRoot
