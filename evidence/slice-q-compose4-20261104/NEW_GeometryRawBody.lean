import NEW_GeometryRawHelpers
import NEW_ResultMapSyntax
set_option autoImplicit false
namespace NEW_GeometryRawBody
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NEW_GeometryRawInterface NEW_GeometryRawHelpers
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
abbrev State := core.slice.iter.Iter U32 × alloc.vec.Vec U32 × alloc.vec.Vec U32

theorem map_iterator {B I F Item : Type} (it : core.iter.traits.iterator.Iterator I Item)
    (f : core.ops.function.FnMut F Item B) :
    NEW_GeometryActual.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator it f = ops.mapIterator it f := by
  rfl

theorem bind_congr {A B : Type} (m : Result A) (k l : A → Result B)
    (h : ∀ a, k a=l a) : (m >>= k) = (m >>= l) := by
  exact congrArg (fun k => m >>= k) (funext h)

/-- Exact one-body Result conversion on the SAME iterator and both Vecs.
All child operations are the concrete emitted dictionary, with no free replies. -/
theorem step (start : Usize) (iter : core.slice.iter.Iter U32)
    (lines flat : alloc.vec.Vec U32) :
    resultMap (NEW_LoopMap.flowMap answer)
      (NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0.body start iter lines flat) =
      Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body ops start iter lines flat := by
  simp only [NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0.body,
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body,
    resultMap_bind,NEW_LoopMap.map_ok,NEW_LoopMap.flowMap,
    ←zero_callback,←outer_callback,←backward,←clone,←map_iterator]
  simp only [ops,bind_assoc_eq,bind_tc_ok,apply_ite,NEW_LoopMap.map_ok,
    NEW_LoopMap.flowMap,answer,geometry,error]
  congr 1
  funext following
  rcases following with ⟨query,iter1⟩
  all_goals
    repeat' first
    | rfl
    | simp only [uncurry,resultMap_bind,NEW_LoopMap.map_ok,NEW_LoopMap.flowMap,
        answer,geometry,error,bind_assoc_eq,bind_tc_ok,←clone,←map_iterator,
        alloc.vec.Vec.is_empty,core.result.Result.map_err,Port4C_GeometryStd.mapError,
        NEW_GeometryActual.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError,
        NEW_GeometryActual.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
        NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError,
        NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
        NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError,
        NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
        Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError,
        Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
        Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError,
        Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
        Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError,
        Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
    | (apply bind_congr; intro)
    | split

#print axioms map_iterator
#print axioms bind_congr
#print axioms step
end NEW_GeometryRawBody
