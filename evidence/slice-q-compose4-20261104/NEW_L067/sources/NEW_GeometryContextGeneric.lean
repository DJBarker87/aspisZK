import NEW_GeometryRawRoot
set_option autoImplicit false
namespace NEW_GeometryContextGeneric
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NEW_GeometryRawBody
variable {CE : Type}

def replace (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32) : Port3_NativeGeometryBody.Ops CE :=
  {o with op8:=sub,op10:=double}

theorem reverse (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32)
    (it : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (flat pref : alloc.vec.Vec U32) (suffix : U32) (inv : alloc.vec.Vec U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0 (replace o sub double) it flat pref suffix inv =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0 o it flat pref suffix inv := by rfl

theorem zero_callback (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool (replace o sub double) =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool o := by rfl

theorem collect_callback (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 (replace o sub double) =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 o := by rfl

theorem error_callback0 (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError (replace o sub double) =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError o := by rfl

theorem error_callback1 (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError (replace o sub double) =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError o := by rfl

theorem error_callback2 (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError (replace o sub double) =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError o := by rfl

/-- Generic one-body congruence. Its sole arithmetic premise is a contextual
three-call law, later discharged without a parent-success assumption. -/
theorem step (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32)
    (poly : ∀ (T : Type) (x : U32) (k : U32 → Result T),
      (do let p ← o.op9 x x; let d ← double p; let one ← o.op7; let z ← sub d one; k z) =
      (do let p ← o.op9 x x; let d ← o.op10 p; let one ← o.op7; let z ← o.op8 d one; k z))
    (start : Usize) (iter : core.slice.iter.Iter U32) (lines flat : alloc.vec.Vec U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body (replace o sub double) start iter lines flat =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body o start iter lines flat := by
  simp only [Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body,
    reverse,zero_callback,collect_callback,error_callback0,error_callback1,error_callback2]
  simp only [replace,bind_assoc_eq,bind_tc_ok]
  congr 1
  funext following
  rcases following with ⟨query,it1⟩
  cases query with
  | none => simp only [uncurry]; rfl
  | some q =>
   simp only [uncurry]
   repeat' first
   | exact poly _ _ _
   | (apply NEW_GeometryRawBody.bind_congr; intro)
   | simp only [uncurry,bind_assoc_eq,bind_tc_ok]
   | split
   all_goals trace_state

#print axioms replace
#print axioms reverse
#print axioms zero_callback
#print axioms collect_callback
#print axioms error_callback0
#print axioms error_callback1
#print axioms error_callback2
#print axioms step
end NEW_GeometryContextGeneric
