import NNV_GeometryBranches
import NNV_GeometryIndexPorts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_GeometryQueryForm
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 Port3_NativeGeometryBody
open NNV_GeometryBranches

def fibre {C : Type} (ops : Ops C) (u : Usize) := do
 let r ← ops.op12 u
 ops.op2 (verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError ops) r ()
def normalized {C : Type} (ops : Ops C) (iter1 : core.slice.iter.Iter U32) (query : U32)
 (line_z_values flat : alloc.vec.Vec U32) : Result Out := do
 let u ← lift (UScalar.cast .Usize query)
 let r1 ← fibre ops u
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
 match cf with
 | core.ops.control_flow.ControlFlow.Continue val =>
   let p ← ops.op15 val
   let i ← u / 4#usize
   let i1 ← lift (Std.Usize.wrapping_mul i 4#usize)
   let r3 ← fibre ops i1
   let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r3
   match cf1 with
   | core.ops.control_flow.ControlFlow.Continue val1 =>
     let line_x ← ops.op14 val1
     let i2 ← lift (Std.Usize.wrapping_mul i 4#usize)
     let i3 ← lift (Std.Usize.wrapping_add i2 3#usize)
     let r5 ← fibre ops i3
     let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r5
     match cf2 with
     | core.ops.control_flow.ControlFlow.Continue val2 =>
       let line_y ← ops.op14 val2
       let m ← ops.op9 line_x line_x
       let m1 ← ops.op10 m
       let m2 ← ops.op7
       let line_z ← ops.op8 m1 m2
       let s ←
         lift (Array.to_slice
           (Array.make 5#usize [ p.x, p.y, line_x, line_y, line_z ]))
       let i4 ← core.slice.Slice.iter s
       let (b, _) ←
         ops.op3
           (verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool ops)
           i4 ()
       if b
       then ok (done (core.result.Result.Err verifier.Error.Query))
       else
         let s1 ←
           lift (Array.to_slice
             (Array.make 5#usize [ p.x, p.y, line_x, line_y, line_z ]))
         let flat1 ←
           alloc.vec.Vec.extend_from_slice
             core.marker.CopyU32.cloneInst flat s1
         let line_z_values1 ← alloc.vec.Vec.push line_z_values line_z
         ok (cont (iter1, line_z_values1, flat1))
     | core.ops.control_flow.ControlFlow.Break residual =>
       let r6 ←
         core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
           verifier.QueryGeometry (core.convert.FromSame verifier.Error)
           residual
       ok (done r6)
   | core.ops.control_flow.ControlFlow.Break residual =>
     let r4 ←
       core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
         verifier.QueryGeometry (core.convert.FromSame verifier.Error)
         residual
     ok (done r4)
 | core.ops.control_flow.ControlFlow.Break residual =>
   let r2 ←
     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
       verifier.QueryGeometry (core.convert.FromSame verifier.Error)
       residual
   ok (done r2)

theorem source {C : Type} (ops : Ops C) (it : core.slice.iter.Iter U32) (q : U32)
 (zs flat : alloc.vec.Vec U32) :
 NNV_GeometryBranches.query ops it q zs flat = normalized ops it q zs flat := by
 simp only [NNV_GeometryBranches.query,normalized,fibre,bind_assoc_eq]
 all_goals rfl
#print axioms source
end AspisR1.NNV_GeometryQueryForm
end
