import NNH_Run5bGeometryReverse
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_GeometryBranches
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 Port3_NativeGeometryBody
abbrev Out := ControlFlow ((core.slice.iter.Iter U32) × (alloc.vec.Vec U32) × (alloc.vec.Vec U32))
 (core.result.Result verifier.QueryGeometry verifier.Error)
def terminal {C : Type} (ops : Ops C) (start : Usize)
 (line_z_values flat : alloc.vec.Vec U32) : Result Out := do
 let b ← ops.op4 Global flat
 if b
 then
   ok (done (core.result.Result.Ok
     {
       start,
       inverses := (alloc.vec.Vec.new (Array aspis_core.field.M31 5#usize)),
       line_z := line_z_values
     }))
 else
   let s := alloc.vec.Vec.deref flat
   let (prefixes, product) ← ops.op13 s
   let suffix_inverse ← ops.op11 product
   let i := alloc.vec.Vec.len flat
   let flat_inverse := alloc.vec.Vec.with_capacity aspis_core.field.M31 i
   let i1 := alloc.vec.Vec.len flat
   let m ← ops.op6
   let flat_inverse1 ←
     alloc.vec.Vec.resize core.marker.CopyU32.cloneInst
       flat_inverse i1 m
   let i2 := alloc.vec.Vec.len flat
   let iter2 ←
     core.iter.traits.iterator.Iterator.rev.trait_default
       (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
       (core.ops.range.Range.Insts.DoubleEndedIterator
       core.iter.range.StepUsize) { start := 0#usize, «end» := i2 }
   let flat_inverse2 ←
     (verifier.QueryGeometry.for_range_loop0_loop0 ops) iter2 flat prefixes
       suffix_inverse flat_inverse1
   let i3 := alloc.vec.Vec.len line_z_values
   let m1 ←
     ops.op1
       (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
       (verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 ops)
       { start := 0#usize, «end» := i3 } flat_inverse2
   let inverses ←
     core.iter.traits.iterator.Iterator.collect.default
       (ops.mapIterator
       (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
       (verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 ops))
       (core.iter.traits.collect.FromIteratorVec (Array aspis_core.field.M31
       5#usize)) m1
   ok (done (core.result.Result.Ok
     { start, inverses, line_z := line_z_values }))

def query {C : Type} (ops : Ops C) (iter1 : core.slice.iter.Iter U32) (query : U32)
 (line_z_values flat : alloc.vec.Vec U32) : Result Out := do
 let u ← lift (UScalar.cast .Usize query)
 let r ← ops.op12 u
 let r1 ←
   ops.op2
     (verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError ops)
     r ()
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
 match cf with
 | core.ops.control_flow.ControlFlow.Continue val =>
   let p ← ops.op15 val
   let i ← u / 4#usize
   let i1 ← lift (Std.Usize.wrapping_mul i 4#usize)
   let r2 ← ops.op12 i1
   let r3 ←
     ops.op2
       (verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError ops)
       r2 ()
   let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r3
   match cf1 with
   | core.ops.control_flow.ControlFlow.Continue val1 =>
     let line_x ← ops.op14 val1
     let i2 ← lift (Std.Usize.wrapping_mul i 4#usize)
     let i3 ← lift (Std.Usize.wrapping_add i2 3#usize)
     let r4 ← ops.op12 i3
     let r5 ←
       ops.op2
         (verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError ops)
         r4 ()
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

theorem body {C : Type} (ops : Ops C) (start : Usize) (iter : core.slice.iter.Iter U32)
 (zs flat : alloc.vec.Vec U32) :
 verifier.QueryGeometry.for_range_loop0.body ops start iter zs flat =
 (do let (o,it) ← core.slice.iter.IteratorSliceIter.next iter
     match o with | none => terminal ops start zs flat | some q => query ops it q zs flat) := rfl
#print axioms body
end AspisR1.NNV_GeometryBranches
end
