import NNU_GeometryInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_GeometryEnd
open Aeneas Aeneas.Std Result Port3_NativeGeometryBody

def ending {C : Type} (g : Ops C) (start : Usize) (zs flat : alloc.vec.Vec U32) :
 Result (ControlFlow (core.slice.iter.Iter U32 × alloc.vec.Vec U32 × alloc.vec.Vec U32)
   (core.result.Result AspisR1Stage2.verifier.QueryGeometry AspisR1Stage2.verifier.Error)) := do
 let b ← g.op4 Global flat
 if b
 then
   ok (done (core.result.Result.Ok
     {
       start,
       inverses := (alloc.vec.Vec.new (Array aspis_core.field.M31 5#usize)),
       line_z := zs
     }))
 else
   let s := alloc.vec.Vec.deref flat
   let (prefixes, product) ← g.op13 s
   let suffix_inverse ← g.op11 product
   let i := alloc.vec.Vec.len flat
   let flat_inverse := alloc.vec.Vec.with_capacity aspis_core.field.M31 i
   let i1 := alloc.vec.Vec.len flat
   let m ← g.op6
   let flat_inverse1 ←
     alloc.vec.Vec.resize core.marker.CopyU32.cloneInst
       flat_inverse i1 m
   let i2 := alloc.vec.Vec.len flat
   let iter2 ←
     core.iter.traits.iterator.Iterator.rev.trait_default
       (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
       (core.g.range.Range.Insts.DoubleEndedIterator
       core.iter.range.StepUsize) { start := 0#usize, «end» := i2 }
   let flat_inverse2 ←
     (verifier.QueryGeometry.for_range_loop0_loop0 g) iter2 flat prefixes
       suffix_inverse flat_inverse1
   let i3 := alloc.vec.Vec.len zs
   let m1 ←
     g.op1
       (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
       (verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 g)
       { start := 0#usize, «end» := i3 } flat_inverse2
   let inverses ←
     core.iter.traits.iterator.Iterator.collect.default
       (g.mapIterator
       (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
       (verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 g))
       (core.iter.traits.collect.FromIteratorVec (Array aspis_core.field.M31
       5#usize)) m1
   ok (done (core.result.Result.Ok
     { start, inverses, line_z := zs }))

theorem same {C C' : Type} (g : Ops C) (h : Ops C')
 (map1 : @g.op1 = @h.op1) (empty4 : @g.op4 = @h.op4)
 (zero6 : g.op6=h.op6) (mul9 : g.op9=h.op9)
 (inv11 : g.op11=h.op11) (pref13 : g.op13=h.op13)
 (maps : @g.mapIterator = @h.mapIterator)
 (gather : verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 g =
   verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 h)
 (start : Usize) (zs flat : alloc.vec.Vec U32) : ending g start zs flat = ending h start zs flat := by
 unfold ending
 simp only [map1,empty4,zero6,inv11,pref13,maps,gather,
   NNH_Run5bGeometryReverse.loop g h (fun x y=>congrFun (congrFun mul9 x) y)]
#print axioms ending
#print axioms same
end AspisR1.NNU_GeometryEnd
end
