import NFB_RootGather
set_option autoImplicit false
noncomputable section
namespace NFB_TerminalCuts
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NEW_GeometryDictionary NFB_GatherTrace
open Port3_PushFrame (bind_success)

/-- Every terminal success obtains its intermediate buffers from THIS run.
No prefix, inverse or collected output is supplied independently. -/
theorem complete (start : Usize) (it : It) (lines flat : Vec)
 (out : AspisR1Stage2.verifier.QueryGeometry)
 (ending : it.i=it.slice.val.length) (notempty : flat.val≠[])
 (accepted : Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body
 adopted start it lines flat=ok (done (.Ok out))) :
 ∃ (prefixes : Vec) (product suffix zero : U32) (resized inverse : Vec)
   (rev : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
   (mapped : core.iter.adapters.map.Map (core.ops.range.Range Usize) Vec)
   (groups : alloc.vec.Vec (Array U32 5#usize)),
 adopted.op13 flat.deref=ok (prefixes,product) ∧
 adopted.op11 product=ok suffix ∧ adopted.op6=ok zero ∧
 alloc.vec.Vec.resize core.marker.CopyU32.cloneInst
  (alloc.vec.Vec.with_capacity U32 (alloc.vec.Vec.len flat)) (alloc.vec.Vec.len flat) zero=ok resized ∧
 core.iter.traits.iterator.Iterator.rev.trait_default
  (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
  (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)
  {start:=0#usize,«end»:=alloc.vec.Vec.len flat}=ok rev ∧
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0 adopted
  rev flat prefixes suffix resized=ok inverse ∧
 adopted.op1
  (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
  (Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 adopted)
  {start:=0#usize,«end»:=alloc.vec.Vec.len lines} inverse=ok mapped ∧
 core.iter.traits.iterator.Iterator.collect.default
  (adopted.mapIterator (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
   (Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 adopted))
  (core.iter.traits.collect.FromIteratorVec (Array U32 5#usize)) mapped=ok groups ∧
 out.start=start ∧ out.line_z=lines ∧ out.inverses=groups := by
 have next := NFB_QueryIterator.end_next it (by omega)
 unfold Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body at accepted
 rw [next,bind_tc_ok] at accepted
 have empty : adopted.op4 Global flat=ok false := by
  change ok flat.val.isEmpty=ok false
  simp only [List.isEmpty_eq_false_iff.mpr notempty]
 rw [empty,bind_tc_ok] at accepted
 simp only [Bool.false_eq_true,if_false] at accepted
 obtain ⟨⟨prefixes,product⟩,hp,accepted⟩ := bind_success _ _ _ accepted
 obtain ⟨suffix,hs,accepted⟩ := bind_success _ _ _ accepted
 obtain ⟨zero,hz,accepted⟩ := bind_success _ _ _ accepted
 obtain ⟨resized,hr,accepted⟩ := bind_success _ _ _ accepted
 obtain ⟨rev,hv,accepted⟩ := bind_success _ _ _ accepted
 obtain ⟨inverse,hi,accepted⟩ := bind_success _ _ _ accepted
 obtain ⟨mapped,hm,accepted⟩ := bind_success _ _ _ accepted
 obtain ⟨groups,hg,accepted⟩ := bind_success _ _ _ accepted
 cases Result.ok.inj accepted
 exact ⟨prefixes,product,suffix,zero,resized,inverse,rev,mapped,groups,hp,hs,hz,hr,hv,hi,hm,hg,rfl,rfl,rfl⟩
#print axioms complete
end NFB_TerminalCuts
end
