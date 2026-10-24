import Port4C_GeometryGroups
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_CollectStd
open Aeneas Aeneas.Std Result
variable {CoreError : Type}

def mapIterator {B I F Item : Type}
    (it : core.iter.traits.iterator.Iterator I Item) (f : core.ops.function.FnMut F Item B) :
    core.iter.traits.iterator.Iterator (core.iter.adapters.map.Map I F) B :=
  {next := OraclePortStdBuilder.mapNext it f}

def install (ops : Port3_NativeGeometryBody.Ops CoreError) : Port3_NativeGeometryBody.Ops CoreError :=
  {Port4C_GeometryGroups.install ops with
    op1 := OraclePortStdBuilder.iterMap
    mapIterator := mapIterator}

theorem next_group (ops : Port3_NativeGeometryBody.Ops CoreError)
    (flat : alloc.vec.Vec U32) (count : Usize)
    (iter iter1 : core.ops.range.Range Usize) (i : Usize)
    (bound : count.val≤22) (size : flat.val.length=5*count.val) (hi : i.val<count.val)
    (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some i,iter1)) :
    (mapIterator (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315
        (install ops))).next ⟨iter,flat⟩=
      ok (some (Port4C_GeometryGroups.record flat i),⟨iter1,flat⟩) := by
  have group := Port4C_GeometryGroups.outer (install ops) flat count i bound size hi
  change OraclePortStdBuilder.mapNext _ _ ⟨iter,flat⟩=_
  unfold OraclePortStdBuilder.mapNext
  change (do
    let (x,i1) ← (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize).next iter
    match x with
    | none => ok (none,(⟨i1,flat⟩ : core.iter.adapters.map.Map (core.ops.range.Range Usize) (alloc.vec.Vec U32)))
    | some j => do
      let (group,c) ←
        Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut
          (install ops) flat j
      ok (some group,⟨i1,c⟩))=_
  have next1 : (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize).next iter=ok (some i,iter1) := next
  rw [next1,bind_tc_ok]
  change (do
    let pair ← Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut
      (install ops) flat i
    ok (some pair.1,(⟨iter1,pair.2⟩ : core.iter.adapters.map.Map (core.ops.range.Range Usize) (alloc.vec.Vec U32))))=_
  rw [group,bind_tc_ok]

#print axioms next_group
#print Aeneas.Std.alloc.vec.FromIteratorVec.iterToList
end AspisR1.Port4C_CollectStd
end
