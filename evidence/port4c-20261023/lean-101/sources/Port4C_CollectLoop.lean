import Port4C_CollectStd
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_CollectLoop
open Aeneas Aeneas.Std Result
open Port3_NativeGeometryBody
variable {CoreError : Type}
abbrev Group := Array U32 5#usize

def record (flat : alloc.vec.Vec U32) (i : Nat) : Group :=
  Array.make 5#usize [Port4C_GeometryGroups.word flat (5*i),Port4C_GeometryGroups.word flat (5*i+1),
    Port4C_GeometryGroups.word flat (5*i+2),Port4C_GeometryGroups.word flat (5*i+3),Port4C_GeometryGroups.word flat (5*i+4)]

def iterator (ops : Ops CoreError) :=
  Port4C_CollectStd.mapIterator (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
    (verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315
      (Port4C_CollectStd.install ops))

/-- Standard collect traversal, with every actual source grouping callback.
The list accumulator is reversed once, preserving query and lane order. -/
theorem list_total (ops : Ops CoreError) (flat : alloc.vec.Vec U32) (count : Usize)
    (iter : core.ops.range.Range Usize) (acc : List Group) (fuel : Nat)
    (bound : count.val≤22) (size : flat.val.length=5*count.val)
    (ending : iter.end=count) (span : iter.start.val+fuel=count.val) :
    alloc.vec.FromIteratorVec.iterToList (iterator ops) ⟨iter,flat⟩ acc=
      ok (acc.reverse++(List.range' iter.start.val fuel).map (record flat)) := by
  induction fuel generalizing iter acc with
  | zero =>
    obtain ⟨⟨o,iter1⟩,run,ho,_⟩ := WP.spec_imp_exists
      (core.iter.range.IteratorRange.next_UScalar_none_spec
        (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
        (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro a b; rfl)
        iter (by rw [ending]; omega))
    subst o
    rw [alloc.vec.FromIteratorVec.iterToList]
    simp only [iterator,Port4C_CollectStd.mapIterator,OraclePortStdBuilder.mapNext,run,bind_tc_ok,
      List.range'_zero,List.map_nil,List.append_nil]
  | succ fuel ih =>
    obtain ⟨⟨o,iter1⟩,run,ho,hs,he⟩ := WP.spec_imp_exists
      (core.iter.range.IteratorRange.next_UScalar_some_spec
        (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
        (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x; rfl) (by intro a b; rfl)
        iter (by rw [ending]; omega))
    subst o
    have next := Port4C_CollectStd.next_group ops flat count iter iter1 iter.start
      bound size (by omega) run
    have tail := ih iter1 (Port4C_GeometryGroups.record flat iter.start::acc)
      (he.trans ending) (by omega)
    rw [alloc.vec.FromIteratorVec.iterToList]
    have next1 : (iterator ops).next ⟨iter,flat⟩=
        ok (some (Port4C_GeometryGroups.record flat iter.start),⟨iter1,flat⟩) := next
    rw [next1,bind_tc_ok]
    change alloc.vec.FromIteratorVec.iterToList (iterator ops) ⟨iter1,flat⟩
      (Port4C_GeometryGroups.record flat iter.start::acc)=_
    rw [tail,List.range'_succ,List.map_cons,List.reverse_cons,hs,List.append_assoc,List.singleton_append]
    rfl

#print axioms list_total
end AspisR1.Port4C_CollectLoop
end
