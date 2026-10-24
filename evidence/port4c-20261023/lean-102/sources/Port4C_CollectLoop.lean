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

def collect (ops : Ops CoreError) (flat : alloc.vec.Vec U32) (count : Usize) :
    Result (alloc.vec.Vec Group) :=
  core.iter.traits.iterator.Iterator.collect.default (iterator ops)
    (core.iter.traits.collect.FromIteratorVec Group) ⟨{start:=0#usize,«end»:=count},flat⟩

/-- Full standard map/collect result, in source query and five-lane order. -/
theorem total (ops : Ops CoreError) (flat : alloc.vec.Vec U32) (count : Usize)
    (bound : count.val≤22) (size : flat.val.length=5*count.val) :
    ∃ out, collect ops flat count=ok out ∧
      out.val=(List.range count.val).map (record flat) ∧ out.val.length=count.val := by
  have run := list_total ops flat count {start:=0#usize,«end»:=count} [] count.val bound size rfl (by simp)
  have run1 : alloc.vec.FromIteratorVec.iterToList (iterator ops)
      ⟨{start:=0#usize,«end»:=count},flat⟩ []=ok ((List.range count.val).map (record flat)) := by
    simpa only [show (0#usize).val=0 from rfl,List.reverse_nil,List.nil_append,List.range_eq_range'] using run
  have cap : ((List.range count.val).map (record flat)).length≤Usize.max := by
    rw [List.length_map,List.length_range]
    have limit : 22≤Usize.max := by scalar_tac
    omega
  let out : alloc.vec.Vec Group := ⟨(List.range count.val).map (record flat),cap⟩
  refine ⟨out,?_,rfl,by simp [out]⟩
  unfold collect core.iter.traits.iterator.Iterator.collect.default
    core.iter.traits.collect.FromIteratorVec alloc.vec.FromIteratorVec.from_iter
  simp only [core.iter.traits.collect.IntoIterator.Blanket,
    core.iter.traits.collect.IntoIterator.Blanket.into_iter,bind_tc_ok]
  change (do let xs ← alloc.vec.FromIteratorVec.iterToList (iterator ops)
               ⟨{start:=0#usize,«end»:=count},flat⟩ []
             if h : xs.length≤Usize.max then ok (⟨xs,h⟩ : alloc.vec.Vec Group) else fail .panic)=ok out
  rw [run1,bind_tc_ok,dif_pos cap]

#print axioms total
#print axioms list_total
end AspisR1.Port4C_CollectLoop
end
