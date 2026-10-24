import Port4C_FromFn
import Port4C_GeometryFields

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_GeometryGroups
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeGeometryBody
variable {CoreError : Type}

def install (ops : Ops CoreError) : Ops CoreError := {ops with op0 := OraclePortStdBuilder.fromFn}
def word (flat : alloc.vec.Vec U32) (i : Nat) : U32 := flat.val[i]?.getD 0#u32

def record (flat : alloc.vec.Vec U32) (i : Usize) : Array U32 5#usize :=
  Array.make 5#usize [word flat (5*i.val),word flat (5*i.val+1),word flat (5*i.val+2),
    word flat (5*i.val+3),word flat (5*i.val+4)]

theorem inner (ops : Ops CoreError) (flat : alloc.vec.Vec U32) (count i j : Usize)
    (bound : count.val≤22) (size : flat.val.length=5*count.val)
    (hi : i.val<count.val) (hj : j.val<5) :
    verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
      (install ops) (flat,i) j=ok (word flat (5*i.val+j.val),(flat,i)) := by
  let index := Usize.wrapping_add (Usize.wrapping_mul 5#usize i) j
  have mul : (Usize.wrapping_mul 5#usize i).val=5*i.val :=
    Port3_Wrapping.wrap_mul_value 5#usize i (by change 5*i.val≤4096; omega)
  have value : index.val=5*i.val+j.val := by
    change (Usize.wrapping_add (Usize.wrapping_mul 5#usize i) j).val=5*i.val+j.val
    rw [Port3_Wrapping.wrap_add_value _ j (by rw [mul]; omega),mul]
  obtain ⟨x,read,hx⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec flat index (by
    change index.val<flat.val.length
    rw [value,size]
    omega))
  have same : x=word flat (5*i.val+j.val) := by
    unfold word
    rw [←value,List.getElem?_eq_getElem (by rw [value,size]; omega),Option.getD_some]
    exact hx
  unfold verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
  change (do let x ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) flat index
             ok (x,(flat,i)))=ok _
  have read1 : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) flat index=ok x := read
  rw [read1,bind_tc_ok,same]

/-- CURRENT native from_fn callback returns all five inverse lanes in order.
No callback success or already grouped record is supplied as a premise. -/
theorem outer (ops : Ops CoreError) (flat : alloc.vec.Vec U32) (count i : Usize)
    (bound : count.val≤22) (size : flat.val.length=5*count.val) (hi : i.val<count.val) :
    verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut
      (install ops) flat i=ok (record flat i,flat) := by
  have callback : ∀ (c : alloc.vec.Vec U32 × Usize) (j : Usize), j.val<(5#usize).val →
      c=(flat,i) →
      verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
        (install ops) c j=ok (word flat (5*i.val+j.val),c) := by
    intro c j hj same
    subst c
    exact inner ops flat count i j bound size hi hj
  unfold verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut
  change (do
    let a ← OraclePortStdBuilder.fromFn 5#usize
      (verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31 (install ops))
      (flat,i)
    ok (a,flat))=ok (record flat i,flat)
  have pure : OraclePortStdBuilder.fromFn 5#usize
      (verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31 (install ops))
      (flat,i)=ok (record flat i) := by
    unfold OraclePortStdBuilder.fromFn
    have indices : OraclePortStdBuilder.indices 5#usize=[0#usize,1#usize,2#usize,3#usize,4#usize] := rfl
    rw [indices]
    simp only [OraclePortStdBuilder.fromFnLoop,
      verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31,
      inner ops flat count i 0#usize bound size hi (by decide),
      inner ops flat count i 1#usize bound size hi (by decide),
      inner ops flat count i 2#usize bound size hi (by decide),
      inner ops flat count i 3#usize bound size hi (by decide),
      inner ops flat count i 4#usize bound size hi (by decide),bind_tc_ok]
    rfl
  rw [pure,bind_tc_ok]

#print axioms inner
#print axioms outer
end AspisR1.Port4C_GeometryGroups
end
