import R1Z.BuilderTreeArguments

/-! Full path Parts content from actual source arguments. -/
set_option autoImplicit false
namespace R1Z.BuilderPathContent
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderPrimitiveArguments BuilderDigestArguments BuilderTreeArguments BuilderRecordsArray BuilderRecordsFields
open AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder
abbrev Matrix := Array (Array U32 8#usize) 24#usize
abbrev Pairs := Array ((Array U32 8#usize) × (Array U32 8#usize)) 24#usize

def pairs (w : RW) (p : RP) : Pairs := tabulate 24#usize fun j =>
  orderedR ((curArr (wordWitness w) (wordPublic p)).val[j]!) w.sibs.val[j]! (bitB (wordWitness w) j)

theorem current_array (w : RW) (p : RP) :
    AspisBuilderGlueSource.core.array.from_fn 24#usize
      path_arrays.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU328 (w,p) =
      ok (curArr (wordWitness w) (wordPublic p)) := by
  have hf : ∀ i : Usize, i.val < 24 →
      path_arrays.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU328.call_mut (w,p) i =
        ok (okOr (treeCurR (wordWitness w) (wordPublic p) i.val) zero8,(w,p)) := by
    intro i hi
    rw [path_arrays.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU328.call_mut,
      tree_ok w p i (by omega)]
    rfl
  rw [from_fn_nat 24#usize path_arrays.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU328
    (w,p) (fun j => okOr (treeCurR (wordWitness w) (wordPublic p) j) zero8) hf]
  rfl

theorem pair_array (w : RW) (p : RP) :
    AspisBuilderGlueSource.core.array.from_fn 24#usize
      path_arrays.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizePairArrayU328ArrayU328
      (curArr (wordWitness w) (wordPublic p),w) = ok (pairs w p) := by
  apply from_fn_nat
  intro i hi
  change path_arrays.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizePairArrayU328ArrayU328.call_mut
    (curArr (wordWitness w) (wordPublic p),w) i = _
  rw [path_arrays.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizePairArrayU328ArrayU328.call_mut,
    index_ok_gen _ i hi]
  simp only [bind_tc_ok]
  rw [index_ok_gen _ i hi]
  simp only [bind_tc_ok]
  rw [bit w i hi]
  simp only [bind_tc_ok,ordered]

theorem pairs_get (w : RW) (p : RP) (i : Nat) (hi : i < 24) :
    (pairs w p).val[i]! = levelPair (wordWitness w) (wordPublic p) ⟨i,hi⟩ := by
  rw [pairs,tabulate_get _ _ i (by simpa using hi)]
  unfold curArr
  rw [arr24_get _ i hi]
  rfl

theorem left_array (w : RW) (p : RP) :
    AspisBuilderGlueSource.core.array.from_fn 24#usize
      path_arrays.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU328 (pairs w p) =
      ok (leftArr (wordWitness w) (wordPublic p)) := by
  have hf : ∀ i : Usize, i.val < 24 →
      path_arrays.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU328.call_mut (pairs w p) i =
        ok (((pairs w p).val[i.val]!).1,pairs w p) := by
    intro i hi
    rw [path_arrays.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU328.call_mut,
      index_ok_gen _ i (by simpa using hi)]
    rfl
  rw [from_fn_nat 24#usize path_arrays.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU328
    (pairs w p) (fun j => ((pairs w p).val[j]!).1) hf]
  congr 1


theorem right_array (w : RW) (p : RP) :
    AspisBuilderGlueSource.core.array.from_fn 24#usize
      path_arrays.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU328 (pairs w p) =
      ok (rightArr (wordWitness w) (wordPublic p)) := by
  have hf : ∀ i : Usize, i.val < 24 →
      path_arrays.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU328.call_mut (pairs w p) i =
        ok (((pairs w p).val[i.val]!).2,pairs w p) := by
    intro i hi
    rw [path_arrays.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU328.call_mut,
      index_ok_gen _ i (by simpa using hi)]
    rfl
  rw [from_fn_nat 24#usize path_arrays.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU328
    (pairs w p) (fun j => ((pairs w p).val[j]!).2) hf]
  congr 1


theorem arrays (w : RW) (p : RP) : path_arrays w p =
    ok (curArr (wordWitness w) (wordPublic p),leftArr (wordWitness w) (wordPublic p),
      rightArr (wordWitness w) (wordPublic p)) := by
  rw [path_arrays,current_array]
  simp only [bind_tc_ok]
  rw [pair_array]
  simp only [bind_tc_ok]
  rw [left_array]
  simp only [bind_tc_ok]
  rw [right_array]
  rfl

theorem parts_path (w : RW) (p : RP) (pt : Parts) (h : parts w p = ok pt) :
    pathR (wordWitness w) (wordPublic p) = ok pt.path := by
  unfold parts at h
  obtain ⟨m,_,h⟩ := bind_ok_inv h
  obtain ⟨blocks,_,h⟩ := bind_ok_inv h
  rw [arrays] at h
  simp only [bind_tc_ok] at h
  obtain ⟨path,hpath,h⟩ := bind_ok_inv h
  obtain ⟨i,_,h⟩ := bind_ok_inv h
  obtain ⟨o,_,h⟩ := bind_ok_inv h
  obtain ⟨aux,_,h⟩ := bind_ok_inv h
  have he := congrArg Parts.path (Result.ok.inj h)
  have hm : pathR (wordWitness w) (wordPublic p) = ok path := by
    unfold pathR
    rw [← BuilderPrimitiveWriters.write_path_block]
    exact hpath
  rw [hm]
  exact congrArg Result.ok he

theorem parts_path_content (w : RW) (p : RP) (pt : Parts) (h : parts w p = ok pt) :
    pt.path = okOr (pathR (wordWitness w) (wordPublic p)) (Array.repeat 1536#usize 0#u32) := by
  rw [parts_path w p pt h,okOr_ok]

#print axioms current_array
#print axioms pair_array
#print axioms pairs_get
#print axioms left_array
#print axioms right_array
#print axioms arrays
#print axioms parts_path
#print axioms parts_path_content
end R1Z.BuilderPathContent
