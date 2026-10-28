import R1Z.BuilderColumnsExtracted
import R1Z.BuilderSliceCollect
import R1Z.BuilderStdArray
import R1Z.BuilderPartsContent

/-! Actual Vec column wrapper, with ordered slice collection and no table
or success premise. No bank cell is enumerated. -/
set_option autoImplicit false
namespace R1Z.BuilderColumns
open Aeneas Aeneas.Std Result R0Z.WriterRefine BuilderStdModels
open AspisBuilderColumnsSource.pool_v1.pair_forest_copy_builder
open BuilderRecordsArray

def column (flat : Array U32 16384#usize) (c : Nat) : alloc.vec.Vec U32 :=
  ⟨flat.val.slice (c*1024) ((c+1)*1024),by
    apply (List.slice_length_le _ _ _).trans
    rw [flat.property]
    scalar_tac⟩

theorem column_step (flat : Array U32 16384#usize) (c : Usize) (hc : c.val < 16) :
    columns.closure.Insts.CoreOpsFunctionFnMutTupleUsizeVecM31.call_mut flat c =
      ok (column flat c.val,flat) := by
  let start := Usize.wrapping_mul c 1024#usize
  let finish := Usize.wrapping_mul (Usize.wrapping_add c 1#usize) 1024#usize
  have vs : start.val = c.val*1024 := by
    dsimp [start]
    rw [umul _ _ (by simp; omega)]
    rfl
  have va : (Usize.wrapping_add c 1#usize).val = c.val+1 := by
    rw [uadd _ _ (by simp; omega)]
    rfl
  have ve : finish.val = (c.val+1)*1024 := by
    dsimp [finish]
    rw [umul _ _ (by rw [va]; simp; omega),va]
    rfl
  have hb : start ≤ finish ∧ finish.val ≤ flat.to_slice.length := by
    change start.val ≤ finish.val ∧ finish.val ≤ flat.val.length
    rw [vs,ve,flat.property]
    simp only [UScalar.ofNatCore_val_eq]
    omega
  have hs : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U32))
      flat ⟨start,finish⟩ = ok (column flat c.val) := by
    change core.slice.index.SliceIndexRangeUsizeSlice.index
      ⟨start,finish⟩ flat.to_slice = _
    rw [core.slice.index.SliceIndexRangeUsizeSlice.index]
    dsimp only
    rw [if_pos hb]
    congr 1
    apply Subtype.ext
    change flat.val.slice start.val finish.val = flat.val.slice (c.val*1024) ((c.val+1)*1024)
    rw [vs,ve]
  have ht := BuilderSliceCollect.collect_identity
    columns.closure.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32M31
    (by intros; rfl) (column flat c.val) 0 ()
  have ht' : core.iter.traits.iterator.Iterator.collect.default
      (AspisBuilderColumnsSource.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
        (core.iter.traits.iterator.IteratorSliceIter U32)
        columns.closure.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32M31)
      (core.iter.traits.collect.FromIteratorVec U32) ⟨⟨column flat c.val,0⟩,()⟩ =
      ok (column flat c.val) := by
    change core.iter.traits.iterator.Iterator.collect.default
      (mappedIterator (core.iter.traits.iterator.IteratorSliceIter U32)
        columns.closure.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32M31)
      (core.iter.traits.collect.FromIteratorVec U32) ⟨⟨column flat c.val,0⟩,()⟩ = _
    simpa [BuilderSliceCollect.suffix] using ht
  rw [columns.closure.Insts.CoreOpsFunctionFnMutTupleUsizeVecM31.call_mut]
  simp only [lift,bind_tc_ok]
  rw [hs]
  simp only [bind_tc_ok,core.slice.Slice.iter,
    AspisBuilderColumnsSource.core.iter.traits.iterator.Iterator.map.default,iterMap]
  change (do
    let v ← core.iter.traits.iterator.Iterator.collect.default
      (AspisBuilderColumnsSource.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
        (core.iter.traits.iterator.IteratorSliceIter U32)
        columns.closure.closure.Insts.CoreOpsFunctionFnMutTupleSharedU32M31)
      (core.iter.traits.collect.FromIteratorVec U32) ⟨⟨column flat c.val,0⟩,()⟩
    ok (v,flat)) = _
  rw [ht']
  rfl

theorem columns_eq (flat : Array U32 16384#usize) :
    columns flat = ok (tabulate 16#usize (column flat)) := by
  rw [columns]
  change fromFn 16#usize columns.closure.Insts.CoreOpsFunctionFnMutTupleUsizeVecM31 flat = _
  have h := fromFn_bounded 16#usize
    columns.closure.Insts.CoreOpsFunctionFnMutTupleUsizeVecM31
    (fun c => column flat c.val) flat
    (fun c hc => column_step flat c (by simpa using hc))
  rw [h]
  congr 1

theorem column_length (flat : Array U32 16384#usize) (c : Nat) (hc : c < 16) :
    (column flat c).val.length = 1024 := by
  rw [column,List.slice_length,flat.property]
  simp only [UScalar.ofNatCore_val_eq]
  omega

theorem column_at (flat : Array U32 16384#usize) (c r : Nat)
    (hc : c < 16) (hr : r < 1024) :
    (column flat c).val[r]! = flat.val[c*1024+r]! := by
  change (flat.val.slice (c*1024) ((c+1)*1024))[r]! = _
  apply List.getElem!_slice
  constructor
  · rw [flat.property]
    simp only [UScalar.ofNatCore_val_eq]
    omega
  · omega

/-- Read a shipped Vec column, extending the sixteen columns by zero. -/
def read (out : Array (alloc.vec.Vec U32) 16#usize) (c : Fin 29) (r : Fin 1024) : U32 :=
  if c.val < 16 then (out.val[c.val]!).val[r.val]! else 0#u32

theorem read_table (flat : Array U32 16384#usize) (c : Fin 29) (r : Fin 1024) :
    read (tabulate 16#usize (column flat)) c r = BuilderPartsContent.columnCell flat c r := by
  unfold read BuilderPartsContent.columnCell
  by_cases h : c.val < 16
  · rw [if_pos h,if_pos h,tabulate_get _ _ _ (by simpa using h)]
    exact column_at flat c.val r.val h r.isLt
  · rw [if_neg h,if_neg h]

/-- Actual Parts-to-banks-to-Vec composition, conditional only on the
primitive canonical component correspondence that remains to be supplied. -/
theorem source_banks_columns
    (rw : AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.RW)
    (rp : AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.RP)
    (pt : AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.Parts)
    (hp : AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.parts rw rp = ok pt)
    (w : RustWitness) (p : RustPublic) (hc : BuilderPartsContent.Content pt w p) :
    ∃ merged out,
      AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.merged_banks rw rp =
        ok (true,BuilderBankMaterialization.stableModel pt,
          BuilderBankMaterialization.lateModel pt,merged) ∧
      columns merged = ok out ∧
      (∀ c, c < 16 → (out.val[c]!).val.length = 1024) ∧
      ∀ c r, read out c r = copyCellMerged w p c r := by
  obtain ⟨merged,hm,hcells⟩ := BuilderPartsContent.banks_columns rw rp pt hp w p hc
  refine ⟨merged,tabulate 16#usize (column merged),hm,columns_eq merged,?_,?_⟩
  · intro c h
    rw [tabulate_get _ _ _ (by simpa using h)]
    exact column_length merged c h
  · intro c r
    rw [read_table]
    exact hcells c r

#print axioms column_step
#print axioms columns_eq
#print axioms column_length
#print axioms column_at
#print axioms read_table
#print axioms source_banks_columns
end R1Z.BuilderColumns
