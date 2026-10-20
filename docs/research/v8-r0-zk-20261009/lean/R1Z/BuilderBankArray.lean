import R1Z.BuilderBankExtracted
import R1Z.BuilderStdArray
import R0Z.BuilderWitness
import R0Z.WriterRefineOcc

/-! The actual extracted from_fn call refines the existing canonical
first-eight-lane adapter. No closure or array external remains assumed. -/
set_option autoImplicit false
namespace R1Z.BuilderBankArray
open Aeneas Aeneas.Std Result R0Z.WriterRefine

theorem digest8 (s : Array Std.U32 16#usize) :
    AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.digest8 s =
      ok (R0Z.WriterRefine.digest8 s) := by
  rw [AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.digest8]
  let f := AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.digest8.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
  change BuilderStdModels.fromFn 8#usize f s = _
  have hf : ∀ i : Std.Usize, i.val < (8#usize : Std.Usize).val →
      f.call_mut s i = ok (s.val[i.val]!, s) := by
    intro i hi
    change (do let x ← Array.index_usize s i; ok (x, s)) = _
    have hb : (8#usize : Std.Usize).val < (16#usize : Std.Usize).val := by decide
    rw [index_ok s i (lt_trans hi hb)]
    rfl
  rw [BuilderStdModels.fromFn_bounded 8#usize f (fun i => s.val[i.val]!) s hf]
  congr 1

#print axioms digest8
end R1Z.BuilderBankArray
