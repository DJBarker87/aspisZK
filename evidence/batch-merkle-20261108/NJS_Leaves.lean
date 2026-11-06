import NJS_Extract.Funs
import Port3_BatchStd
import NBH_ArrayEq
set_option autoImplicit false
noncomputable section
namespace NJS_Leaves
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

theorem key (keys : Array U64 16#usize) (i : Usize) :
    NJS_Extract.verifier.candidate.batch_key_at keys i = Array.index_usize keys i := by rfl

theorem index (values : Array U32 16#usize) (i : Usize) (expected : U32) :
    NJS_Extract.verifier.candidate.same_batch_index values i expected =
      AspisR1.Port3_BatchStd.sameIndex values i expected := by rfl

theorem leaf (values : Array (Array U8 32#usize) 16#usize) (i : Usize)
    (expected : Array U8 32#usize) :
    NJS_Extract.verifier.candidate.same_batch_leaf values i expected =
      AspisR1.Port3_BatchStd.sameLeaf values i expected := by
  simp only [NJS_Extract.verifier.candidate.same_batch_leaf,
    AspisR1.Port3_BatchStd.sameLeaf, NBH_ArrayEq.source]

#check key
#check index
#check leaf
#print axioms key
#print axioms index
#print axioms leaf
end NJS_Leaves
