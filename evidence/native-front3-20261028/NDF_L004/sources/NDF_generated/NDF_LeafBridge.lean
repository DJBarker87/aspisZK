import NDF_ScalarBridge
import NBH_ArrayEq
set_option autoImplicit false
namespace NDF_LeafBridge
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

theorem same_leaf (values : Array (Array U8 32#usize) 16#usize) (i : Usize)
    (leaf : Array U8 32#usize) :
    NDF_Reference.same_batch_leaf_ref values i leaf = AspisR1.Port3_BatchStd.sameLeaf values i leaf := by
  unfold NDF_Reference.same_batch_leaf_ref AspisR1.Port3_BatchStd.sameLeaf
  congr 1
  funext value
  exact NBH_ArrayEq.source value leaf

#print axioms same_leaf
end NDF_LeafBridge
