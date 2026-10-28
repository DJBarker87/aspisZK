import NDD_Reference.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_LeafRefs
/-- Value specifications only; the inventory supplies no adopted cohort helper
for these leaves, so these theorems do not close their enclosing source row. -/
theorem arity_bits (eight : Bool) :
    NDD_Reference.bits_ref eight = ok (if eight then 3#u32 else 1#u32) := by
  cases eight <;> rfl

theorem index (values : Array U32 16#usize) (i : Usize) :
    NDD_Reference.index_ref values i = Array.index_usize values i := rfl

theorem value (values : Array (Array U8 32#usize) 16#usize) (i : Usize) :
    NDD_Reference.value_ref values i = Array.index_usize values i := rfl

theorem root (values : Array (Array U8 32#usize) 16#usize) (expected : Array U8 32#usize) :
    NDD_Reference.root_ref values expected = (do
      let first ← Array.index_usize values 0#usize
      core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 first expected) := rfl

#print axioms arity_bits
#print axioms index
#print axioms value
#print axioms root
end NDD_LeafRefs
