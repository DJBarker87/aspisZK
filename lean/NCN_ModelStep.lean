import NCI_ResidueWords
import NCI_ArrayFrame
import NCI_GetterModel
import S8Kani2MutableSource
set_option autoImplicit false
namespace AspisR1.NCN_ModelStep
open Aeneas Aeneas.Std Result ControlFlow
open S8Kani2MutableExtraction

/-- Exact emitted product/add/write on the selected row. The Vec borrow and
iterator next are explicit lower ports; no desired whole-call output is assumed. -/
theorem product_write (row : Array U64 4#usize) (limbs : Array U32 4#usize)
    (j : Usize) (basis : U32) (terms : Nat)
    (hj : j.val < 4)
    (ha : (limbs.val[j.val]'(by simpa using hj)).val < NCI_ResidueBounds.P)
    (hb : basis.val < NCI_ResidueBounds.P)
    (hr : (row.val[j.val]'(by simpa using hj)).val <
      NCI_ResidueBounds.Boundary + (terms%4)*NCI_ResidueBounds.MaxProduct) :
    ∃ limb : U32, ∃ old product sum : U64, ∃ after : Array U64 4#usize,
      Array.index_usize limbs j = ok limb ∧
      Array.index_usize row j = ok old ∧
      (UScalar.cast .U64 limb * UScalar.cast .U64 basis) = ok product ∧
      old + product = ok sum ∧ Array.update row j sum = ok after ∧
      sum.val = old.val + limb.val*basis.val ∧
      after.val = row.val.set j.val sum := by
  have hl : j.val < limbs.val.length := by simpa using hj
  have rr : j.val < row.val.length := by simpa using hj
  let limb := limbs.val[j.val]'hl
  let old := row.val[j.val]'rr
  obtain ⟨product,sum,prod,_,add,total⟩ :=
    NCI_ResidueWords.product_sum limb basis old terms ha hb hr
  obtain ⟨after,write,contents⟩ := NCI_ArrayFrame.write row j sum rr
  exact ⟨limb,old,product,sum,after,NCI_GetterModel.array_get limbs j hl,
    NCI_GetterModel.array_get row j rr,prod,add,write,total,contents⟩

#print axioms product_write
end AspisR1.NCN_ModelStep
