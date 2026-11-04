import NFE_NEV_DotEight
import NEG_ProductAbstraction
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFF_Cell
open Aeneas Aeneas.Std Result

/-- Local-record reply continuation: the pre-state is not chosen from a model result. -/
def opaque (sums : Array U64 8#usize) (index : Usize) (product : U64) :
    Result (Array U64 8#usize) := do
  let before ← Array.index_usize sums index
  let after ← before+product
  Array.update sums index after

/-- A reply associated with the SAME reached operands gives the exact checked
cell, including its failure behavior. No successful output is assumed. -/
theorem replay (coefficient : Array U32 8#usize) (scalar word : U32)
    (sums : Array U64 8#usize) (index : Usize) (product : U64)
    (read : Array.index_usize coefficient index=ok word)
    (hw : word.val<NEG_DotDomain.P) (hs : scalar.val<NEG_DotDomain.P)
    (law : NEG_ProductAbstraction.Product 64 word.val scalar.val product.val) :
    NFE_NEV_DotCell.cell coefficient scalar sums index=opaque sums index product := by
  obtain ⟨actual,multiply,value,bound,nativeLaw⟩ := NFE_NEV_DotScalar.product word scalar hw hs
  have same : actual=product := UScalar.eq_of_val_eq (nativeLaw.trans law.symm)
  simp only [NFE_NEV_DotCell.cell,read,multiply,same,bind_tc_ok,opaque]

/-- The deterministic primitive reply is admissible; native source association
still has to identify the reached operands, as checked by the NFF local log. -/
theorem primitive_reply (word scalar : U32)
    (hw : word.val<NEG_DotDomain.P) (hs : scalar.val<NEG_DotDomain.P) :
    ∃ product : U64,
      (core.convert.num.FromU64U32.from word)*(core.convert.num.FromU64U32.from scalar)=ok product ∧
      NEG_ProductAbstraction.Product 64 word.val scalar.val product.val ∧
      product.val≤NEG_DotDomain.B := by
  obtain ⟨p,m,v,b,l⟩ := NFE_NEV_DotScalar.product word scalar hw hs
  exact ⟨p,m,l,b⟩

#print axioms replay
#print axioms primitive_reply
end AspisR1.NFF_Cell
end
