import NEV_DotScalar
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NEV_DotCell
open Aeneas Aeneas.Std Result
/-- Literal widened multiply/checked-add/read/write cell of the actual suffix. -/
def cell (coefficient : Array U32 8#usize) (scalar : U32)
    (sums : Array U64 8#usize) (index : Usize) : Result (Array U64 8#usize) := do
 let word ← Array.index_usize coefficient index
 let product ← (core.convert.num.FromU64U32.from word)*(core.convert.num.FromU64U32.from scalar)
 let before ← Array.index_usize sums index
 let after ← before+product
 Array.update sums index after
/-- All arithmetic is discharged by the retained bound and new SAME-input
product specialization. Native K058/K059 checks the instruction/frame cut. -/
theorem total (coefficient : Array U32 8#usize) (scalar word : U32)
    (sums : Array U64 8#usize) (index : Usize) (before : U64) (n : Nat)
    (inside : index.val<8) (readWord : Array.index_usize coefficient index=ok word)
    (readSum : Array.index_usize sums index=ok before)
    (hw : word.val<NEG_DotDomain.P) (hs : scalar.val<NEG_DotDomain.P)
    (active : n<4) (bound : before.val≤n*NEG_DotDomain.B) :
    ∃ after,cell coefficient scalar sums index=ok (sums.set index after) ∧
      after.val=before.val+word.val*scalar.val ∧
      after.val≤(n+1)*NEG_DotDomain.B := by
  obtain ⟨product,multiply,value,productBound,_⟩:=NEV_DotScalar.product word scalar hw hs
  have safe:=NEG_DotDomain.term_safe n before.val product.val active bound productBound
  obtain ⟨after,add,afterValue⟩:=WP.spec_imp_exists
    (UScalar.add_spec (x:=before) (y:=product)
      (by norm_num [UScalar.max,UScalar.size,U64.max,U64.size,U64.numBits];norm_num at safe;omega))
  obtain ⟨updated,write,shape⟩:=WP.spec_imp_exists
    (Array.update_spec sums index after (by change index.val<sums.val.length;rw [sums.property];exact inside))
  have actualWrite : Array.update sums index after=ok (sums.set index after) := shape ▸ write
  refine ⟨after,?_,?_,?_⟩
  · simp only [cell,readWord,readSum,multiply,add,actualWrite,bind_tc_ok]
  · rw [afterValue,value]
  · rw [afterValue];exact NEG_DotDomain.term_invariant n before.val product.val bound productBound
#print axioms total
end NEV_DotCell
end
