import RPv_PoseidonPreparedChannelGeneratedStep
import NFT_Dot
set_option autoImplicit false
namespace NFT_ChannelFour
open Aeneas Aeneas.Std Result

/-- The fourth product fits too: this extends the old three-product model's
2*(P-1)^2 pre-cell limit to the 3*(P-1)^2 needed by sum_products4. -/
theorem generated_step (a b : U32) (acc : U64)
    (ha : a.val<2147483647) (hb : b.val<2147483647)
    (budget : acc.val≤3*(2147483647-1)^2) :
    ∃ out : U64,
      AspisR1PoseidonPreparedChannelGeneratedStep.generatedChannelUpdate a b acc=ok out ∧
      out.val=acc.val+a.val*b.val := by
  obtain ⟨product,prun,pvalue⟩:=NFT_Dot.scalar_product a b ha hb
  have product_bound : a.val*b.val≤(2147483647-1)^2 := by
    calc
      a.val*b.val≤(2147483647-1)*(2147483647-1) := Nat.mul_le_mul (by omega) (by omega)
      _=(2147483647-1)^2 := by ring
  have sum_bound : acc.val+product.val<2^64 := by
    rw [pvalue]
    have total : acc.val+a.val*b.val≤4*(2147483647-1)^2 := by omega
    exact lt_of_le_of_lt total (by norm_num)
  obtain ⟨out,run,value⟩:=AspisR1.ExtractedMaskReducerOps.add_success acc product sum_bound
  refine ⟨out,?_,?_⟩
  · change (do let p ← UScalar.mul (UScalar.cast .U64 a) (UScalar.cast .U64 b); UScalar.add acc p)=ok out
    rw [prun]
    exact run
  · rw [value,pvalue]

#print axioms generated_step
end NFT_ChannelFour
