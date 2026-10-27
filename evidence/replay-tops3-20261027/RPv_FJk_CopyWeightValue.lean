import RPv_FJk_CopyWeightSimple
import RPv_FJk_CopyWeightBits
set_option autoImplicit false
namespace AspisR1.FJk_CopyWeightValue
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal
variable {K : Type} [Field K]
/-- All five actual weight branches identified with the retained descriptor model. -/
theorem value (l : CompiledPoolV1PairForestLink) (index : U64)
    (v : PoolV1PairForestCompiledVariantV1) (out : U32)
    (hg : JGa_LinkBounds.Good l) (run : link_weight l index v=ok out) :
    (out.val : K)=R0P.copyLinkWeight (FJk_CopyDescriptor.link l) index.val
      (FJk_CopyDescriptor.variant v) ∧ out.val≤1 := by
  have kinds := hg.2.2.2.1
  rcases (by omega : l.weight_kind.val=0 ∨ l.weight_kind.val=1 ∨ l.weight_kind.val=2 ∨
    l.weight_kind.val=3 ∨ l.weight_kind.val=4) with hk|hk|hk|hk|hk
  · have h := FJk_CopyWeightSimple.zero l index v out (UScalar.eq_of_val_eq hk) run
    rw [h]
    simp [FJk_CopyDescriptor.link,R0P.copyLinkWeight,hk]
  · have h := FJk_CopyWeightSimple.transfer l index v out (UScalar.eq_of_val_eq hk) run
    rw [h]
    cases v <;> simp [FJk_CopyDescriptor.link,FJk_CopyDescriptor.variant,R0P.copyLinkWeight,hk]
  · have h := FJk_CopyWeightSimple.withdrawal l index v out (UScalar.eq_of_val_eq hk) run
    rw [h]
    cases v <;> simp [FJk_CopyDescriptor.link,FJk_CopyDescriptor.variant,R0P.copyLinkWeight,hk]
  · have h := FJk_CopyWeightBits.complement l index v out (UScalar.eq_of_val_eq hk) hg.2.2.2.2 run
    refine ⟨?_,h.2⟩
    rw [h.1]
    simp only [FJk_CopyDescriptor.link,R0P.copyLinkWeight,hk]
  · have h := FJk_CopyWeightBits.keep l index v out (UScalar.eq_of_val_eq hk) hg.2.2.2.2 run
    refine ⟨?_,h.2⟩
    rw [h.1]
    simp only [FJk_CopyDescriptor.link,R0P.copyLinkWeight,hk]
#print axioms value
end AspisR1.FJk_CopyWeightValue
