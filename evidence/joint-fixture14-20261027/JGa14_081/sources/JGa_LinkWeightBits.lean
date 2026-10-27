import JFy_Steps
import JGa_LinkBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_LinkWeightBits
open Aeneas Aeneas.Std Result WP FIq_Native
open pool_v1.pair_forest_copy_terminal

@[step] theorem bit (i : U64) : lift (i &&& 1#u64) ⦃ out => out.val≤1 ⦄ := by
  change (i &&& 1#u64).val≤1
  rw [UScalar.val_and]
  exact Nat.and_le_right
#print axioms bit

@[step] theorem cast (i : U64) (hi : i.val≤1) :
    lift (UScalar.cast .U32 i) ⦃ out => out.val≤1 ⦄ := by
  change (UScalar.cast .U32 i).val≤1
  scalar_tac
#print axioms cast

theorem keep (l : CompiledPoolV1PairForestLink) (index : U64)
    (v : PoolV1PairForestCompiledVariantV1) (hk : l.weight_kind=4#u8) (hl : l.weight_level.val<64) :
    ∃ w,link_weight l index v=ok w := by
  have spec : link_weight l index v ⦃ _ => True ⦄ := by
    unfold link_weight
    rw [hk]
    step* <;> scalar_tac
  obtain ⟨w,hw,_⟩ := WP.spec_imp_exists spec
  exact ⟨w,hw⟩
#print axioms keep

theorem complement (l : CompiledPoolV1PairForestLink) (index : U64)
    (v : PoolV1PairForestCompiledVariantV1) (hk : l.weight_kind=3#u8) (hl : l.weight_level.val<64) :
    ∃ w,link_weight l index v=ok w := by
  have spec : link_weight l index v ⦃ _ => True ⦄ := by
    unfold link_weight
    rw [hk]
    step* <;> scalar_tac
  obtain ⟨w,hw,_⟩ := WP.spec_imp_exists spec
  exact ⟨w,hw⟩
#print axioms complement
end AspisR1.JGa_LinkWeightBits
end
