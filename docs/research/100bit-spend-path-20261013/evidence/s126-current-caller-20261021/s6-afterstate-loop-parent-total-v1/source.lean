import S6AfterstateLoopParentSourceV1
import S6OwnedFrontierTotalV1
import S6SourceAfterstateValidatorTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6AfterstateLoopParent.Total
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.pair_terminal

/-- The whole native carrier and all twenty iterations agree with the
focused helper reference; only namespace/type-alias spelling differs. -/
theorem frontier_eq (afterstate : PoolV1PairVerifiedAfterstateV1) (output : Array U8 688#usize) :
    frontier_owned_reference afterstate output =
      AspisS6OwnedFrontier.frontier_owned afterstate output := by
  rfl

@[step] theorem frontier_spec (afterstate : PoolV1PairVerifiedAfterstateV1)
    (output : Array U8 688#usize) :
    frontier_owned_reference afterstate output ⦃ _ => True ⦄ := by
  rw [frontier_eq]
  obtain ⟨result,h⟩ := AspisS6OwnedFrontier.Total.frontier_total afterstate output
  rw [h,WP.spec_ok]
  trivial

@[step] theorem validator_spec (afterstate : PoolV1PairVerifiedAfterstateV1) :
    AspisS6SourceCodec.aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate afterstate
      ⦃ _ => True ⦄ := by
  obtain ⟨result,h⟩ := AspisS6SourceCodec.AfterstateTotal.afterstate_total afterstate
  rw [h,WP.spec_ok]
  trivial

private theorem array_slice_length {T : Type} {N : Usize} (a : Array T N) :
    (Array.to_slice a).length=N.val := by
  change a.val.length=N.val
  exact a.property

/-- TOTAL enclosing native-type encoder reference, actual validation/header/
error paths and all688 output bytes. No child-success or canonicality premise. -/
@[step] theorem encode_spec (afterstate : PoolV1PairVerifiedAfterstateV1) :
    encode afterstate ⦃ _ => True ⦄ := by
  unfold encode encode_pool_v1_pair_verified_afterstate_v1
  step*
  all_goals (simp_all only [array_slice_length] <;> scalar_tac)

theorem encode_total (afterstate : PoolV1PairVerifiedAfterstateV1) :
    ∃ out, encode afterstate=ok out := by
  obtain ⟨out,h,_⟩ := spec_imp_exists (encode_spec afterstate)
  exact ⟨out,h⟩

#print axioms frontier_eq
#print axioms frontier_spec
#print axioms encode_total
end AspisS6AfterstateLoopParent.Total
