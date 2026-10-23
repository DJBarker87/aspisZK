import S6SourceAfterstateValidatorTotalV1
import S6SourcePaymentCommonEncodeTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.AfterstateEncodeTotal
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.pair_terminal

@[step] theorem validator_spec (afterstate : PoolV1PairVerifiedAfterstateV1) :
    validate_verified_afterstate afterstate ⦃ _ => True ⦄ := by
  obtain ⟨out,h⟩ := AfterstateTotal.afterstate_total afterstate
  rw [h,WP.spec_ok]
  trivial

private theorem array_slice_length {T : Type} {N : Usize} (a : Array T N) :
    (Array.to_slice a).length=N.val := by
  change a.val.length=N.val
  exact a.property

/-- TOTAL complete688-byte afterstate encoder, including all twenty nodes. -/
@[step] theorem write_spec (afterstate : PoolV1PairVerifiedAfterstateV1) :
    encode_pool_v1_pair_verified_afterstate_v1 afterstate ⦃ _ => True ⦄ := by
  unfold encode_pool_v1_pair_verified_afterstate_v1
  step*
  all_goals (simp_all only [array_slice_length] <;> scalar_tac)

theorem write_total (afterstate : PoolV1PairVerifiedAfterstateV1) :
    ∃ out,encode_pool_v1_pair_verified_afterstate_v1 afterstate=ok out := by
  obtain ⟨out,h,_⟩ := spec_imp_exists (write_spec afterstate)
  exact ⟨out,h⟩

#print axioms validator_spec
#print axioms write_total
end AspisS6SourceCodec.AfterstateEncodeTotal
