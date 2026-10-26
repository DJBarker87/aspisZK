import R1Z.PV_RunJoin_Source

/-! A fixed pure dictionary cannot associate two distinct successive native
entropy outputs at the same nonce. This is a boundary obstruction, not a
privacy counterexample. Native observations are retained separately. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativeRepeat
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev Secret := aspis_prover.state_only_entropy.StateOnlyAttemptSecrets

/-- Even choosing the pure dictionary per WHOLE sample cannot change the
result between two equal calls within that sample. -/
theorem incompatible_successes (nonce : Array U8 32#usize)
    (first second : Secret) (distinct : first ≠ second) :
    ¬ ∃ ops : ExternalFuns,
      letI : ExternalFuns := ops
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce nonce =
        .ok (.Ok first) ∧
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce nonce =
        .ok (.Ok second) := by
  rintro ⟨ops, hfirst, hsecond⟩
  have equal := hfirst.symm.trans hsecond
  exact distinct (by cases equal; rfl)

/-- The same obstruction survives an injective native representation, so
changing representation alone cannot supply the missing world argument. -/
theorem incompatible_representation {Native : Type}
    (encode : Native → Secret) (injective : Function.Injective encode)
    (nonce : Array U8 32#usize) (first second : Native) (distinct : first ≠ second) :
    ¬ ∃ ops : ExternalFuns,
      letI : ExternalFuns := ops
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce nonce =
        .ok (.Ok (encode first)) ∧
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce nonce =
        .ok (.Ok (encode second)) := by
  apply incompatible_successes nonce
  intro same
  exact distinct (injective same)

#print axioms incompatible_successes
#print axioms incompatible_representation
end R1Z.PV_RunJoin_NativeRepeat
