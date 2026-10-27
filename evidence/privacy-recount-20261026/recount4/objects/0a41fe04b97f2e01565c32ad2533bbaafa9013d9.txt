import R1Z.PV_Join_PublicPrefix5
import R1Z.PV_Join_FixtureInputs
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_FixturePrefix5
open Aeneas Aeneas.Std Result ProverRwFull
variable [ProverRwRngCaller.NativeTypes] [ProverRwRngCaller.ErasureFns]

/-- Uniform for transfer and withdrawal compiler records. It proves the first
operation after entering the attempt, not that retry/admission reaches it. -/
theorem entered_input (base : ExternalTypes)
    (ops : @ExternalFuns (PV_Join_PublicCaller.native base))
    (input : PV_Src_NativeInput.Input)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize)) :
    letI : ExternalTypes := PV_Join_PublicCaller.native base
    ∀ (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
      (store : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore),
      ∃ next : PV_Join_PublicPrefix5.BytesReply → PV_Join_PublicPrefix5.AttemptReply,
        @prover.prove_masked_attempt _ (PV_Join_PublicCaller.selected base ops)
          (PV_Join_FixtureInputs.publicInput base input)
          (PV_Join_FixtureInputs.compiled base input.compiled) transport.Variant.S2
          hash attempt store =
        ((PV_Join_PublicCaller.selected base ops).op226
          (PV_Join_FixtureInputs.publicInput base input) >>= next) := by
  letI : ExternalTypes := PV_Join_PublicCaller.native base
  intro attempt store
  exact PV_Join_PublicPrefix5.first (PV_Join_PublicCaller.selected base ops)
    (PV_Join_FixtureInputs.publicInput base input)
    (PV_Join_FixtureInputs.compiled base input.compiled) transport.Variant.S2 hash attempt store

#print axioms entered_input
end R1Z.PV_Join_FixturePrefix5
