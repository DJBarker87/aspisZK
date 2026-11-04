import NEU_ReconstructCore
import NDM_AdoptedReconstruction
set_option autoImplicit false
noncomputable section
namespace NEU_ReconstructAdopted
open Aeneas Aeneas.Std Result AdapterRw
open AspisR1.JHf_Carrier
abbrev Request := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
abbrev Auth := r1_pool_adapter.AuthenticatedAsq8Accounts
abbrev Candidate := NDM_CommonCarrier.Candidate

def run {State : Type} (request : Request) (a : Auth) (c : Candidate) (state : State) :=
  let observed := NEU_ReconstructCore.run (toRequest request)
    (toAuthenticatedAsq8Accounts a) (toPoolV1PairVerifiedAfterstateV1 c) state
  ((do let reply ← observed.1; ok (NDM_CohortStatement.transport reply)),observed.2.1,observed.2.2)

/-- Exact selected op52 source, full Result, external state and ordered child
trace. All constructor validator hypotheses are discharged in the model.
This needs the separate native certificates to become a composed root. -/
theorem result_state_effects {State : Type} (request : Request) (a : Auth)
    (c : Candidate) (state : State) :
    run request a c state =
    (AspisR1.JHf_ReconstructionSlot.source request a c,state,
      NEU_ReconstructCore.trace (toRequest request) (toAuthenticatedAsq8Accounts a)
        (toPoolV1PairVerifiedAfterstateV1 c)) := by
  unfold run
  rw [NEU_ReconstructCore.result_state_effects]
  dsimp only
  unfold AspisR1.JHf_ReconstructionSlot.source
  cases call : AspisR1AdapterReconstruct.r1_pool_adapter.reconstruct_asq8_statement
    (toRequest request) (toAuthenticatedAsq8Accounts a) (toPoolV1PairVerifiedAfterstateV1 c) with
  | fail e => rfl
  | div => rfl
  | ok reply => cases reply <;> rfl

#print axioms result_state_effects
end NEU_ReconstructAdopted
