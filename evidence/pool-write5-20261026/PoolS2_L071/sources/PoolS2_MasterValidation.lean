import PoolS2_PolicyExact
import PoolS2_PdaSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolS2_MasterValidation
open Aeneas Aeneas.Std Result PoolS2_PdaSource
abbrev ForestError := AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
/-- Source constant: pair depth = tree depth = 20, capacity = 1u64 << 20. -/
def capacity : U64 := 1048576#u64
/-- Pure std iteration/equality interpretation of AENEAS010 validate_master.
Canonical complete Master carrier; error order preserved. This interpretation
is not a certificate for the native iterator, Box or caller. -/
def run (m : Master) : Result (core.result.Result Unit ForestError) := by
  classical
  exact do
    if m.identity.pool = PoolS2_PolicyFacts.zero ∨
        m.identity.asset_mint = PoolS2_PolicyFacts.zero ∨
        m.identity.token_program = PoolS2_PolicyFacts.zero ∨
        m.identity.deployment_domain = PoolS2_PolicyFacts.zero then
      ok (.Err .ZeroRequiredBinding)
    else
      let policy ← PoolS2_PolicySource.pool_v1.format.validate_verifier_policy_v1 m.verifier_policy
      match policy with
      | .Err _ => ok (.Err .Policy)
      | .Ok _ =>
        if m.last_checkpoint_lane_sequences.val.any (fun s => s > capacity) then
          ok (.Err .InvalidMasterState)
        else if m.has_checkpoint then
          if m.next_checkpoint_sequence = 0#u64 then ok (.Err .InvalidMasterState)
          else ok (.Ok ())
        else if m.next_checkpoint_sequence ≠ 0#u64 then ok (.Err .InvalidMasterState)
        else if m.last_checkpoint_lane_sequences ≠ Array.repeat 8#usize 0#u64 then
          ok (.Err .InvalidMasterState)
        else ok (.Ok ())

#print axioms run
end AspisR1.PoolS2_MasterValidation
end
