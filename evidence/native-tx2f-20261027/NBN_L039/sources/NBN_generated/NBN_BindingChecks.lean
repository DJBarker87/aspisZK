import NBN_StatementResult
set_option autoImplicit false
noncomputable section
namespace NBN_BindingChecks
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder NBN_StatementResult
abbrev Common := pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1
attribute [local instance] Classical.propDecidable

def chain (c : Common) (p : NBD_TerminalProjection.Parts)
    (tail : core.result.Result Unit Error) : core.result.Result Unit Error :=
  if p.1 ≠ c.master_account then .Err .MasterBindingMismatch
  else if p.2.1 ≠ c.lane_transition.live_snapshot.deployment_domain then .Err .DeploymentBindingMismatch
  else if c.lane_transition.live_snapshot.pool ≠ c.master_account then .Err .MasterBindingMismatch
  else if p.2.2.1 ≠ c.checkpoint_sequence then .Err .CheckpointBindingMismatch
  else if p.2.2.2.1 ≠ c.historical_global_anchor then .Err .HistoricalAnchorMismatch
  else tail

def tail (s : Statement) : core.result.Result Unit Error :=
  match NBN_OutputLane.result (parts s).2.2.2.2.1 with
  | .Err e => .Err (.Account e)
  | .Ok lane => if lane ≠ (common s).output_lane then .Err .OutputLaneMismatch
    else match lateStatus (common s).lane_transition with
      | .Err e => .Err (.LaneTransition e)
      | .Ok _ => .Ok ()

theorem factor (s : Statement) : suffix s = chain (common s) (parts s) (tail s) := by
  cases s <;> rfl

theorem fields (c : Common) (p : NBD_TerminalProjection.Parts)
    (t : core.result.Result Unit Error) (h : chain c p t = .Ok ()) :
    p.1 = c.master_account ∧ p.2.1 = c.lane_transition.live_snapshot.deployment_domain ∧
    c.lane_transition.live_snapshot.pool = c.master_account ∧
    p.2.2.1 = c.checkpoint_sequence ∧ p.2.2.2.1 = c.historical_global_anchor := by
  unfold chain at h
  by_cases h1 : p.1 = c.master_account
  · simp only [h1,ne_eq,not_true_eq_false,if_false] at h
    by_cases h2 : p.2.1 = c.lane_transition.live_snapshot.deployment_domain
    · simp only [h2,ne_eq,not_true_eq_false,if_false] at h
      by_cases h3 : c.lane_transition.live_snapshot.pool = c.master_account
      · simp only [h3,ne_eq,not_true_eq_false,if_false] at h
        by_cases h4 : p.2.2.1 = c.checkpoint_sequence
        · simp only [h4,ne_eq,not_true_eq_false,if_false] at h
          by_cases h5 : p.2.2.2.1 = c.historical_global_anchor
          · exact ⟨h1,h2,h3,h4,h5⟩
          · simp only [h5,ne_eq,not_false_eq_true,if_true] at h; cases h
        · simp only [h4,ne_eq,not_false_eq_true,if_true] at h; cases h
      · simp only [h3,ne_eq,not_false_eq_true,if_true] at h; cases h
    · simp only [h2,ne_eq,not_false_eq_true,if_true] at h; cases h
  · simp only [h1,ne_eq,not_false_eq_true,if_true] at h; cases h

#print axioms factor
#print axioms fields
end NBN_BindingChecks
