import NBN_ResultDependency
set_option autoImplicit false
noncomputable section
namespace NBN_ResultDomains
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open NBN_StatementResult NBN_ResultValidator
attribute [local instance] Classical.propDecidable

theorem fields (r : Record)
    (accepted : pool_v1.pair_forest_terminal.validate_result r = ok (.Ok ())) :
    r.master_account ≠ zero ∧ r.selected_lane_account ≠ zero ∧
    NBN_OutputLane.result r.nullifier = .Ok r.output_lane ∧
    NBH_Validators.afterResult r.verified_afterstate = .Ok () := by
  rw [source] at accepted
  unfold status at accepted
  split at accepted
  · cases accepted
  · rename_i nz
    have nonzero := not_or.mp nz
    cases lane : NBN_OutputLane.result r.nullifier with
    | Err e => simp only [lane] at accepted; cases accepted
    | Ok l =>
      simp only [lane] at accepted
      split at accepted
      · cases accepted
      · rename_i mismatch
        have same : r.output_lane = l := not_not.mp mismatch
        rw [← same] at lane
        cases after : NBH_Validators.afterResult r.verified_afterstate with
        | Err e => simp only [after] at accepted; cases accepted
        | Ok u => cases u; exact ⟨nonzero.1,nonzero.2,lane,rfl⟩

theorem nullifier_domain (r : Record)
    (accepted : pool_v1.pair_forest_terminal.validate_result r = ok (.Ok ())) :
    NBD_DigestInduction.Canonical r.nullifier := by
  have lane := (fields r accepted).2.2.1
  unfold NBN_OutputLane.result at lane
  split at lane
  · assumption
  · cases lane

#print axioms fields
#print axioms nullifier_domain
end NBN_ResultDomains
