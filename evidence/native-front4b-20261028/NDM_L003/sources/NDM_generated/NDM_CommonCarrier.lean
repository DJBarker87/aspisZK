import NDM_Reference.Funs
import AdapterRwModel
set_option autoImplicit false
namespace NDM_CommonCarrier
open Aeneas Aeneas.Std Result
open AdapterRw
open aspis_statement.pool_v1
abbrev Common := pair_forest_terminal.PoolV1PairForestTerminalCommonV1
abbrev Candidate := pair_terminal.PoolV1PairVerifiedAfterstateV1

def value (a : r1_pool_adapter.AuthenticatedAsq8Accounts) (c : Candidate) : Common :=
 ⟨a.master_account,a.checkpoint_account,a.selected_lane_account,a.selected_lane.lane_id,
  a.checkpoint.checkpoint_sequence,a.checkpoint.global_root,⟨a.live_snapshot,c⟩⟩

def project (c : Common) := (c.master_account,c.checkpoint_account,c.selected_lane_account,
 c.output_lane,c.checkpoint_sequence,c.historical_global_anchor,
 c.lane_transition.live_snapshot,c.lane_transition.candidate_afterstate)

theorem reference (a : r1_pool_adapter.AuthenticatedAsq8Accounts) (c : Candidate) :
 NDM_Reference.common_ref a.master_account a.checkpoint_account a.selected_lane_account
 a.selected_lane.lane_id a.checkpoint.checkpoint_sequence a.checkpoint.global_root
 a.live_snapshot c = ok (project (value a c)) := rfl

theorem project_injective (a b : Common) (same : project a = project b) : a=b := by
 cases a with
 | mk am ac al ao asq ah at =>
  cases b with
  | mk bm bc bl bo bsq bh bt =>
   cases at
   cases bt
   simp_all [project]

/-- This is a carrier equality. The native projection hypotheses are separate obligations. -/
theorem assemble (a : r1_pool_adapter.AuthenticatedAsq8Accounts) (c : Candidate)
 (actual : Common) (windows : project actual = project (value a c)) :
 actual = value a c := project_injective actual (value a c) windows

#print axioms reference
#print axioms project_injective
#print axioms assemble
end NDM_CommonCarrier
