import AspisR1TerminalResultConstructorCut.Funs

/-! The exact initial record constructor in selected `emit_result`, extracted
with its three actual Statement methods. Validators, serialization and SDK
return-data effects are outside this cut. -/
set_option autoImplicit false
namespace AspisR1.TerminalResultConstructorFields
open Aeneas Aeneas.Std Result
open AspisR1TerminalResultConstructorCut
abbrev Statement := PoolV1PairForestTerminalStatementV1
abbrev Output := PoolV1PairForestTerminalResultV1

def common : Statement → PoolV1PairForestTerminalCommonV1
  | .PrivateTransfer c _ => c
  | .Withdrawal c _ => c

def kind : Statement → PoolV1TransitionKind
  | .PrivateTransfer _ _ => .PrivateTransfer
  | .Withdrawal _ _ => .Withdrawal

def nullifier : Statement → Array U32 8#usize
  | .PrivateTransfer _ p => p.nullifier
  | .Withdrawal _ p => p.nullifier

def value (s : Statement) : Output where
  transition_kind := kind s
  master_account := (common s).master_account
  selected_lane_account := (common s).selected_lane_account
  output_lane := (common s).output_lane
  nullifier := nullifier s
  verified_afterstate := (common s).lane_transition.candidate_afterstate

/-- All methods in the actual emitted constructor succeed, for either variant,
and the resulting afterstate is the candidate in that same statement. -/
theorem source_success (s : Statement) :
    emitted_result_value s = .ok (value s) := by
  cases s <;> rfl

theorem successful_source_fields (s : Statement) (out : Output)
    (h : emitted_result_value s = .ok out) :
    out.transition_kind = kind s ∧
    out.master_account = (common s).master_account ∧
    out.selected_lane_account = (common s).selected_lane_account ∧
    out.output_lane = (common s).output_lane ∧
    out.nullifier = nullifier s ∧
    out.verified_afterstate = (common s).lane_transition.candidate_afterstate := by
  have hout : out = value s := by
    rw [source_success] at h
    exact (Result.ok.inj h).symm
  subst out
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms source_success
#print axioms successful_source_fields
end AspisR1.TerminalResultConstructorFields
