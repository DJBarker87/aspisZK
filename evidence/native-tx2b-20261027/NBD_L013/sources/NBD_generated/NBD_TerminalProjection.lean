import AspisR1TerminalDecoder.Funs
set_option autoImplicit false
namespace NBD_TerminalProjection
open Aeneas Aeneas.Std Result WP
open AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal
abbrev Statement := PoolV1PairForestTerminalStatementV1
abbrev Common := PoolV1PairForestTerminalCommonV1
abbrev Kind := pool_v1.historical_anchor.PoolV1TransitionKind
abbrev Error := PoolV1PairForestTerminalFormatErrorV1
abbrev Parts := Array U8 32#usize × Array U8 32#usize × U64 × Array U32 8#usize × Array U32 8#usize × U32

def common : Statement → Common
  | .PrivateTransfer c _ => c
  | .Withdrawal c _ => c

def parts : Statement → Parts
  | .PrivateTransfer _ p => (p.pool,p.deployment_domain,p.anchor_sequence,p.anchor_root,p.nullifier,p.asset_id)
  | .Withdrawal _ p => (p.pool,p.deployment_domain,p.anchor_sequence,p.anchor_root,p.nullifier,p.asset_id)

def kind (b : U8) : core.result.Result Kind Error :=
  if b = 1#u8 then .Ok .PrivateTransfer
  else if b = 2#u8 then .Ok .Withdrawal
  else .Err .InvalidTransitionKind

/-- Arbitrary fields and both variants; no validation success is assumed. -/
theorem source_common (s : Statement) : s.common = ok (common s) := by
  cases s <;> rfl

theorem source_parts (s : Statement) : statement_public_common s = ok (parts s) := by
  cases s <;> rfl

/-- Exact invalid-byte rejection, as well as both valid discriminants. -/
theorem source_kind (b : U8) : transition_kind b = ok (kind b) := by
  have spec : transition_kind b ⦃ out => out = kind b ⦄ := by
    unfold transition_kind
    step*
    all_goals simp_all [kind]
    all_goals scalar_tac
  obtain ⟨out,call,same⟩ := WP.spec_imp_exists spec
  rw [same] at call
  exact call

/-- The nullifier used by callers is the fifth field of the SAME tuple. -/
theorem nullifier_same (s : Statement) :
    (parts s).2.2.2.2.1 = match s with
      | .PrivateTransfer _ p => p.nullifier
      | .Withdrawal _ p => p.nullifier := by
  cases s <;> rfl

#print axioms source_common
#print axioms source_parts
#print axioms source_kind
#print axioms nullifier_same
end NBD_TerminalProjection
