import Lean
import NFY_Part026
import NFY_Part025

-- BEGIN copied NBN_BindingChecks: lean/NBN_BindingChecks.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_BindingChecks
abbrev ErrT := NFY_NBN_StatementResult.Error
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder NFY_NBN_StatementResult
abbrev Common := pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1
attribute [local instance] Classical.propDecidable

def chain (c : Common) (p : NBD_TerminalProjection.Parts)
    (tail : core.result.Result Unit ErrT) : core.result.Result Unit ErrT :=
  if p.1 ≠ c.master_account then .Err .MasterBindingMismatch
  else if p.2.1 ≠ c.lane_transition.live_snapshot.deployment_domain then .Err .DeploymentBindingMismatch
  else if c.lane_transition.live_snapshot.pool ≠ c.master_account then .Err .MasterBindingMismatch
  else if p.2.2.1 ≠ c.checkpoint_sequence then .Err .CheckpointBindingMismatch
  else if p.2.2.2.1 ≠ c.historical_global_anchor then .Err .HistoricalAnchorMismatch
  else tail

def tail (s : Statement) : core.result.Result Unit ErrT :=
  match NFY_NBN_OutputLane.result (parts s).2.2.2.2.1 with
  | .Err e => .Err (.Account e)
  | .Ok lane => if lane ≠ (common s).output_lane then .Err .OutputLaneMismatch
    else match lateStatus (common s).lane_transition with
      | .Err e => .Err (.LaneTransition e)
      | .Ok _ => .Ok ()

theorem factor (s : Statement) : suffix s = chain (common s) (parts s) (tail s) := by
  cases s <;> rfl

theorem fields (c : Common) (p : NBD_TerminalProjection.Parts)
    (t : core.result.Result Unit ErrT) (h : chain c p t = .Ok ()) :
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
end NFY_NBN_BindingChecks
-- END copied NBN_BindingChecks
-- BEGIN copied NBN_StatementCut: lean/NBN_StatementCut.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_StatementCut
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder NFY_NBN_StatementResult
attribute [local instance] Classical.propDecidable
abbrev PE := pool_v1.payment_relation.PoolV1PaymentStatementFormatError
abbrev AE := pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
abbrev LE := pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
abbrev E := NFY_NBN_StatementResult.Error

def tail (s : Statement) (lane : core.result.Result U8 AE) (late : core.result.Result Unit LE) :
    core.result.Result Unit E :=
  match lane with
  | .Err e => .Err (.Account e)
  | .Ok l => if l ≠ (common s).output_lane then .Err .OutputLaneMismatch
    else match late with
      | .Err e => .Err (.LaneTransition e)
      | .Ok _ => .Ok ()

/-- Exact native K003 control cut. Child values are arbitrary, not successful. -/
def run (s : Statement) (pay : Result (core.result.Result (Array U8 216#usize) PE))
    (lane : core.result.Result U8 AE) (late : core.result.Result Unit LE) : Result (core.result.Result Unit E) :=
  if (common s).master_account = zero ∨ (common s).checkpoint_account = zero ∨
      (common s).selected_lane_account = zero then ok (.Err .NonZeroBinding)
  else if 8 ≤ (common s).output_lane.val then ok (.Err .InvalidOutputLane)
  else do
    let r ← pay
    match r with
    | .Err e => ok (.Err (.Payment e))
    | .Ok _ => ok (NFY_NBN_BindingChecks.chain (common s) (parts s) (tail s lane late))

theorem source (s : Statement) :
    pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s =
      run s (payment s) (NFY_NBN_OutputLane.result (parts s).2.2.2.2.1)
        (lateStatus (common s).lane_transition) := by
  rw [NFY_NBN_StatementResult.source]
  cases s <;> rfl

/-- Substitution uses only exact lower Results on the SAME input/variant. -/
theorem lower_substitution (s : Statement)
    (pay : Result (core.result.Result (Array U8 216#usize) PE))
    (lane : core.result.Result U8 AE) (late : core.result.Result Unit LE)
    (payment_exact : pay = payment s)
    (lane_exact : lane = NFY_NBN_OutputLane.result (parts s).2.2.2.2.1)
    (late_exact : late = lateStatus (common s).lane_transition) :
    run s pay lane late =
      pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s := by
  rw [payment_exact,lane_exact,late_exact,source]

#print axioms source
#print axioms lower_substitution
end NFY_NBN_StatementCut
-- END copied NBN_StatementCut
-- BEGIN copied NBN_ValidatorSummary: lean/NBN_ValidatorSummary.lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace NFY_NBN_ValidatorSummary
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder NFY_NBN_StatementResult
attribute [local instance] Classical.propDecidable
abbrev E := NFY_NBN_StatementResult.Error
abbrev Transfer := pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
abbrev Withdrawal := pool_v1.payment_relation.PoolV1WithdrawalPublicV1
abbrev PaymentResult := Result (core.result.Result (Array U8 216#usize) PaymentError)
abbrev Encode := NFY_NBN_EncoderSummary.Encode

def NBN_Dep_TransferEncode (f : Transfer → PaymentResult) : Prop :=
  ∀ p, f p = pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 p

def NBN_Dep_WithdrawalEncode (f : Withdrawal → PaymentResult) : Prop :=
  ∀ p, f p = pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 p

def paymentWith (t : Transfer → PaymentResult) (w : Withdrawal → PaymentResult) : Statement → PaymentResult
  | .PrivateTransfer _ p => t p
  | .Withdrawal _ p => w p

theorem payment_source (t : Transfer → PaymentResult) (w : Withdrawal → PaymentResult)
    (ht : NBN_Dep_TransferEncode t) (hw : NBN_Dep_WithdrawalEncode w) (s : Statement) :
    paymentWith t w s = payment s := by
  cases s <;> first | exact ht _ | exact hw _

def chain (c : NFY_NBN_BindingChecks.Common) (p : NBD_TerminalProjection.Parts)
    (tail : Result (core.result.Result Unit E)) : Result (core.result.Result Unit E) :=
  if p.1 ≠ c.master_account then ok (.Err .MasterBindingMismatch)
  else if p.2.1 ≠ c.lane_transition.live_snapshot.deployment_domain then ok (.Err .DeploymentBindingMismatch)
  else if c.lane_transition.live_snapshot.pool ≠ c.master_account then ok (.Err .MasterBindingMismatch)
  else if p.2.2.1 ≠ c.checkpoint_sequence then ok (.Err .CheckpointBindingMismatch)
  else if p.2.2.2.1 ≠ c.historical_global_anchor then ok (.Err .HistoricalAnchorMismatch)
  else tail

theorem chain_pure (c : NFY_NBN_BindingChecks.Common) (p : NBD_TerminalProjection.Parts)
    (tail : core.result.Result Unit E) :
    chain c p (ok tail) = ok (NFY_NBN_BindingChecks.chain c p tail) := by
  unfold chain NFY_NBN_BindingChecks.chain
  repeat' first | rfl | split

def tail (enc : Encode) (s : Statement) : Result (core.result.Result Unit E) := do
  let lane ← NFY_NBN_FirstByteDependency.lane enc (parts s).2.2.2.2.1
  match lane with
  | .Err e => ok (.Err (.Account e))
  | .Ok l =>
    if l ≠ (common s).output_lane then ok (.Err .OutputLaneMismatch)
    else do
      let (r,_) ← NFY_NBN_LateSummary.run enc (common s).lane_transition NFY_NBN_LateResult.zero
      match r with
      | .Err e => ok (.Err (.LaneTransition e))
      | .Ok _ => ok (.Ok ())

theorem tail_source (enc : Encode)
    (lower : NFY_NBN_DigestResultDependency.NBN_Dep_DigestEncodeCanonical enc) (s : Statement) :
    tail enc s = ok (NFY_NBN_BindingChecks.tail s) := by
  unfold tail
  rw [NFY_NBN_FirstByteDependency.lane_source enc lower,NFY_NBN_OutputLane.source]
  simp only [bind_tc_ok]
  unfold NFY_NBN_BindingChecks.tail
  cases lane : NFY_NBN_OutputLane.result (parts s).2.2.2.2.1 with
  | Err e => rfl
  | Ok l =>
    by_cases mismatch : l = (common s).output_lane
    · simp only [mismatch,ne_eq,not_true_eq_false,if_false]
      rw [NFY_NBN_LateSummary.source enc lower,NFY_NBN_LateResult.source]
      have len : NFY_NBN_LateResult.zero.length = 1520 := by
        simp only [NFY_NBN_LateResult.zero,Slice.length,Array.to_slice,Array.repeat_val,List.length_replicate]
        rfl
      rw [if_neg (not_not.mpr len)]
      unfold lateStatus
      by_cases index : U64.checked_add (common s).lane_transition.live_snapshot.next_pair_index 1#u64 ≠
          some (common s).lane_transition.candidate_afterstate.next_pair_index
      · simp only [ne_eq] at index
        simp only [ne_eq,index,not_false_eq_true,if_true,bind_tc_ok]
        rfl
      · simp only [index,if_false,bind_tc_ok,Aeneas.Std.uncurry]
        cases NFY_NBN_LateTail.status (common s).lane_transition <;> rfl
    · simp only [mismatch,ne_eq,not_false_eq_true,if_true]

def run (enc : Encode) (t : Transfer → PaymentResult) (w : Withdrawal → PaymentResult) (s : Statement) :
    Result (core.result.Result Unit E) :=
  if (common s).master_account = zero ∨ (common s).checkpoint_account = zero ∨
      (common s).selected_lane_account = zero then ok (.Err .NonZeroBinding)
  else if 8 ≤ (common s).output_lane.val then ok (.Err .InvalidOutputLane)
  else do
    let pay ← paymentWith t w s
    match pay with
    | .Err e => ok (.Err (.Payment e))
    | .Ok _ => chain (common s) (parts s) (tail enc s)

theorem source (enc : Encode) (t : Transfer → PaymentResult) (w : Withdrawal → PaymentResult)
    (hd : NFY_NBN_DigestResultDependency.NBN_Dep_DigestEncodeCanonical enc)
    (ht : NBN_Dep_TransferEncode t) (hw : NBN_Dep_WithdrawalEncode w) (s : Statement) :
    run enc t w s = pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s := by
  rw [NFY_NBN_StatementResult.source]
  unfold run result
  dsimp only
  rw [payment_source t w ht hw s,tail_source enc hd s,chain_pure,← NFY_NBN_BindingChecks.factor s]
  rfl

#print axioms payment_source
#print axioms chain_pure
#print axioms tail_source
#print axioms source
end NFY_NBN_ValidatorSummary
-- END copied NBN_ValidatorSummary
-- BEGIN copied NBN_StatementDomains: lean/NBN_StatementDomains.lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace NFY_NBN_StatementDomains
open Aeneas Aeneas.Std Result
open NFY_NBN_StatementResult
open AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal

/-- Same-variant child, not an independently selected successful payment. -/
theorem payment_reached (s : Statement)
    (accepted : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    ∃ bytes, payment s = ok (.Ok bytes) ∧ suffix s = .Ok () := by
  rw [source] at accepted
  unfold result at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · cases hp : payment s with
      | fail e => simp only [hp,bind_tc_fail] at accepted; cases accepted
      | div => simp only [hp,bind_tc_div] at accepted; cases accepted
      | ok r =>
        simp only [hp,bind_tc_ok] at accepted
        cases r with
        | Err e => cases accepted
        | Ok bytes => exact ⟨bytes,rfl,Result.ok.inj accepted⟩

theorem bindings (s : Statement)
    (accepted : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    (parts s).1 = (common s).master_account ∧
    (parts s).2.1 = (common s).lane_transition.live_snapshot.deployment_domain ∧
    (common s).lane_transition.live_snapshot.pool = (common s).master_account ∧
    (parts s).2.2.1 = (common s).checkpoint_sequence ∧
    (parts s).2.2.2.1 = (common s).historical_global_anchor := by
  obtain ⟨_,_,h⟩ := payment_reached s accepted
  rw [NFY_NBN_BindingChecks.factor] at h
  exact NFY_NBN_BindingChecks.fields (common s) (parts s) (NFY_NBN_BindingChecks.tail s) h

theorem lane_late (s : Statement)
    (accepted : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    NFY_NBN_OutputLane.result (parts s).2.2.2.2.1 = .Ok (common s).output_lane ∧
    lateStatus (common s).lane_transition = .Ok () := by
  obtain ⟨_,_,h⟩ := payment_reached s accepted
  obtain ⟨hp,hd,hl,hs,ha⟩ := bindings s accepted
  simp only [suffix,hp,hd,hl,hs,ha,ne_eq,not_true_eq_false,if_false] at h
  cases lane : NFY_NBN_OutputLane.result (parts s).2.2.2.2.1 with
  | Err e => simp only [lane] at h; cases h
  | Ok value =>
    simp only [lane] at h
    split at h
    · cases h
    · rename_i same
      have eq : value = (common s).output_lane := not_not.mp same
      subst value
      refine ⟨rfl,?_⟩
      cases late : lateStatus (common s).lane_transition with
      | Err e => simp only [late] at h; cases h
      | Ok u => cases u; rfl

theorem late_children (s : Statement)
    (accepted : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    U64.checked_add (common s).lane_transition.live_snapshot.next_pair_index 1#u64 =
      some (common s).lane_transition.candidate_afterstate.next_pair_index ∧
    NFY_NBH_LiveValidator.result (common s).lane_transition.live_snapshot = .Ok () ∧
    NFY_NBH_Validators.afterResult (common s).lane_transition.candidate_afterstate = .Ok () := by
  have h := (lane_late s accepted).2
  unfold lateStatus at h
  split at h
  · cases h
  · rename_i index
    refine ⟨not_not.mp index,?_⟩
    unfold NFY_NBN_LateTail.status at h
    cases live : NFY_NBH_LiveValidator.result (common s).lane_transition.live_snapshot with
    | Err e => simp only [live] at h; cases h
    | Ok u =>
      cases u
      simp only [live] at h
      refine ⟨rfl,?_⟩
      cases after : NFY_NBH_Validators.afterResult (common s).lane_transition.candidate_afterstate with
      | Err e => simp only [after] at h; cases h
      | Ok u => cases u; rfl

#print axioms payment_reached
#print axioms bindings
#print axioms lane_late
#print axioms late_children
end NFY_NBN_StatementDomains
-- END copied NBN_StatementDomains

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
