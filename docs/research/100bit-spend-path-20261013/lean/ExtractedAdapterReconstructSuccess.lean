import AspisR1AdapterReconstruct.Funs

/-! Success inversion for the exact extracted adapter reconstruction leaf.
`AuthenticatedAsq8Accounts` is a structural input here: this theorem does not
establish owner, PDA, custody, account-constructor, or runtime reachability. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1AdapterReconstruct.AdapterReconstructSuccess
open aspis_statement.pool_v1.pair_forest_terminal
open aspis_statement.pool_v1.payment_relation
open aspis_statement.pool_v1.pair_terminal
open r1_pool_adapter

/-- The fixed field copy performed by the actual `asq8_common`. -/
def common (a : AuthenticatedAsq8Accounts) (candidate : PoolV1PairVerifiedAfterstateV1) :
    PoolV1PairForestTerminalCommonV1 :=
  { master_account := a.master_account
    checkpoint_account := a.checkpoint_account
    selected_lane_account := a.selected_lane_account
    output_lane := a.selected_lane.lane_id
    checkpoint_sequence := a.checkpoint.checkpoint_sequence
    historical_global_anchor := a.checkpoint.global_root
    lane_transition := { live_snapshot := a.live_snapshot, candidate_afterstate := candidate } }

theorem asq8_common_exact (a : AuthenticatedAsq8Accounts)
    (candidate : PoolV1PairVerifiedAfterstateV1) :
    asq8_common a candidate = ok (common a candidate) := rfl

/-- Exactly the public variant and value supplied in the request. -/
def statement (c : PoolV1PairForestTerminalCommonV1)
    (p : PoolV1PairForestTerminalPaymentV1) : PoolV1PairForestTerminalStatementV1 :=
  match p with
  | .PrivateTransfer v => .PrivateTransfer c v
  | .Withdrawal v => .Withdrawal c v

def requestedAsset (p : PoolV1PairForestTerminalPaymentV1) : aspis_core.field.M31 :=
  match p with
  | .PrivateTransfer v => v.asset_id
  | .Withdrawal v => v.asset_id

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem bool_guard_success {α ε : Type} (m : Result Bool) (e : ε)
    (k : Result (core.result.Result α ε)) (v : α)
    (h : (do let b ← m; if b then ok (.Err e) else k) = ok (.Ok v)) :
    m = ok false ∧ k = ok (.Ok v) := by
  obtain ⟨b, hb, hk⟩ := bind_success _ _ _ h
  cases b with
  | false => exact ⟨hb, by simpa only [Bool.false_eq_true, ↓reduceIte] using hk⟩
  | true => simp only [↓reduceIte] at hk; cases hk

private theorem option_ne_false (x : Option U64) (y : U64)
    (h : core.cmp.PartialEq.ne.trait_default
      (core.option.Option.Insts.CoreCmpPartialEqOption core.cmp.PartialEqU64)
      x (some y) = ok false) : x = some y := by
  cases x with
  | none =>
    simp only [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      core.option.Option.Insts.CoreCmpPartialEqOption.eq, optionDiscriminant_some, bind_tc_ok] at h
    have hn : (1#isize : Isize) ≠ 0#isize := by scalar_tac
    simp only [hn, decide_false, Bool.false_eq_true, not_false_eq_true, decide_true] at h
    cases h
  | some v =>
    simp only [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      core.option.Option.Insts.CoreCmpPartialEqOption.eq, bind_tc_ok] at h
    have hv : v = y := UScalar.val_eq_imp _ _ (by simpa using h)
    exact congrArg some hv

private theorem m31_ne_false (x y : aspis_core.field.M31)
    (h : core.cmp.PartialEq.ne.trait_default
      aspis_core.field.M31.Insts.CoreCmpPartialEqM31 x y = ok false) : x = y := by
  simp only [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq, bind_tc_ok] at h
  exact UScalar.val_eq_imp _ _ (by simpa using h)

theorem transfer_box_success (c : PoolV1PairForestTerminalCommonV1)
    (p : PoolV1PrivateTransferPublicV1) (out : PoolV1PairForestTerminalStatementV1)
    (h : transfer_statement_box c p = ok (.Ok out)) :
    out = .PrivateTransfer c p ∧
    validate_pool_v1_pair_forest_terminal_statement_v1 (.PrivateTransfer c p) = ok (.Ok ()) := by
  unfold transfer_statement_box at h
  obtain ⟨r, hr, h⟩ := bind_success _ _ _ h
  cases r with
  | Err e =>
    simp only [core.result.Result.map_err,
      transfer_statement_box.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once,
      bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at h
    cases h
  | Ok value =>
    cases value
    simp only [core.result.Result.map_err, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch] at h
    exact ⟨by simpa only [Result.ok.injEq, core.result.Result.Ok.injEq] using h.symm, hr⟩

theorem withdrawal_box_success (c : PoolV1PairForestTerminalCommonV1)
    (p : PoolV1WithdrawalPublicV1) (out : PoolV1PairForestTerminalStatementV1)
    (h : withdrawal_statement_box c p = ok (.Ok out)) :
    out = .Withdrawal c p ∧
    validate_pool_v1_pair_forest_terminal_statement_v1 (.Withdrawal c p) = ok (.Ok ()) := by
  unfold withdrawal_statement_box at h
  obtain ⟨r, hr, h⟩ := bind_success _ _ _ h
  cases r with
  | Err e =>
    simp only [core.result.Result.map_err,
      withdrawal_statement_box.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once,
      bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at h
    cases h
  | Ok value =>
    cases value
    simp only [core.result.Result.map_err, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch] at h
    exact ⟨by simpa only [Result.ok.injEq, core.result.Result.Ok.injEq] using h.symm, hr⟩

/-- Successful actual reconstruction fixes the public value, candidate, every
copied account/checkpoint field, the two guards, and actual terminal success. -/
theorem reconstruct_success (request : PoolV1PairForestTerminalRequestV1)
    (a : AuthenticatedAsq8Accounts) (candidate : PoolV1PairVerifiedAfterstateV1)
    (out : PoolV1PairForestTerminalStatementV1)
    (h : reconstruct_asq8_statement request a candidate = ok (.Ok out)) :
    U64.checked_add a.live_snapshot.next_pair_index 1#u64 = some candidate.next_pair_index ∧
    a.master.identity.asset_id = requestedAsset request.«public» ∧
    out = statement (common a candidate) request.«public» ∧
    validate_pool_v1_pair_forest_terminal_statement_v1 out = ok (.Ok ()) := by
  unfold reconstruct_asq8_statement at h
  obtain ⟨o, ho, h⟩ := bind_success _ _ _ h
  have ho' : o = U64.checked_add a.live_snapshot.next_pair_index 1#u64 := by
    simpa only [lift, Result.ok.injEq] using ho.symm
  subst o
  obtain ⟨hindex, h⟩ := bool_guard_success _ _ _ _ h
  have hindex' := option_ne_false _ _ hindex
  refine ⟨hindex', ?_⟩
  cases hp : request.«public» with
  | PrivateTransfer p =>
    simp only [hp, bind_tc_ok] at h
    obtain ⟨hasset, h⟩ := bool_guard_success _ _ _ _ h
    have hasset' := m31_ne_false _ _ hasset
    simp only [asq8_common_exact, bind_tc_ok] at h
    obtain ⟨hout, hvalid⟩ := transfer_box_success _ _ _ h
    exact ⟨by simpa only [hp, requestedAsset] using hasset',
      by simpa only [hp, statement] using hout, by simpa only [hout] using hvalid⟩
  | Withdrawal p =>
    simp only [hp, bind_tc_ok] at h
    obtain ⟨hasset, h⟩ := bool_guard_success _ _ _ _ h
    have hasset' := m31_ne_false _ _ hasset
    simp only [asq8_common_exact, bind_tc_ok] at h
    obtain ⟨hout, hvalid⟩ := withdrawal_box_success _ _ _ h
    exact ⟨by simpa only [hp, requestedAsset] using hasset',
      by simpa only [hp, statement] using hout, by simpa only [hout] using hvalid⟩

#print axioms asq8_common_exact
#print axioms transfer_box_success
#print axioms withdrawal_box_success
#print axioms reconstruct_success
end AspisR1AdapterReconstruct.AdapterReconstructSuccess
