import ExtractedTerminalEquality

/-! Success inversion for the actual extracted terminal validator. The public
value is identical to the payment encoder's argument. These are the validator's
own checks; no account-owner, PDA, custody, or runtime-reachability claim is made. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1TerminalValidator.TerminalWithdrawalSuccess
open pool_v1.pair_forest_terminal pool_v1.payment_relation
open TerminalEquality

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem bool_guard_success {ε : Type} (m : Result Bool) (e : ε)
    (k : Result (core.result.Result Unit ε))
    (h : (do let b ← m; if b then ok (.Err e) else k) = ok (.Ok ())) :
    m = ok false ∧ k = ok (.Ok ()) := by
  obtain ⟨b, hb, hk⟩ := bind_success _ _ _ h
  cases b with
  | false => exact ⟨hb, by simpa only [Bool.false_eq_true, ↓reduceIte] using hk⟩
  | true => simp only [↓reduceIte] at hk; cases hk

private theorem mapped_try_success {α ε δ O : Type}
    (m : Result (core.result.Result α ε)) (f : core.ops.function.FnOnce O ε δ)
    (op : O) (k : α → Result (core.result.Result Unit δ))
    (h : (do
      let r ← m
      let r1 ← core.result.Result.map_err f r op
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf with
      | .Continue v => k v
      | .Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame δ) residual) = ok (.Ok ())) :
    ∃ v, m = ok (.Ok v) ∧ k v = ok (.Ok ()) := by
  obtain ⟨r, hr, hk⟩ := bind_success _ _ _ h
  cases r with
  | Ok v =>
      exact ⟨v, hr, by simpa only [core.result.Result.map_err, bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry.branch] using hk⟩
  | Err e =>
      cases hf : f.call_once op e <;>
        simp only [core.result.Result.map_err, hf, bind_tc_ok, bind_tc_fail, bind_tc_div,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at hk <;> cases hk

private theorem array_eq_false {α : Type} [DecidableEq α] {n : Usize}
    (cmp : core.cmp.PartialEq α α)
    (hne : ∀ x y, cmp.ne x y ⦃ b => b ↔ x ≠ y ⦄) (a b : Array α n)
    (h : core.array.equality.PartialEqArray.eq cmp a b = ok false) : a ≠ b := by
  rw [array_eq_value cmp hne] at h
  simpa only [Result.ok.injEq, decide_eq_false_iff_not] using h

private theorem array_ne_false {α : Type} [DecidableEq α] {n : Usize}
    (cmp : core.cmp.PartialEq α α)
    (hne : ∀ x y, cmp.ne x y ⦃ b => b ↔ x ≠ y ⦄) (a b : Array α n)
    (h : core.array.equality.PartialEqArray.ne cmp a b = ok false) : a = b := by
  rw [array_ne_value cmp hne] at h
  simpa only [Result.ok.injEq, decide_eq_false_iff_not, not_not] using h

/-- All direct guards, and the actual nested encoder successes, follow from
successful execution. No parser, chosen projection, or nested-success premise. -/
theorem terminal_withdrawal_success
    (c : PoolV1PairForestTerminalCommonV1) (p : PoolV1WithdrawalPublicV1)
    (h : validate_pool_v1_pair_forest_terminal_statement_v1 (.Withdrawal c p) =
      ok (.Ok ())) :
    ∃ pay : Array U8 216#usize, ∃ late : Slice U8,
      encode_pool_v1_withdrawal_public_v1 p = ok (.Ok pay) ∧
      c.master_account ≠ Array.repeat 32#usize 0#u8 ∧
      c.checkpoint_account ≠ Array.repeat 32#usize 0#u8 ∧
      c.selected_lane_account ≠ Array.repeat 32#usize 0#u8 ∧
      c.output_lane.val < 8 ∧
      p.pool = c.master_account ∧
      p.deployment_domain = c.lane_transition.live_snapshot.deployment_domain ∧
      c.lane_transition.live_snapshot.pool = c.master_account ∧
      p.anchor_sequence = c.checkpoint_sequence ∧
      p.anchor_root = c.historical_global_anchor ∧
      pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 p.nullifier =
        ok (.Ok c.output_lane) ∧
      pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1
        c.lane_transition (Array.to_slice (Array.repeat 1520#usize 0#u8)) =
        ok (.Ok (), late) := by
  unfold validate_pool_v1_pair_forest_terminal_statement_v1 at h
  obtain ⟨common, hcommon, h⟩ := bind_success _ _ _ h
  have hc : common = c := by
    simpa only [PoolV1PairForestTerminalStatementV1.common, Result.ok.injEq] using hcommon.symm
  subst common
  obtain ⟨hm, h⟩ := bool_guard_success _ _ _ h
  obtain ⟨hc, h⟩ := bool_guard_success _ _ _ h
  obtain ⟨hs, h⟩ := bool_guard_success _ _ _ h
  obtain ⟨i, hi, h⟩ := bind_success _ _ _ h
  have hi' : i = core.convert.num.FromUsizeU8.from c.output_lane := by
    simpa only [lift, Result.ok.injEq] using hi.symm
  subst i
  split at h
  · cases h
  · rename_i hlane
    have hlane' : c.output_lane.val < 8 := by
      simp only [pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT,
        UScalar.le_equiv, core.convert.num.FromUsizeU8.from_val_eq,
        UScalar.ofNatCore_val_eq] at hlane
      omega
    obtain ⟨pay, hpay, h⟩ := mapped_try_success _ _ _ _ h
    obtain ⟨public, hpublic, h⟩ := bind_success _ _ _ h
    have hp : public = (p.pool, p.deployment_domain, p.anchor_sequence,
        p.anchor_root, p.nullifier, p.asset_id) := by
      simpa only [statement_public_common, Result.ok.injEq] using hpublic.symm
    subst public
    obtain ⟨hpool, h⟩ := bool_guard_success _ _ _ h
    obtain ⟨hdeployment, h⟩ := bool_guard_success _ _ _ h
    obtain ⟨hsnapshot, h⟩ := bool_guard_success _ _ _ h
    split at h
    · cases h
    · rename_i hsequence
      obtain ⟨hanchor, h⟩ := bool_guard_success _ _ _ h
      obtain ⟨lane, hlaneEval, h⟩ := mapped_try_success _ _ _ _ h
      split at h
      · cases h
      · rename_i hlaneEq
        have hlaneEq : lane = c.output_lane := by simpa only [bne_iff_ne, not_not] using hlaneEq
        subst lane
        obtain ⟨s, hslice, h⟩ := bind_success _ _ _ h
        have hslice' : s = Array.to_slice_mut (Array.repeat 1520#usize 0#u8) := by
          simpa only [lift, Result.ok.injEq] using hslice.symm
        subst s
        obtain ⟨⟨r, late⟩, hlate, h⟩ := bind_success _ _ _ h
        obtain ⟨u, hu, _⟩ := mapped_try_success (ok r) _ _ _ h
        cases u
        have hr : r = core.result.Result.Ok () := by simpa only [Result.ok.injEq] using hu
        subst r
        exact ⟨pay, late, hpay,
          array_eq_false _ u8_ne_spec _ _ hm,
          array_eq_false _ u8_ne_spec _ _ hc,
          array_eq_false _ u8_ne_spec _ _ hs, hlane',
          array_ne_false _ u8_ne_spec _ _ hpool,
          array_ne_false _ u8_ne_spec _ _ hdeployment,
          array_ne_false _ u8_ne_spec _ _ hsnapshot,
          by simpa only [bne_iff_ne, not_not] using hsequence,
          array_ne_false _ m31_ne_spec _ _ hanchor, hlaneEval, hlate⟩

#print axioms terminal_withdrawal_success
end AspisR1TerminalValidator.TerminalWithdrawalSuccess
