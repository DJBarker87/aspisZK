import ExtractedAdapterReconstructSuccess

/-! R8 transfer bindings checked by the retained actual Adapter terminal-validator prefix. These link
request fields to the supplied structural account records; they do not establish
owner/PDA authentication, custody, stage1 serialization, or checkpoint provenance.
The full late/tree validation is neither replaced nor assumed to be total. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisR1AdapterReconstruct.TransferBindings
open aspis_statement.pool_v1.pair_forest_terminal
open aspis_statement.pool_v1.payment_relation
open aspis_statement.pool_v1.pair_terminal
open r1_pool_adapter

-- Reuse the backend's symbolic slice-comparison law for these fixed arrays.
local instance {α : Type} [DecidableEq α] {n : Usize} : DecidableEq (Array α n) :=
  inferInstanceAs (DecidableEq { l : List α // l.length = n.val })

private theorem array_eq_value {α : Type} [DecidableEq α] {n : Usize}
    (cmp : core.cmp.PartialEq α α)
    (hne : ∀ x y, cmp.ne x y ⦃ b => b ↔ x ≠ y ⦄)
    (a b : Array α n) :
    core.array.equality.PartialEqArray.eq cmp a b = ok (decide (a = b)) := by
  have hs := core.slice.cmp.PartialEqSlice.eq_homo_spec cmp a.to_slice b.to_slice hne
  change WP.spec (core.array.equality.PartialEqArray.eq cmp a b)
    (fun v => v ↔ a.to_slice = b.to_slice) at hs
  obtain ⟨v, hv, hp⟩ := spec_imp_exists hs
  have he : a.to_slice = b.to_slice ↔ a = b := by
    constructor
    · intro h; apply Subtype.ext; exact congrArg (fun x : Slice α => x.val) h
    · intro h; exact congrArg Array.to_slice h
  have hp : v ↔ a = b := hp.trans he
  have hv' : v = decide (a = b) := by cases v <;> simp_all
  simpa only [hv'] using hv

private theorem array_ne_value {α : Type} [DecidableEq α] {n : Usize}
    (cmp : core.cmp.PartialEq α α)
    (hne : ∀ x y, cmp.ne x y ⦃ b => b ↔ x ≠ y ⦄)
    (a b : Array α n) :
    core.array.equality.PartialEqArray.ne cmp a b = ok (decide (a ≠ b)) := by
  simp only [core.array.equality.PartialEqArray.ne, array_eq_value cmp hne,
    bind_tc_ok]
  congr 1
  simp

private theorem u8_ne_spec (x y : U8) :
    core.cmp.PartialEqU8.ne x y ⦃ b => b ↔ x ≠ y ⦄ := by
  change WP.spec (ok (decide (x ≠ y))) _
  simp only [WP.spec_ok, decide_eq_true_eq]

private theorem m31_ne_spec (x y : aspis_core.field.M31) :
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31.ne x y ⦃ b => b ↔ x ≠ y ⦄ := by
  simp only [core.cmp.PartialEq.ne.default,
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq, bind_tc_ok,
    WP.spec_ok, decide_eq_true_eq]

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

theorem terminal_metadata_bindings
    (c : PoolV1PairForestTerminalCommonV1) (p : PoolV1PrivateTransferPublicV1)
    (h : validate_pool_v1_pair_forest_terminal_statement_v1 (.PrivateTransfer c p) =
      ok (.Ok ())) :
    c.master_account ≠ Array.repeat 32#usize 0#u8 ∧
      c.checkpoint_account ≠ Array.repeat 32#usize 0#u8 ∧
      c.selected_lane_account ≠ Array.repeat 32#usize 0#u8 ∧
      c.output_lane.val < 8 ∧
      p.pool = c.master_account ∧
      p.deployment_domain = c.lane_transition.live_snapshot.deployment_domain ∧
      c.lane_transition.live_snapshot.pool = c.master_account ∧
      p.anchor_sequence = c.checkpoint_sequence ∧
      p.anchor_root = c.historical_global_anchor ∧
      aspis_statement.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1 p.nullifier =
        ok (.Ok c.output_lane) := by
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
      simp only [aspis_statement.pool_v1.pair_forest_accounts.POOL_V1_PAIR_FOREST_LANE_COUNT,
        UScalar.le_equiv, core.convert.num.FromUsizeU8.from_val_eq,
        UScalar.ofNatCore_val_eq] at hlane
      omega
    dsimp only at h
    obtain ⟨r, hpay, h⟩ := bind_success _ _ _ h
    cases r with
    | Err e =>
        obtain ⟨mapped, hmap, h⟩ := bind_success _ _ _ h
        have hmap' : mapped = .Err (PoolV1PairForestTerminalFormatErrorV1.Payment e) := by
          simpa only [core.result.Result.map_err,
            validate_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1,
            validate_pool_v1_pair_forest_terminal_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1.call_once,
            bind_tc_ok, Result.ok.injEq] using hmap.symm
        subst mapped
        obtain ⟨cf, hcf, h⟩ := bind_success _ _ _ h
        have hcf' : cf = .Break (.Err (PoolV1PairForestTerminalFormatErrorV1.Payment e)) := by
          simpa only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] using hcf.symm
        subst cf
        simp only [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from, bind_tc_ok] at h
        cases h
    | Ok pay =>
        obtain ⟨mapped, hmap, h⟩ := bind_success _ _ _ h
        have hmap' : mapped = .Ok pay := by
          simpa only [core.result.Result.map_err, Result.ok.injEq] using hmap.symm
        subst mapped
        obtain ⟨cf, hcf, h⟩ := bind_success _ _ _ h
        have hcf' : cf = .Continue pay := by
          simpa only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] using hcf.symm
        subst cf
        dsimp only at h
        obtain ⟨view, hpublic, h⟩ := bind_success _ _ _ h
        have hp : view = (p.pool, p.deployment_domain, p.anchor_sequence,
            p.anchor_root, p.nullifier, p.asset_id) := by
          simpa only [statement_public_common, Result.ok.injEq] using hpublic.symm
        subst view
        obtain ⟨hpool, h⟩ := bool_guard_success _ _ _ h
        obtain ⟨hdeployment, h⟩ := bool_guard_success _ _ _ h
        obtain ⟨hsnapshot, h⟩ := bool_guard_success _ _ _ h
        split at h
        · cases h
        · rename_i hsequence
          obtain ⟨hanchor, h⟩ := bool_guard_success _ _ _ h
          obtain ⟨r, hlaneEval, h⟩ := bind_success _ _ _ h
          cases r with
          | Err e =>
              obtain ⟨mapped, hmap, h⟩ := bind_success _ _ _ h
              have hmap' : mapped = .Err (PoolV1PairForestTerminalFormatErrorV1.Account e) := by
                simpa only [core.result.Result.map_err,
                  validate_pool_v1_pair_forest_terminal_statement_v1.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1,
                  validate_pool_v1_pair_forest_terminal_statement_v1.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once,
                  bind_tc_ok, Result.ok.injEq] using hmap.symm
              subst mapped
              obtain ⟨cf, hcf, h⟩ := bind_success _ _ _ h
              have hcf' : cf = .Break (.Err (PoolV1PairForestTerminalFormatErrorV1.Account e)) := by
                simpa only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] using hcf.symm
              subst cf
              simp only [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from, bind_tc_ok] at h
              cases h
          | Ok lane =>
              obtain ⟨mapped, hmap, h⟩ := bind_success _ _ _ h
              have hmap' : mapped = .Ok lane := by
                simpa only [core.result.Result.map_err, Result.ok.injEq] using hmap.symm
              subst mapped
              obtain ⟨cf, hcf, h⟩ := bind_success _ _ _ h
              have hcf' : cf = .Continue lane := by
                simpa only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] using hcf.symm
              subst cf
              dsimp only at h
              split at h
              · cases h
              · rename_i hlaneEq
                have hlaneEq : lane = c.output_lane := by simpa only [bne_iff_ne, not_not] using hlaneEq
                rw [hlaneEq] at hlaneEval
                exact ⟨array_eq_false _ u8_ne_spec _ _ hm,
                  array_eq_false _ u8_ne_spec _ _ hc,
                  array_eq_false _ u8_ne_spec _ _ hs, hlane',
                  array_ne_false _ u8_ne_spec _ _ hpool,
                  array_ne_false _ u8_ne_spec _ _ hdeployment,
                  array_ne_false _ u8_ne_spec _ _ hsnapshot,
                  by simpa only [bne_iff_ne, not_not] using hsequence,
                  array_ne_false _ m31_ne_spec _ _ hanchor, hlaneEval⟩

/-- Fixed request/account bindings derived from actual reconstruction success.
No authentication consequence is inferred from the structural input type name. -/
theorem reconstruct_transfer_bindings
    (request : PoolV1PairForestTerminalRequestV1)
    (a : AuthenticatedAsq8Accounts) (candidate : PoolV1PairVerifiedAfterstateV1)
    (out : PoolV1PairForestTerminalStatementV1) (p : PoolV1PrivateTransferPublicV1)
    (hp : request.«public» = .PrivateTransfer p)
    (hr : reconstruct_asq8_statement request a candidate = ok (.Ok out)) :
    U64.checked_add a.live_snapshot.next_pair_index 1#u64 = some candidate.next_pair_index ∧
    a.master.identity.asset_id = p.asset_id ∧
    a.master_account ≠ Array.repeat 32#usize 0#u8 ∧
    a.checkpoint_account ≠ Array.repeat 32#usize 0#u8 ∧
    a.selected_lane_account ≠ Array.repeat 32#usize 0#u8 ∧
    a.selected_lane.lane_id.val < 8 ∧
    p.pool = a.master_account ∧
    p.deployment_domain = a.live_snapshot.deployment_domain ∧
    a.live_snapshot.pool = a.master_account ∧
    p.anchor_sequence = a.checkpoint.checkpoint_sequence ∧
    p.anchor_root = a.checkpoint.global_root ∧
    aspis_statement.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1
      p.nullifier = ok (.Ok a.selected_lane.lane_id) := by
  obtain ⟨hindex, hasset, hout, hv⟩ := AdapterReconstructSuccess.reconstruct_success
    request a candidate out hr
  have hout' : out = .PrivateTransfer (AdapterReconstructSuccess.common a candidate) p := by
    simpa only [hp, AdapterReconstructSuccess.statement] using hout
  rw [hout'] at hv
  refine ⟨hindex, ?_, ?_⟩
  · simpa only [hp, AdapterReconstructSuccess.requestedAsset] using hasset
  · simpa only [AdapterReconstructSuccess.common] using
      terminal_metadata_bindings (AdapterReconstructSuccess.common a candidate) p hv

#print axioms terminal_metadata_bindings
#print axioms reconstruct_transfer_bindings
end AspisR1AdapterReconstruct.TransferBindings
