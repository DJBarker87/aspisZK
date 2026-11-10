import NPH_R22JoinCW3
import S1ClaimBorrowedAbiTransportV1
import S1ClaimOwnedNestedTransferV1
import ClaimDotConcreteAdapterV1

/-! NPH_ (R22, run of 2026-11-10 night, CW step 3): the borrowed-ABI owned claim loop
(S1ClaimBorrowedAbiNativeV1 owned_claim_loops), whose exit calls borrowed_abi.owned_sum.
- `sums_eq`: borrowed_abi.owned_sum, owned_sum and prepared_claim_sum are the same function
  (rfl, S1ClaimBorrowedAbiTransportV1.sum_eq and S1ClaimOwnedNestedTransferV1), so
  NPH_R22JoinCW3.claim_sum_site serves all three sum loops.
- `owned_body_cont`/`owned_body_done`: one outer iteration writes parts[point+1] := finishDot
  output and keeps every other cell; a done exit returns the current parts unchanged.
- `owned_loop_canon`: every successful run of owned_claim_loops_loop0 from canonical parts
  returns canonical parts (fuel induction on iter.end - iter.start through loop.eq_def).
- `concrete_finish`: the concrete ClaimDotOps (AspisR1S5ClaimDotConcreteAdapter.concreteOps)
  finishDot output is canonical for every state (FinishDotSourceABI.finishFromPush_total).
- `owned_claim_sites`: in owned_claim_loops on concreteOps, from a canonical kappa and
  inactive, the exit-branch owned_sum is ok with canonical output.
The kappa and inactive canonicality stay explicit hypotheses (their producers are the tx1
prepare sampler and inactive decoder, not composed here). Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22JoinCW4
open Aeneas Aeneas.Std Result
open AspisR1CurrentPreparedClaim AspisR1CurrentPreparedClaim.Concrete AspisR1.NPH_R22JoinCW3

theorem sums_eq (k parts : Array E 7#usize) :
    verifier.borrowed_abi.owned_sum k parts = verifier.prepared_claim_sum k parts := rfl

theorem owned_body_cont {D : Type} (ops : ClaimDotOps D)
    (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (extra before_z1 : Array aspis_core.field.QM31 29#usize) (y1 : Slice U8)
    (g : Array E 29#usize) (iter : core.ops.range.Range Usize) (parts : Array E 7#usize)
    (hfinish : ∀ s v, ops.finishDot s = ok v → Canonical v)
    (hend : iter.end.val ≤ 6) (hp : CanonArr parts)
    (iter1 : core.ops.range.Range Usize) (parts1 : Array E 7#usize)
    (run : verifier.borrowed_abi.owned_claim_loops_loop0.body ops claims extra before_z1 y1 g iter parts =
      ok (.cont (iter1, parts1))) :
    iter1.end = iter.end ∧ iter1.start.val = iter.start.val + 1 ∧ iter.start.val < iter.end.val ∧
      CanonArr parts1 := by
  unfold verifier.borrowed_abi.owned_claim_loops_loop0.body at run
  obtain ⟨⟨o, it⟩, hnext, run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none => cases Result.ok.inj run
  | some point =>
    obtain ⟨hpt, hitend, hstart, hlt⟩ := NHI_RangeProgress.some_next iter it point hnext
    obtain ⟨dot, _, run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨⟨dot1, pending⟩, _, run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases pending with
    | some r => cases Result.ok.inj run
    | none =>
      obtain ⟨we, hwe, run⟩ := Port3_PushFrame.bind_success _ _ _ run
      obtain ⟨i, hi, run⟩ := Port3_PushFrame.bind_success _ _ _ run
      obtain ⟨a, ha, run⟩ := Port3_PushFrame.bind_success _ _ _ run
      have e := Result.ok.inj run
      simp only [ControlFlow.cont.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      have hv := hfinish dot1 we hwe
      have p6 : point.val < 6 := by subst hpt; omega
      have hiv := ClaimParts.add_one_success_val point i p6 hi
      have hil : i.val < 7 := by omega
      refine ⟨hitend, hstart, hlt, fun j hj => ?_⟩
      rw [ClaimParts.update_cells parts a i we hil ha j hj]
      split
      · exact hv
      · exact hp j hj

theorem owned_body_done {D : Type} (ops : ClaimDotOps D)
    (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (extra before_z1 : Array aspis_core.field.QM31 29#usize) (y1 : Slice U8)
    (g : Array E 29#usize) (iter : core.ops.range.Range Usize) (parts : Array E 7#usize)
    (y : Array E 7#usize × Option (core.result.Result E verifier.Error))
    (run : verifier.borrowed_abi.owned_claim_loops_loop0.body ops claims extra before_z1 y1 g iter parts =
      ok (.done y)) : y.1 = parts := by
  unfold verifier.borrowed_abi.owned_claim_loops_loop0.body at run
  obtain ⟨⟨o, it⟩, _, run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none =>
    have e := Result.ok.inj run
    simp only [ControlFlow.done.injEq] at e
    rw [← e]
  | some point =>
    obtain ⟨dot, _, run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨⟨dot1, pending⟩, _, run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases pending with
    | some r =>
      have e := Result.ok.inj run
      simp only [ControlFlow.done.injEq] at e
      rw [← e]
    | none =>
      obtain ⟨we, _, run⟩ := Port3_PushFrame.bind_success _ _ _ run
      obtain ⟨i, _, run⟩ := Port3_PushFrame.bind_success _ _ _ run
      obtain ⟨a, _, run⟩ := Port3_PushFrame.bind_success _ _ _ run
      cases Result.ok.inj run

theorem owned_loop_canon {D : Type} (ops : ClaimDotOps D)
    (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (extra before_z1 : Array aspis_core.field.QM31 29#usize) (y1 : Slice U8)
    (g : Array E 29#usize) (hfinish : ∀ s v, ops.finishDot s = ok v → Canonical v) :
    ∀ (n : Nat) (iter : core.ops.range.Range Usize) (parts : Array E 7#usize),
      iter.end.val ≤ 6 → iter.end.val - iter.start.val ≤ n → CanonArr parts →
      ∀ parts2 pr, verifier.borrowed_abi.owned_claim_loops_loop0 ops iter claims extra before_z1 y1 g parts =
        ok (parts2, pr) → CanonArr parts2 := by
  intro n
  induction n with
  | zero =>
    intro iter parts hend hn hp parts2 pr run
    unfold verifier.borrowed_abi.owned_claim_loops_loop0 at run
    rw [Aeneas.Std.loop.eq_def] at run
    dsimp only at run
    cases hb : verifier.borrowed_abi.owned_claim_loops_loop0.body ops claims extra before_z1 y1 g iter parts with
    | fail e => simp only [hb] at run; cases run
    | div => simp only [hb] at run; cases run
    | ok cf =>
      cases cf with
      | done y =>
        simp only [hb] at run
        have e : y = (parts2, pr) := by first | exact Result.ok.inj run | exact run
        have hy := owned_body_done ops claims extra before_z1 y1 g iter parts y hb
        rw [e] at hy
        rw [show parts2 = parts from hy]; exact hp
      | cont x =>
        obtain ⟨i1, p1⟩ := x
        obtain ⟨_, _, hlt, _⟩ := owned_body_cont ops claims extra before_z1 y1 g iter parts hfinish hend hp
          i1 p1 hb
        omega
  | succ n ih =>
    intro iter parts hend hn hp parts2 pr run
    unfold verifier.borrowed_abi.owned_claim_loops_loop0 at run
    rw [Aeneas.Std.loop.eq_def] at run
    dsimp only at run
    cases hb : verifier.borrowed_abi.owned_claim_loops_loop0.body ops claims extra before_z1 y1 g iter parts with
    | fail e => simp only [hb] at run; cases run
    | div => simp only [hb] at run; cases run
    | ok cf =>
      cases cf with
      | done y =>
        simp only [hb] at run
        have e : y = (parts2, pr) := by first | exact Result.ok.inj run | exact run
        have hy := owned_body_done ops claims extra before_z1 y1 g iter parts y hb
        rw [e] at hy
        rw [show parts2 = parts from hy]; exact hp
      | cont x =>
        obtain ⟨i1, p1⟩ := x
        obtain ⟨he, hs, hlt, hc⟩ := owned_body_cont ops claims extra before_z1 y1 g iter parts hfinish hend hp
          i1 p1 hb
        simp only [hb] at run
        apply ih i1 p1 (by rw [he]; exact hend) (by rw [he, hs]; omega) hc parts2 pr
        unfold verifier.borrowed_abi.owned_claim_loops_loop0
        exact run

theorem concrete_finish (rawFn : AspisR1EbyKPushDotBackend.RawFn) :
    ∀ s v, (AspisR1S5ClaimDotConcreteAdapter.concreteOps rawFn).finishDot s = ok v → Canonical v := by
  intro s v h
  obtain ⟨out, ho, hc, _⟩ := AspisR1FinishDotSourceABI.finishFromPush_total s
  simp only [AspisR1S5ClaimDotConcreteAdapter.concreteOps, ho, bind_tc_ok] at h
  cases Result.ok.inj h
  exact hc

/-- The exit-branch sum of the borrowed owned claim on the concrete ClaimDotOps. -/
theorem owned_claim_sites (rawFn : AspisR1EbyKPushDotBackend.RawFn)
    (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (extra before_z1 : Array aspis_core.field.QM31 29#usize) (y1 : Slice U8)
    (g : Array E 29#usize) (inactive kappa : E) (hi : Canonical inactive) (hkappa : Canonical kappa)
    (k : Array E 7#usize)
    (hkrun : (AspisR1S5ClaimDotConcreteAdapter.concreteOps rawFn).powers 7#usize kappa = ok k)
    (parts1 : Array E 7#usize)
    (h1 : Array.update (Array.repeat 7#usize aspis_core.field.WideExact.ZERO) 0#usize inactive = ok parts1)
    (parts2 : Array E 7#usize) (pr : Option (core.result.Result E verifier.Error))
    (hloop : verifier.borrowed_abi.owned_claim_loops_loop0 (AspisR1S5ClaimDotConcreteAdapter.concreteOps rawFn)
      { start := 0#usize, «end» := 6#usize } claims extra before_z1 y1 g parts1 = ok (parts2, pr)) :
    ∃ out, verifier.borrowed_abi.owned_sum k parts2 = ok out ∧ Canonical out := by
  have hk := claim_powers kappa hkappa k hkrun
  have hp := owned_loop_canon (AspisR1S5ClaimDotConcreteAdapter.concreteOps rawFn) claims extra before_z1 y1 g
    (concrete_finish rawFn) 6 _ parts1 (by decide) (by decide) (claim_initial inactive hi parts1 h1) parts2 pr hloop
  rw [sums_eq]
  exact claim_sum_site k parts2 hk hp

#print axioms sums_eq
#print axioms owned_body_cont
#print axioms owned_body_done
#print axioms owned_loop_canon
#print axioms concrete_finish
#print axioms owned_claim_sites
end AspisR1.NPH_R22JoinCW4
