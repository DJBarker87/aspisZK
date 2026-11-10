import NPH_R22JoinCW2
import CurrentClaimPartsUpdates
import CurrentClaimHelperCanonical
import CurrentClaimSumTotal
import CurrentClaimPowersInstance
import NHI_RangeProgress

/-! NPH_ (R22, run of 2026-11-10 night, CW step 2).
- `concrete_tail_sites`: if the un-installed NJJ_QueryOps.concrete tail slots
  (op3 = SAQ_MixedSource.mulE, op2 = SAQ_Arithmetic.add, op9 = SAQ_Arithmetic.mulK) are
  executed at a state satisfying the query invariant NFS_QueryInvariant.Domain, every CW
  kernel call inside them receives W arguments. (On the deployed paths these slots are
  replaced by NFS_QueryOps.installed, NPH_R22Join094.Dcon_tail; this lemma covers the
  record as installed by NJJ_QueryOps.concrete, LIBC_QueryOps.seed and SAQ_Arithmetic.install
  in case any reached execution runs it un-installed.)
- The CurrentPreparedClaim claim loop (CurrentClaimDotModel prepared_claim): the 7-entry
  parts array stays canonical along every successful iteration (`claim_body_preserves`),
  starting from `update (repeat ZERO) 0 inactive` (`claim_initial`); the coefficient array is
  canonical from the concrete powers instance on a canonical kappa (`claim_powers`). At the
  exit branch the sum loop prepared_claim_sum is ok with canonical output
  (`claim_sum_site`, through CurrentClaimSumTotal.prepared_claim_sum_total_exact), so each
  CW mul/add inside it receives canonical arguments. Producer hypotheses kept explicit:
  canonical kappa and inactive, and the ClaimDotOps finishDot producer
  (every successful finishDot output canonical).
Standard axioms; nothing merged is changed. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22JoinCW3
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1.NPH_R22Producers AspisR1.NPH_R22Callbacks

theorem pcanon_WK (q : SAQ_WideABI.K) (h : NBF_PowerStep.Canonical q) : WK q := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp only [S7Kani2OwnedRowRefinement.powerLimb, Port3_RowsInstall.toK] at h0 h1 h2 h3
  simp (config := {decide := true}) only [ite_true, ite_false] at h0 h1 h2 h3
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    first
    | (show _ ≤ 2147483647; omega)
    | (simp only [SAQ_WideABI.toQ]; omega)
    | (simp_all [SAQ_WideABI.toQ]; omega)

theorem wideCanon_W (x : SAQ_WideABI.E) (h : NBO_TailDomain.WideCanonical x) : WE x :=
  ⟨pcanon_WK x.c0 h.1, pcanon_WK x.c1 h.2⟩

theorem concrete_tail_sites {p : verifier.Prepared} {s f : Nat} {a : verifier.Accumulator}
    {b : verifier.BatchedWeights} (d : AspisR1.NFS_QueryInvariant.Domain p s f a b)
    (value : SAQ_WideABI.E) (hv : WE value) :
    ∃ we we1 q', NJJ_QueryOps.concrete.op3 value a.power = ok we ∧ WE we ∧
      NJJ_QueryOps.concrete.op2 a.rhs we = ok we1 ∧ WE we1 ∧
      NJJ_QueryOps.concrete.op9 a.power p.rho = ok q' ∧ WK q' := by
  obtain ⟨we, h3, w3⟩ := SAQ_MixedSource_mulE_W value a.power hv
  obtain ⟨we1, h2, w2⟩ := SAQ_Arithmetic_add_W a.rhs we (wideCanon_W _ d.rhs) w3
  obtain ⟨q', h9, w9⟩ := SAQ_Arithmetic_mulK_W a.power p.rho (pcanon_WK _ d.power) (pcanon_WK _ d.rho)
  exact ⟨we, we1, q', h3, w3, h2, w2, h9, w9⟩

/-! ### CurrentPreparedClaim claim loop -/

open AspisR1CurrentPreparedClaim AspisR1CurrentPreparedClaim.Concrete

abbrev CanonArr (x : Array E 7#usize) : Prop := ∀ j (h : j.val < 7), Canonical (cell x j h)

theorem claim_sum_site (k parts : Array E 7#usize) (hk : CanonArr k) (hp : CanonArr parts) :
    ∃ out, verifier.prepared_claim_sum k parts = ok out ∧ Canonical out := by
  obtain ⟨out, ho, hc, _⟩ := prepared_claim_sum_total_exact k parts hk hp
  exact ⟨out, ho, hc⟩

theorem claim_body_preserves {D H : Type} (ops : ClaimDotOps D) (inst : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (y1 : Slice U8) (g : Array E 29#usize) (k : Array E 7#usize)
    (iter : core.ops.range.Range Usize) (parts : Array E 7#usize)
    (hfinish : ∀ s v, ops.finishDot s = ok v → Canonical v)
    (hend : iter.end.val ≤ 6) (hp : CanonArr parts)
    (iter1 : core.ops.range.Range Usize) (parts1 : Array E 7#usize)
    (run : verifier.prepared_claim_loop.body ops inst sem y1 g k iter parts = ok (.cont (iter1, parts1))) :
    iter1.end = iter.end ∧ CanonArr parts1 := by
  unfold verifier.prepared_claim_loop.body at run
  obtain ⟨⟨o, it⟩, hnext, run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none =>
    obtain ⟨we, _, run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases Result.ok.inj run
  | some point =>
    obtain ⟨hpt, hitend, _, hlt⟩ := NHI_RangeProgress.some_next iter it point hnext
    obtain ⟨r, hr, run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨cf, hcf, run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases r with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch] at hcf
      cases Result.ok.inj hcf
      obtain ⟨r1, _, run⟩ := Port3_PushFrame.bind_success _ _ _ run
      cases Result.ok.inj run
    | Ok val =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch] at hcf
      cases Result.ok.inj hcf
      obtain ⟨i, hi, run⟩ := Port3_PushFrame.bind_success _ _ _ run
      obtain ⟨a, ha, run⟩ := Port3_PushFrame.bind_success _ _ _ run
      have e := Result.ok.inj run
      simp only [ControlFlow.cont.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      have hv := ClaimScalar.helper_return_canonical ops inst sem y1 g point val hfinish hr
      have p6 : point.val < 6 := by subst hpt; omega
      have hiv := ClaimParts.add_one_success_val point i p6 hi
      have hil : i.val < 7 := by omega
      refine ⟨hitend, fun j hj => ?_⟩
      rw [ClaimParts.update_cells parts a i val hil ha j hj]
      split
      · exact hv
      · exact hp j hj

theorem claim_initial (inactive : E) (hc : Canonical inactive) (a : Array E 7#usize)
    (ha : Array.update (Array.repeat 7#usize aspis_core.field.WideExact.ZERO) 0#usize inactive = ok a) :
    CanonArr a := by
  intro j hj
  rw [ClaimParts.update_cells _ a 0#usize inactive (by decide) ha j hj]
  split
  · exact hc
  · have z : cell (Array.repeat 7#usize aspis_core.field.WideExact.ZERO) j hj =
        aspis_core.field.WideExact.ZERO := by
      first
      | simp only [cell, Array.repeat, List.getElem_replicate]
      | (simp [cell, Array.repeat]; generalize j.val = n at hj ⊢; interval_cases n <;> rfl)
    rw [z]; exact zero_canonical

theorem claim_powers (kappa : E) (hk : Canonical kappa) (k : Array E 7#usize)
    (run : ClaimPowers.powers 7#usize kappa = ok k) : CanonArr k := by
  obtain ⟨out, ho, hp⟩ := ClaimPowers.powers_total_exact 7#usize kappa hk
  have same : out = k := Result.ok.inj (ho.symm.trans run)
  subst same
  intro j hj
  exact (hp ⟨j.val, by simpa using hj⟩).1

/-- Reached states of the claim loop: from the initial parts by successful iterations. -/
inductive ClaimReach {D H : Type} (ops : ClaimDotOps D) (inst : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (y1 : Slice U8) (g : Array E 29#usize) (k : Array E 7#usize)
    (iter0 : core.ops.range.Range Usize) (parts0 : Array E 7#usize) :
    core.ops.range.Range Usize → Array E 7#usize → Prop where
  | init : ClaimReach ops inst sem y1 g k iter0 parts0 iter0 parts0
  | step {iter parts iter1 parts1} : ClaimReach ops inst sem y1 g k iter0 parts0 iter parts →
      verifier.prepared_claim_loop.body ops inst sem y1 g k iter parts = ok (.cont (iter1, parts1)) →
      ClaimReach ops inst sem y1 g k iter0 parts0 iter1 parts1

theorem claim_reach_canon {D H : Type} {ops : ClaimDotOps D} {inst : aspis_core.Digest32 H}
    {sem : r1_semantic.Verified H} {y1 : Slice U8} {g : Array E 29#usize} {k : Array E 7#usize}
    {iter0 : core.ops.range.Range Usize} {parts0 : Array E 7#usize}
    (hfinish : ∀ s v, ops.finishDot s = ok v → Canonical v)
    (hend : iter0.end.val ≤ 6) (h0 : CanonArr parts0)
    {iter : core.ops.range.Range Usize} {parts : Array E 7#usize}
    (reach : ClaimReach ops inst sem y1 g k iter0 parts0 iter parts) :
    iter.end = iter0.end ∧ CanonArr parts := by
  induction reach with
  | init => exact ⟨rfl, h0⟩
  | step _ run ih =>
    obtain ⟨e, c⟩ := ih
    obtain ⟨e1, c1⟩ := claim_body_preserves ops inst sem y1 g k _ _ hfinish (by rw [e]; exact hend) c _ _ run
    exact ⟨e1.trans e, c1⟩

/-- The composed claim site on the concrete-powers instance: at every reached state of
prepared_claim (withConcretePowers ops) on a canonical kappa and inactive, the sum loop that
the exit branch calls is ok with canonical output (so its CW mul/add calls receive
canonical arguments). -/
theorem claim_sites {D H : Type} (ops : ClaimDotOps D) (inst : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (y1 : Slice U8) (g : Array E 29#usize)
    (inactive kappa : E) (hi : Canonical inactive) (hkappa : Canonical kappa)
    (hfinish : ∀ s v, ops.finishDot s = ok v → Canonical v)
    (k : Array E 7#usize) (hkrun : (ClaimPowers.withConcretePowers ops).powers 7#usize kappa = ok k)
    (a : Array E 7#usize)
    (ha : Array.update (Array.repeat 7#usize aspis_core.field.WideExact.ZERO) 0#usize inactive = ok a)
    {iter : core.ops.range.Range Usize} {parts : Array E 7#usize}
    (reach : ClaimReach (ClaimPowers.withConcretePowers ops) inst sem y1 g k
      { start := 0#usize, «end» := 6#usize } a iter parts) :
    ∃ out, verifier.prepared_claim_sum k parts = ok out ∧ Canonical out := by
  have hk := claim_powers kappa hkappa k hkrun
  obtain ⟨_, hp⟩ := claim_reach_canon (ops := ClaimPowers.withConcretePowers ops) hfinish
    (by decide) (claim_initial inactive hi a ha) reach
  exact claim_sum_site k parts hk hp

#print axioms pcanon_WK
#print axioms wideCanon_W
#print axioms concrete_tail_sites
#print axioms claim_sum_site
#print axioms claim_body_preserves
#print axioms claim_initial
#print axioms claim_powers
#print axioms claim_reach_canon
#print axioms claim_sites
end AspisR1.NPH_R22JoinCW3
