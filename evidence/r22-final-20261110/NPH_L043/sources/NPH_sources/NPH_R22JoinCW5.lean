import NPH_R22JoinCW4
import RPz7_S1BorrowedClaimPreparedBoundaryV1
import RPz7_CurrentPreparedInstalledMeaning

/-! NPH_ (R22, CW step 4): the walk of PreparedScratchModel.prepare from its entry to the
claim call.
- `prepare_claim_congr`: for any boundaries B and any claim c', prepare with B.claim replaced
  by c' equals prepare B whenever c' agrees with B.claim at (v.y1, v.inactive, any scratch, any
  kappa returned by a successful row-28 scalar of B.sampling). So every claim call that the
  prepare executes, on both fold branches and on every outcome of the later steps, has these
  arguments. Proof by bind-stepping through the prepare body.
- `deployed_kappa`: on the deployed sampling (installedBoundaries S e, definitionally
  withCandidateSamplers of an installed record: installed_as_candidate_samplers), every
  row-28 scalar output is canonical (scalar_candidate_samplers_false_canonical).
- `originalNew_guarded`: for a view whose retained inactive is canonical, the deployed
  originalNew equals the same transported prepare whose claim boundary runs the borrowed
  claim only when kappa and inactive are canonical (and fails otherwise).
- `guarded_claim_sites`: wherever the guarded claim runs the borrowed claim, the claim is
  owned_claim_loops on concreteOps QRaw with canonical kappa and inactive, so
  NPH_R22JoinCW4.owned_claim_sites gives the exit sum ok with canonical output.
The view producer (inactive canonical from the selected wide view) is composed in
NPH_R22JoinCW6. Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22JoinCW5
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

theorem bind_congr_ok {α β : Type} (m : Result α) (k k' : α → Result β)
    (h : ∀ x, m = ok x → k x = k' x) : (m >>= k) = (m >>= k') := by
  cases m with
  | ok x => simp only [bind_tc_ok]; exact h x rfl
  | fail e => simp only [bind_tc_fail]
  | div => simp only [bind_tc_div]

theorem pair_bind_congr_ok {α β γ : Type} (m : Result (α × β)) (k k' : α → β → Result γ)
    (h : ∀ a b, m = ok (a, b) → k a b = k' a b) :
    (do let (a, b) ← m; k a b) = (do let (a, b) ← m; k' a b) := by
  cases m with
  | ok p => cases p with | mk a b => simp only [bind_tc_ok]; exact h a b rfl
  | fail e => simp only [bind_tc_fail]
  | div => simp only [bind_tc_div]

/-- kappa is returned by a successful row-28 (flag false) scalar of the sampling boundary. -/
def KappaOut (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (kappa : aspis_core.field.WideExact) : Prop :=
  ∃ (before after : transcript.Transcript H) (payload : Slice U8),
    PreparedModel.scalar B.sampling D before 28#u8 payload false = ok (kappa, after)

theorem prepare_claim_congr (B : PreparedScratchModel.Boundaries)
    (c' : {H : Type} → aspis_core.Digest32 H → r1_semantic.Verified H → Slice U8 →
      aspis_core.field.WideExact → Array aspis_core.field.WideExact 29#usize →
      aspis_core.field.WideExact → Result (core.result.Result aspis_core.field.WideExact verifier.Error))
    {H : Type} (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H) (v : verifier.View)
    (hash : H) (g : Array aspis_core.field.WideExact 29#usize)
    (hagree : ∀ (g1 : Array aspis_core.field.WideExact 29#usize) (kappa : aspis_core.field.WideExact),
      KappaOut B D kappa → c' D sem v.y1 v.inactive g1 kappa = B.claim D sem v.y1 v.inactive g1 kappa) :
    PreparedScratchModel.prepare { B with claim := c' } D sem v hash g =
      PreparedScratchModel.prepare B D sem v hash g := by
  unfold PreparedScratchModel.prepare
  try dsimp only
  refine bind_congr_ok _ _ _ (fun a _ => ?_)
  refine bind_congr_ok _ _ _ (fun t _ => ?_)
  refine bind_congr_ok _ _ _ (fun gt _ => ?_)
  obtain ⟨gamma, t1⟩ := gt
  try dsimp only
  refine bind_congr_ok _ _ _ (fun a1 _ => ?_)
  refine bind_congr_ok _ _ _ (fun s _ => ?_)
  refine pair_bind_congr_ok _ _ _ (fun kappa t2 hk => ?_)
  have hK : KappaOut B D kappa := ⟨t1, t2, s, hk⟩
  have hc : ∀ g1, c' D sem v.y1 v.inactive g1 kappa = B.claim D sem v.y1 v.inactive g1 kappa :=
    fun g1 => hagree g1 kappa hK
  have hc2 : ∀ g1, ({ B with claim := c' } : PreparedScratchModel.Boundaries).claim D sem v.y1 v.inactive g1 kappa =
      B.claim D sem v.y1 v.inactive g1 kappa := hc
  simp only [hc, hc2]
  all_goals rfl

open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete

theorem deployed_kappa (S : PreparedModel.Boundaries)
    (e : aspis_core.field.M31 → Result aspis_core.field.WideExact)
    {H : Type} (D : aspis_core.Digest32 H) (kappa : aspis_core.field.WideExact)
    (h : KappaOut (concreteBoundaries (installedBoundaries S e)) D kappa) :
    Canonical (toClaimE kappa) := by
  obtain ⟨before, after, payload, hs⟩ := h
  rw [installed_as_candidate_samplers] at hs
  exact scalar_candidate_samplers_false_canonical _ D before after 28#u8 payload kappa hs

open Classical in
/-- The borrowed claim, run only on canonical kappa and inactive. -/
def guardedClaim : {H : Type} → aspis_core.Digest32 H → r1_semantic.Verified H → Slice U8 →
    aspis_core.field.WideExact → Array aspis_core.field.WideExact 29#usize →
    aspis_core.field.WideExact → Result (core.result.Result aspis_core.field.WideExact verifier.Error) :=
  fun {H} D sem y1 inactive g kappa =>
    if Canonical (toClaimE kappa) ∧ Canonical (toClaimE inactive) then
      AspisR1CurrentCaller.BorrowedClaimPrepared.claim D sem y1 inactive g kappa
    else fail Aeneas.Std.Error.panic

open AspisR1CurrentCaller in
/-- The transported deployed prepare with the guarded claim boundary. -/
def guardedNew (S : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (e : AspisR1PublicPreparation.aspis_core.field.M31 → Result PE)
    {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (v : AspisR1CurrentCaller.verifier.View) (hash : H)
    (g : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize) :
    Result ((core.result.Result AspisR1CurrentCaller.verifier.Prepared AspisR1CurrentCaller.verifier.Error) ×
      (Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize)) :=
  (do
    let (r,scratch) ← AspisR1PublicPreparation.PreparedScratchModel.prepare
      { concreteBoundaries (installedBoundaries S e) with claim := guardedClaim }
      (InstalledPreparation.retainedDigest D) (InstalledPreparation.retainedSem sem)
      (InstalledPreparation.retainedView v) hash (mapArray InstalledPreparation.retainedE g)
    ok ((match r with | .Ok x => .Ok (InstalledPreparation.currentPrepared x)
                      | .Err e => .Err (InstalledPreparation.currentError e)),
        mapArray InstalledPreparation.currentE scratch))

open AspisR1CurrentCaller in
theorem originalNew_guarded (S : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (e : AspisR1PublicPreparation.aspis_core.field.M31 → Result PE)
    {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (v : AspisR1CurrentCaller.verifier.View) (hash : H)
    (g : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize)
    (hin : Canonical (toClaimE (InstalledPreparation.retainedView v).inactive)) :
    BorrowedClaimPrepared.originalNew S e D sem v hash g = guardedNew S e D sem v hash g := by
  rw [BorrowedClaimPrepared.originalNew_eq_transport]
  unfold guardedNew
  rw [prepare_claim_congr (concreteBoundaries (installedBoundaries S e)) guardedClaim
    (InstalledPreparation.retainedDigest D) (InstalledPreparation.retainedSem sem)
    (InstalledPreparation.retainedView v) hash (mapArray InstalledPreparation.retainedE g)
    (fun g1 kappa hK => by
      have hk := deployed_kappa S e _ kappa hK
      dsimp only [guardedClaim]
      rw [if_pos ⟨hk, hin⟩]
      exact BorrowedClaimPrepared.claim_eq _ _ _ _ g1 kappa)]
  all_goals rfl

/-- The borrowed claim body is owned_claim_loops on concreteOps QRaw (definitional). -/
theorem claim_body {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H) (y1 : Slice U8)
    (inactive : PE) (g : Array PE 29#usize) (kappa : PE) :
    AspisR1CurrentCaller.BorrowedClaimPrepared.claim D sem y1 inactive g kappa =
      (do
        let r ← AspisR1CurrentPreparedClaim.verifier.borrowed_abi.owned_claim_loops
          (AspisR1S5ClaimDotConcreteAdapter.concreteOps AspisR1EbyKPushDecodedProductUpdate.QRaw)
          (toClaimSem sem).claims (toClaimSem sem).extra (toClaimSem sem).before_z1 y1 (toClaimE inactive)
          (mapArray toClaimE g) (toClaimE kappa)
        ok (match r with | .Ok x => .Ok (fromClaimE x) | .Err e => .Err (fromClaimError e))) := rfl

/-- Wherever the guarded claim runs the borrowed claim, its arguments are canonical, and the
exit-branch owned_sum of every successful run of the claim loop is ok with canonical output. -/
theorem guarded_claim_sites {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H) (y1 : Slice U8)
    (inactive : PE) (g : Array PE 29#usize) (kappa : PE) :
    (guardedClaim D sem y1 inactive g kappa = fail Aeneas.Std.Error.panic) ∨
    (Canonical (toClaimE kappa) ∧ Canonical (toClaimE inactive) ∧
      guardedClaim D sem y1 inactive g kappa =
        AspisR1CurrentCaller.BorrowedClaimPrepared.claim D sem y1 inactive g kappa ∧
      ∀ (k : Array E 7#usize),
        (AspisR1S5ClaimDotConcreteAdapter.concreteOps AspisR1EbyKPushDecodedProductUpdate.QRaw).powers
          7#usize (toClaimE kappa) = ok k →
      ∀ (parts1 : Array E 7#usize),
        Array.update (Array.repeat 7#usize AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.ZERO) 0#usize (toClaimE inactive) =
          ok parts1 →
      ∀ (parts2 : Array E 7#usize) (pr : Option (core.result.Result E AspisR1CurrentPreparedClaim.verifier.Error)),
        AspisR1CurrentPreparedClaim.verifier.borrowed_abi.owned_claim_loops_loop0
          (AspisR1S5ClaimDotConcreteAdapter.concreteOps AspisR1EbyKPushDecodedProductUpdate.QRaw)
          { start := 0#usize, «end» := 6#usize } (toClaimSem sem).claims (toClaimSem sem).extra
          (toClaimSem sem).before_z1 y1 (mapArray toClaimE g) parts1 = ok (parts2, pr) →
        ∃ out, AspisR1CurrentPreparedClaim.verifier.borrowed_abi.owned_sum k parts2 = ok out ∧ Canonical out) := by
  by_cases hc : Canonical (toClaimE kappa) ∧ Canonical (toClaimE inactive)
  · right
    refine ⟨hc.1, hc.2, ?_, ?_⟩
    · dsimp only [guardedClaim]
      rw [if_pos hc]
    · intro k hk parts1 h1 parts2 pr hloop
      exact AspisR1.NPH_R22JoinCW4.owned_claim_sites AspisR1EbyKPushDecodedProductUpdate.QRaw
        (toClaimSem sem).claims (toClaimSem sem).extra (toClaimSem sem).before_z1 y1 (mapArray toClaimE g)
        (toClaimE inactive) (toClaimE kappa) hc.2 hc.1 k hk parts1 h1 parts2 pr hloop
  · left
    dsimp only [guardedClaim]
    rw [if_neg hc]

#print axioms bind_congr_ok
#print axioms pair_bind_congr_ok
#print axioms prepare_claim_congr
#print axioms deployed_kappa
#print axioms originalNew_guarded
#print axioms claim_body
#print axioms guarded_claim_sites
end AspisR1.NPH_R22JoinCW5
