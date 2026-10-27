import RPz7_S1BorrowedClaimPreparedBoundaryV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
namespace AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge
open AspisR1ClaimPreparedBridge.InstalledMeaning AspisR1CurrentPreparedClaim.Concrete

def install (ops : Ops) (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 → Result PE) : Ops :=
  {ConcreteConstants.withConstants ops with op5:=sourceView,op8:=originalNew sampling embed}

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let a ← m;f a)=ok out) : ∃ a,m=ok a ∧ f a=ok out := by
  cases m with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h;cases h
  | div => simp only [bind_tc_div] at h;cases h

/-- Same enclosing first execution, original Prepared.new body, borrowed claim
reference and actual early-return powers. Canonicality, payload and joint trace
are conclusions. The original native claim/source and SDK binding stay open. -/
theorem first_borrowed_reference_claim_and_rank {E M Cv : Type} {L : Nat}
    (invalidAccountData : E) (ops : Ops)
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 → Result PE)
    (D : aspis_core.digest.Digest32 Unit) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice U8) (root : Array U8 32#usize) (length : U32)
    (error : verifier.Error → Result E) (bytes proof : Slice U8) (k : Usize)
    (out : alloc.vec.Vec U8)
    (h : FirstComposition.firstCurrent invalidAccountData (install ops sampling embed)
      D error bytes proof k=ok (.Ok out)) :
    ∃ (s : AspisR1PublicPreparation.FirstCaller.DecoderStatement),
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual bytes=ok (.Ok s) ∧
      k=compact.SPLIT ∧ ∃ (zero : aspis_core.field.wide_exact.WideExact)
        (semantic y1 : Slice U8) (v : AspisR1SelectedWideViewV1.verifier.View)
        (sem : r1_semantic.Verified Unit) (prepared : AspisR1PublicPreparation.verifier.Prepared)
        (scratch : Array PE 29#usize),
        AspisR1SelectedWideViewV1.verifier.candidate.wide_view proof semantic y1=ok (.Ok v) ∧
        ops.op9 D (FirstComposition.toCurrentPublic
          (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)) v.semantic () none=ok (.Ok sem) ∧
        (Canonical (toClaimE prepared.gamma) ∧ Canonical (toClaimE prepared.kappa)) ∧
        OriginalPayloadClaimMeaning (retainedSem sem) v.y1
          (toClaimE (AspisR1SelectedWideViewV1.prepCarrier v.inactive))
          (toClaimE prepared.gamma) (toClaimE prepared.kappa) (toClaimE prepared.claim)
          (mapArray toClaimE scratch) ∧
        (∀ i : Usize, i.val<29 → ∃ value : AspisR1CurrentPreparedClaim.Concrete.E,
          Array.index_usize (mapArray toClaimE scratch) i=ok value ∧
          Canonical value ∧ decode value=decode (toClaimE prepared.gamma)^i.val) ∧
        JointRankTrace sampling embed (retainedDigest D) p pubInput root length
          (retainedSem sem) (AspisR1SelectedWideViewV1.preparedView v) () prepared scratch ∧
        Tx1Reachability.afterPrepare (install ops sampling embed) D bytes proof k () none
          (currentPrepared prepared) (mapArray currentE scratch)=ok (.Ok out) := by
  obtain ⟨s,hd,hk,zero,prepared,scratch,semantic,y1,v,sem,hview,hsem,hnew,htail⟩ :=
    FirstComposition.first_current_prepared_new invalidAccountData (install ops sampling embed)
      D error bytes proof k out h
  change sourceView proof semantic y1=ok (.Ok v) at hview
  unfold sourceView at hview
  obtain ⟨r,hr,hview⟩ := bind_success _ _ _ hview
  cases r with
  | Err e => cases hview
  | Ok oldv =>
    have hv : selectedView oldv=v := core.result.Result.Ok.inj (Result.ok.inj hview)
    subst v
    change originalNew sampling embed D sem (selectedView oldv) ()
      (Array.repeat 29#usize zero)=ok (.Ok prepared,scratch) at hnew
    rw [originalNew_eq_transport] at hnew
    obtain ⟨pair,hbackend,hnew⟩ := bind_success _ _ _ hnew
    rcases pair with ⟨r,oldScratch⟩
    cases r with
    | Err e => cases hnew
    | Ok oldPrepared =>
      have heq : (core.result.Result.Ok (currentPrepared oldPrepared),mapArray currentE oldScratch)=
          (core.result.Result.Ok prepared,scratch) := Result.ok.inj hnew
      have hp : currentPrepared oldPrepared=prepared := core.result.Result.Ok.inj (congrArg Prod.fst heq)
      have hg : mapArray currentE oldScratch=scratch := congrArg Prod.snd heq
      subst prepared
      subst scratch
      rw [retained_selected_view] at hbackend
      have hinactive := AspisR1SelectedWideViewV1.wide_view_inactive_canonical proof semantic y1 oldv hr
      obtain ⟨hcan,halpha,hclaim,hpowers⟩ := prepared_installed_meaning
        sampling embed (retainedDigest D) (retainedSem sem)
        (AspisR1SelectedWideViewV1.preparedView oldv) () oldPrepared oldScratch
        (mapArray retainedE (Array.repeat 29#usize zero)) hinactive hbackend
      have hrank := prepared_installed_joint_rank_trace sampling embed (retainedDigest D)
        p pubInput root length (retainedSem sem) (AspisR1SelectedWideViewV1.preparedView oldv)
        () oldPrepared oldScratch (mapArray retainedE (Array.repeat 29#usize zero)) hbackend
      exact ⟨s,hd,hk,zero,semantic,y1,oldv,sem,oldPrepared,oldScratch,
        hr,hsem,hcan,hclaim,hpowers,hrank,htail⟩

#print axioms first_borrowed_reference_claim_and_rank
end AspisR1CurrentCaller.BorrowedClaimPrepared
