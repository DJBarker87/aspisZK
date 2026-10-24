import S1NativeBufferClaimTraceV1
import S1RankTraceQueryProgramV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
namespace AspisS1NativeBufferClaimTrace
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete OriginalSerializerInstallation
open AspisS1ValuesOwnedInstallation

private theorem bind_success {A B : Type} (r : Result A) (k : A → Result B) (out : B)
    (h : (r >>= k) = ok out) : ∃ a, r = ok a ∧ k a = ok out := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => cases h
  | div => cases h

/-- Accepted concrete first supplies the actual Prepared.new/model call, same
scratch/claim, full joint trace and actual S2 row31/32 program branch. No
separate canonicality, variant, model-call or sampler success is assumed. -/
theorem first_native_buffers_prepared_trace {E M Cv : Type} {L : Nat}
    (invalidAccountData : E) (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (D : aspis_core.digest.Digest32 Unit) (p : FS2.Duplex.Params M Cv L)
    (root : Array U8 32#usize) (length : U32)
    (error : verifier.Error → Result E) (bytes proof : Slice U8) (k : Usize)
    (out : alloc.vec.Vec U8)
    (h : FirstComposition.firstCurrent invalidAccountData (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
      D error bytes proof k=ok (.Ok out)) :
    ∃ (s : AspisR1PublicPreparation.FirstCaller.DecoderStatement),
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual bytes=ok (.Ok s) ∧
      k=compact.SPLIT ∧ ∃ (zero : aspis_core.field.wide_exact.WideExact)
        (semantic y1 : Slice U8) (v : AspisR1SelectedWideViewV1.verifier.View)
        (sem : r1_semantic.Verified Unit) (prepared : AspisR1PublicPreparation.verifier.Prepared)
        (scratch : Array PE 29#usize),
        AspisR1SelectedWideViewV1.verifier.candidate.wide_view proof semantic y1=ok (.Ok v) ∧
        v.variant = .S2 ∧
        (semanticBase ops B).op9 D (FirstComposition.toCurrentPublic
          (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)) v.semantic () none=ok (.Ok sem) ∧
        AspisR1PublicPreparation.PreparedScratchModel.prepare
          (concreteBoundaries (installedBoundaries (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed))
          (retainedDigest D) (retainedSem sem) (AspisR1SelectedWideViewV1.preparedView v) ()
          (mapArray retainedE (Array.repeat 29#usize zero)) = ok (.Ok prepared,scratch) ∧
        AspisS1SemanticArrayRanges.CurrentVerifiedNumeric sem ∧
        (Canonical (toClaimE prepared.gamma) ∧ Canonical (toClaimE prepared.kappa)) ∧
        OriginalPayloadClaimMeaning (retainedSem sem) v.y1
          (toClaimE (AspisR1SelectedWideViewV1.prepCarrier v.inactive))
          (toClaimE prepared.gamma) (toClaimE prepared.kappa) (toClaimE prepared.claim)
          (mapArray toClaimE scratch) ∧
        (∀ i : Usize, i.val<29 → ∃ value : AspisR1CurrentPreparedClaim.Concrete.E,
          Array.index_usize (mapArray toClaimE scratch) i=ok value ∧
          Canonical value ∧ decode value=decode (toClaimE prepared.gamma)^i.val) ∧
        ExactSerializedRankTrace (retainedDigest D) p bytes root length
          (retainedSem sem) (AspisR1SelectedWideViewV1.preparedView v) () prepared scratch ∧
        Row31QueryProgramMeaning (retainedDigest D) (AspisR1SelectedWideViewV1.preparedView v) prepared ∧
        Tx1Reachability.afterPrepare (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B) D bytes proof k () none
          (currentPrepared prepared) (mapArray currentE scratch)=ok (.Ok out) := by
  obtain ⟨s,hd,hk,zero,prepared,scratch,semantic,y1,v,sem,hview,hsem,hnew,htail⟩ :=
    FirstComposition.first_current_prepared_new invalidAccountData
      (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
      D error bytes proof k out h
  change sourceView proof semantic y1 = ok (.Ok v) at hview
  unfold sourceView at hview
  obtain ⟨r,hr,hview⟩ := bind_success _ _ _ hview
  cases r with
  | Err e => cases hview
  | Ok oldv =>
    have hv : selectedView oldv = v := core.result.Result.Ok.inj (Result.ok.inj hview)
    subst v
    change originalNew (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
      D sem (selectedView oldv) () (Array.repeat 29#usize zero) = ok (.Ok prepared,scratch) at hnew
    rw [originalNew_eq_transport] at hnew
    obtain ⟨pair,hbackend,hnew⟩ := bind_success _ _ _ hnew
    rcases pair with ⟨r,oldScratch⟩
    cases r with
    | Err e => cases hnew
    | Ok oldPrepared =>
      have heq : (core.result.Result.Ok (currentPrepared oldPrepared),mapArray currentE oldScratch) =
          (core.result.Result.Ok prepared,scratch) := Result.ok.inj hnew
      have hp := core.result.Result.Ok.inj (congrArg Prod.fst heq)
      have hg := congrArg Prod.snd heq
      subst prepared
      subst scratch
      rw [retained_selected_view] at hbackend
      have hinactive := AspisR1SelectedWideViewV1.wide_view_inactive_canonical proof semantic y1 oldv hr
      obtain ⟨hcan,halpha,hclaim,hpowers⟩ := prepared_installed_meaning
        (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
        (retainedDigest D) (retainedSem sem) (AspisR1SelectedWideViewV1.preparedView oldv)
        () oldPrepared oldScratch (mapArray retainedE (Array.repeat 29#usize zero)) hinactive hbackend
      have hrank := prepared_installed_joint_rank_trace (withOriginalSerializer closedSampling)
        AspisS1M31Embedding.Total.embed (retainedDigest D) p bytes root length (retainedSem sem)
        (AspisR1SelectedWideViewV1.preparedView oldv) () oldPrepared oldScratch
        (mapArray retainedE (Array.repeat 29#usize zero)) hbackend
      have trace := (jointRankTrace_exact_bytes closedSampling (retainedDigest D) p bytes root length
        (retainedSem sem) (AspisR1SelectedWideViewV1.preparedView oldv) () oldPrepared oldScratch).mp hrank
      have variant := AspisR1SelectedWideViewV1.wide_view_variant proof semantic y1 oldv hr
      have mappedVariant : (AspisR1SelectedWideViewV1.preparedView oldv).variant =
          AspisR1PublicPreparation.transport.Variant.S2 := by
        change (match oldv.variant with | .S1 => .S1 | .S2 => .S2 | .D => .D) = _
        rw [variant]
      have folds : AspisR1PublicPreparation.transport.Variant.folds
          (AspisR1SelectedWideViewV1.preparedView oldv).variant = ok 2#usize := by
        rw [mappedVariant]
        rfl
      have row31 := exactRankTrace_row31_program (retainedDigest D) p bytes root length
        (retainedSem sem) (AspisR1SelectedWideViewV1.preparedView oldv) () oldPrepared oldScratch folds trace
      have verify : S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children B D
          (FirstComposition.toCurrentPublic (AspisR1PublicPreparation.PreparationBinding.preparationPublic s))
          oldv.semantic () = ok (.Ok sem) := hsem
      have numeric := AspisS1SemanticArrayRanges.installed_verify_numeric B D _ oldv.semantic () sem verify
      exact ⟨s,hd,hk,zero,semantic,y1,oldv,sem,oldPrepared,oldScratch,
        hr,variant,hsem,hbackend,numeric,hcan,hclaim,hpowers,trace,row31,htail⟩

#print axioms first_native_buffers_prepared_trace
end AspisS1NativeBufferClaimTrace
end
