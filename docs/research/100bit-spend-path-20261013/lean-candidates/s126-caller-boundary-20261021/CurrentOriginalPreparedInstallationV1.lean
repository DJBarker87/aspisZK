import CurrentOriginalPreparedCarrierTransportV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
namespace AspisR1CurrentCaller.OriginalPreparedInstallation
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge
open AspisR1ClaimPreparedBridge.InstalledMeaning AspisR1CurrentPreparedClaim.Concrete
open AspisR1PreparedSourcePowersBoundariesV1 AspisR1PreparedSourcePowersJointRankV1

def originalNew (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 → Result PE)
    {H : Type} (D : aspis_core.digest.Digest32 H) (sem : r1_semantic.Verified H)
    (v : verifier.View) (hash : H) (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    Result ((core.result.Result verifier.Prepared verifier.Error) × Array aspis_core.field.wide_exact.WideExact 29#usize) :=
  OriginalPreparedSource.prepare (sourceBoundaries (installedBoundaries sampling embed)) D sem v hash g

/-- No output/success/totality premise: complete current original source body
under the explicitly installed primitive children equals the retained backend.
The original prepared_claim and RustStd child contracts remain separate gates. -/
theorem originalNew_eq_sourcePrepared
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 → Result PE) :
    @originalNew sampling embed=@sourcePrepared sampling embed := by
  funext H D sem v hash g
  unfold originalNew
  rw [OriginalPreparedSource.prepare_transport]
  unfold OriginalPreparedSource.transported sourcePrepared
  rw [AspisR1PublicPreparation.OriginalPreparedNative.eq_prepare]
  rfl

def installOriginal (ops : Ops)
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 → Result PE) : Ops :=
  {InstalledPreparation.install ops sampling embed with op8:=originalNew sampling embed}

theorem installOriginal_eq (ops : Ops)
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 → Result PE) :
    installOriginal ops sampling embed=InstalledPreparation.install ops sampling embed := by
  unfold installOriginal InstalledPreparation.install
  rw [originalNew_eq_sourcePrepared]

/-- Enclosing first success with the freshly emitted original Prepared.new
body installed on its complete current carriers. The desired claim/rank,
View parsing, decoder result, semantic result and scratch are conclusions.
Primitive child installation is tracked explicitly, never hidden by renaming. -/
theorem first_original_new_claim_and_rank {E M Cv : Type} {L : Nat}
    (invalidAccountData : E) (ops : Ops)
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 → Result PE)
    (D : aspis_core.digest.Digest32 Unit) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice U8) (root : Array U8 32#usize) (length : U32)
    (error : verifier.Error → Result E) (bytes proof : Slice U8) (k : Usize)
    (out : alloc.vec.Vec U8)
    (h : FirstComposition.firstCurrent invalidAccountData (installOriginal ops sampling embed)
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
        JointRankTrace sampling embed (retainedDigest D) p pubInput root length
          (retainedSem sem) (AspisR1SelectedWideViewV1.preparedView v) () prepared scratch ∧
        Tx1Reachability.afterPrepare (installOriginal ops sampling embed) D bytes proof k () none
          (currentPrepared prepared) (mapArray currentE scratch)=ok (.Ok out) := by
  rw [installOriginal_eq] at h ⊢
  exact InstalledPreparation.first_installed_claim_and_rank invalidAccountData ops sampling embed
    D p pubInput root length error bytes proof k out h

#print axioms originalNew_eq_sourcePrepared
#print axioms installOriginal_eq
#print axioms first_original_new_claim_and_rank
end AspisR1CurrentCaller.OriginalPreparedInstallation
