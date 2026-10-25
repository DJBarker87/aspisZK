import S1MaskCallerDomainsV1
import S1SourceMaskOpsV1
import S1SemanticFinishMaskCallsV1
set_option autoImplicit false
namespace AspisS1ReachedMaskInputs
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1ClaimPreparedBridge
open AspisS1ExtractedRoundChildren
open AspisS1SourceMaskOps (mask install root_copy_commutes)
open AspisS1MaskCallerDomains

/-- The SAME reached source mask call, with each actual selector/input in its
canonical domain. No numeric or success property is hidden in a parameter. -/
def ReachedMaskInputRanges {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) : Prop :=
  ∃ (first : Array MainQM 16#usize) (second : Array MainQM 10#usize)
    (row0 : Array MainQM 29#usize) (g value : MainQM),
    AspisR1SelectedMaskProbe.core.array.from_fn 16#usize (FinishModel.closureFn9 D) sem.claims=ok first ∧
    AspisR1SelectedMaskProbe.core.array.from_fn 10#usize (FinishModel.closureFn5 D) sem.claims=ok second ∧
    Array.index_usize sem.claims 0#usize=ok row0 ∧
    Array.index_usize row0 27#usize=ok g ∧
    mask first second g sem.alpha=ok value ∧
    (∀ q ∈ first.val, AspisS1MaskCallerDomains.Canonical q) ∧
    (∀ q ∈ second.val, AspisS1MaskCallerDomains.Canonical q) ∧
    AspisS1MaskCallerDomains.Canonical g ∧
    (∀ q ∈ sem.alpha.val, AspisS1MaskCallerDomains.Canonical q)

/-- Acceptance of the complete source finish plus its later concrete claim
supplies the actual mask operands and their ranges, all on the same semantic
return. The other finish operations retain B; no input range is assumed. -/
theorem source_finish_reached_mask_inputs (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (before : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (sem : r1_semantic.Verified H)
    (finished : FinishModel.finish children (install B)
      D pub pre before challenges none=ok (.Ok sem))
    (y1 : Slice U8) (inactive kappa out : PE) (scratch : Array PE 29#usize)
    (claimed : AspisR1CurrentCaller.BorrowedClaimPrepared.claim D sem y1 inactive scratch kappa=ok (.Ok out)) :
    ReachedMaskInputRanges D sem := by
  have numeric := AspisS1SemanticArrayRanges.accepted_finish_numeric
    (install B) D pub pre before challenges none sem finished
  obtain ⟨fm,sm,rm,gm,hfm,hsm,hrm,hgm,cf,cs,cg,ca⟩ :=
    accepted_claim_mask_inputs D sem y1 inactive kappa out scratch claimed numeric D
  obtain ⟨running,t25,r25,r26,z0,t26,z1,t27,hrounds,_,_,_,hclaims,_,_,_,_,_,_,_,
    first,second,row0,g,value,terminalValue,product,sum,extra28,maskedTerminal,
    hterminal,hfirst,hsecond,hrow,hg,hmask,hproduct,hsum,hextra,hfinal,hguard⟩ :=
    S1SemanticFinishMaskCalls.finish_success children (install B)
      D pub pre before challenges none sem finished
  change AspisR1SelectedMaskProbe.core.array.from_fn 16#usize (FinishModel.closureFn9 D) sem.claims=ok first at hfirst
  change AspisR1SelectedMaskProbe.core.array.from_fn 10#usize (FinishModel.closureFn5 D) sem.claims=ok second at hsecond
  change mask first second g sem.alpha=ok value at hmask
  have fe : fm=first := Result.ok.inj (hfm.symm.trans hfirst)
  have se : sm=second := Result.ok.inj (hsm.symm.trans hsecond)
  have re : rm=row0 := Result.ok.inj (hrm.symm.trans hrow)
  subst fm;subst sm;subst rm
  have ge : gm=g := Result.ok.inj (hgm.symm.trans hg)
  subst gm
  exact ⟨first,second,row0,g,value,hfirst,hsecond,hrow,hg,hmask,cf,cs,cg,ca⟩

/-- The same full installed semantic-verifier return supplies its own finish.
Neither an independent successful finish nor alpha/Claims ranges are premises. -/
theorem source_verify_reached_mask_inputs (B : FinishModel.Boundaries)
    {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (verified : AspisR1CurrentCaller.S1SemanticInstallation.verify children
      (install B) D pub bytes hash=ok (.Ok sem))
    (y1 : Slice U8) (inactive kappa out : PE) (scratch : Array PE 29#usize)
    (claimed : AspisR1CurrentCaller.BorrowedClaimPrepared.claim
      (AspisR1CurrentCaller.InstalledPreparation.retainedDigest D)
      (AspisR1CurrentCaller.InstalledPreparation.retainedSem sem) y1 inactive scratch kappa=ok (.Ok out)) :
    ReachedMaskInputRanges (AspisR1CurrentCaller.InstalledPreparation.retainedDigest D)
      (AspisR1CurrentCaller.InstalledPreparation.retainedSem sem) := by
  have source := AspisR1CurrentCaller.S1SemanticInstallation.verify_return children
    (install B) D pub bytes hash sem verified
  obtain ⟨pre,initial,after,challenges,parsed,publicInit,begin,finish⟩ :=
    S1SemanticVerify.verify_success _
      (AspisR1CurrentCaller.InstalledPreparation.retainedDigest D)
      (AspisR1CurrentCaller.FirstComposition.toRetainedPublic pub) bytes hash none _ source
  rw [root_copy_commutes] at finish
  exact source_finish_reached_mask_inputs (S1SemanticRootCopy.install B)
    (AspisR1CurrentCaller.InstalledPreparation.retainedDigest D)
    (AspisR1CurrentCaller.FirstComposition.toRetainedPublic pub) pre after challenges
    (AspisR1CurrentCaller.InstalledPreparation.retainedSem sem) finish
    y1 inactive kappa out scratch claimed

#print axioms source_finish_reached_mask_inputs
#print axioms source_verify_reached_mask_inputs
end AspisS1ReachedMaskInputs
