import S1SourceFinalOpsV1
import S1ReachedMaskCanonicalV1
set_option autoImplicit false
namespace AspisS1ReachedFinalNumeric
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1ClaimPreparedBridge AspisS1ExtractedRoundChildren
open AspisS1SourceFinalOps (add mul decodeQ)

/-- Every local value is from the same reached source finish. Numeric output
ranges need NO Terminal or eta input-canonicality premise. The stronger
multiplicative field formula is explicitly conditional on those domains. -/
def ReachedFinalNumeric {H : Type} (base : FinishModel.Boundaries)
    (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (sem : r1_semantic.Verified H) : Prop :=
  ∃ (first : Array MainQM 16#usize) (second : Array MainQM 10#usize)
    (row0 : Array MainQM 29#usize) (g maskValue terminalValue product sum extra28 target running : MainQM),
    AspisR1SelectedMaskProbe.core.array.from_fn 16#usize (FinishModel.closureFn9 D) sem.claims=ok first ∧
    AspisR1SelectedMaskProbe.core.array.from_fn 10#usize (FinishModel.closureFn5 D) sem.claims=ok second ∧
    Array.index_usize sem.claims 0#usize=ok row0 ∧ Array.index_usize row0 27#usize=ok g ∧
    AspisS1SourceMaskOps.mask first second g sem.alpha=ok maskValue ∧
    base.terminal pub sem.claims sem.alpha sem.challenges=ok (.Ok terminalValue) ∧
    mul sem.challenges.eta terminalValue=ok product ∧ add maskValue product=ok sum ∧
    Array.index_usize sem.extra 28#usize=ok extra28 ∧ add sum extra28=ok target ∧
    core.cmp.PartialEq.ne.trait_default aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 running target=ok false ∧
    Canonical maskValue ∧ Canonical product ∧ Canonical sum ∧ Canonical extra28 ∧ Canonical target ∧
    decodeQ target=decodeQ maskValue+decodeQ product+decodeQ extra28 ∧
    (Canonical sem.challenges.eta → Canonical terminalValue →
      decodeQ target=decodeQ maskValue+decodeQ sem.challenges.eta*decodeQ terminalValue+decodeQ extra28)

/-- ACCEPTED-ONLY full finish and its later borrowed prepared_claim: no
independent selector/mask/field-call success or numeric hypothesis is added. -/
theorem finish_final_numeric (base : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (before : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (sem : r1_semantic.Verified H)
    (finished : FinishModel.finish children
      (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install base))
      D pub pre before challenges none=ok (.Ok sem))
    (y1 : Slice U8) (inactive kappa out : PE) (scratch : Array PE 29#usize)
    (claimed : AspisR1CurrentCaller.BorrowedClaimPrepared.claim D sem y1 inactive scratch kappa=ok (.Ok out)) :
    ReachedFinalNumeric base D pub sem := by
  have numeric := AspisS1SemanticArrayRanges.accepted_finish_numeric
    (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install base))
    D pub pre before challenges none sem finished
  have inputs := AspisS1ReachedMaskInputs.source_finish_reached_mask_inputs
    (AspisS1SourceFinalOps.install base) D pub pre before challenges sem finished
    y1 inactive kappa out scratch claimed
  obtain ⟨fm,sm,rm,gm,vm,hfm,hsm,hrm,hgm,hvm,cm⟩ :=
    AspisS1ReachedMaskCanonical.canonical_of_reached_inputs D sem inputs
  obtain ⟨running,t25,r25,r26,z0,t26,z1,t27,hrounds,challengesEq,_,_,hclaims,_,_,_,_,_,_,_,
    first,second,row0,g,maskValue,terminalValue,product,sum,extra28,target,
    hterminal,hfirst,hsecond,hrow,hg,hmask,hproduct,hsum,hextra,hfinal,hguard⟩ :=
    S1SemanticFinishMaskCalls.finish_success children
      (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install base))
      D pub pre before challenges none sem finished
  change AspisR1SelectedMaskProbe.core.array.from_fn 16#usize (FinishModel.closureFn9 D) sem.claims=ok first at hfirst
  change AspisR1SelectedMaskProbe.core.array.from_fn 10#usize (FinishModel.closureFn5 D) sem.claims=ok second at hsecond
  change AspisS1SourceMaskOps.mask first second g sem.alpha=ok maskValue at hmask
  change mul challenges.eta terminalValue=ok product at hproduct
  change add maskValue product=ok sum at hsum
  change add sum extra28=ok target at hfinal
  change base.terminal pub sem.claims sem.alpha challenges=ok (.Ok terminalValue) at hterminal
  have fe : fm=first := Result.ok.inj (hfm.symm.trans hfirst)
  have se : sm=second := Result.ok.inj (hsm.symm.trans hsecond)
  have re : rm=row0 := Result.ok.inj (hrm.symm.trans hrow)
  subst fm;subst sm;subst rm
  have ge : gm=g := Result.ok.inj (hgm.symm.trans hg)
  subst gm
  have me : vm=maskValue := Result.ok.inj (hvm.symm.trans hmask)
  have cmask : Canonical maskValue := me ▸ cm
  have cproduct : Canonical product := AspisS1SourceFinalOps.mul_success_canonical _ _ _ hproduct
  have known := AspisS1QueryArrayOperations.index_total sem.extra 28#usize (by scalar_tac)
  have extraEq := Result.ok.inj (hextra.symm.trans known)
  have cextra : Canonical extra28 := by
    rw [extraEq]
    exact numeric.2.1 _ (List.getElem_mem _)
  obtain ⟨sumModel,sumCall,sumCanon,sumValue⟩ := AspisS1SourceFinalOps.add_total maskValue product cmask cproduct
  have sumEq : sumModel=sum := Result.ok.inj (sumCall.symm.trans hsum)
  subst sumModel
  obtain ⟨targetModel,targetCall,targetCanon,targetValue⟩ := AspisS1SourceFinalOps.add_total sum extra28 sumCanon cextra
  have targetEq : targetModel=target := Result.ok.inj (targetCall.symm.trans hfinal)
  subst targetModel
  have formula : decodeQ target=decodeQ maskValue+decodeQ product+decodeQ extra28 := by
    rw [targetValue,sumValue]
  have productCall : mul sem.challenges.eta terminalValue=ok product := by simpa only [challengesEq] using hproduct
  have terminalCall : base.terminal pub sem.claims sem.alpha sem.challenges=ok (.Ok terminalValue) := by
    simpa only [challengesEq] using hterminal
  refine ⟨first,second,row0,g,maskValue,terminalValue,product,sum,extra28,target,running,
    hfirst,hsecond,hrow,hg,hmask,terminalCall,productCall,hsum,hextra,hfinal,hguard,
    cmask,cproduct,sumCanon,cextra,targetCanon,formula,?_⟩
  intro etaCanonical terminalCanonical
  obtain ⟨p,pcall,_,pvalue⟩ := AspisS1SourceFinalOps.mul_total sem.challenges.eta terminalValue etaCanonical terminalCanonical
  have pe : p=product := Result.ok.inj (pcall.symm.trans productCall)
  rw [pe] at pvalue
  rw [formula,pvalue]

/-- Same installed semantic verification supplies its own prefix/begin/finish.
Native SDK/source extraction and other finish fields retain their boundaries. -/
theorem verify_final_numeric (base : FinishModel.Boundaries)
    {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (verified : AspisR1CurrentCaller.S1SemanticInstallation.verify children
      (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install base)) D pub bytes hash=ok (.Ok sem))
    (y1 : Slice U8) (inactive kappa out : PE) (scratch : Array PE 29#usize)
    (claimed : AspisR1CurrentCaller.BorrowedClaimPrepared.claim
      (AspisR1CurrentCaller.InstalledPreparation.retainedDigest D)
      (AspisR1CurrentCaller.InstalledPreparation.retainedSem sem) y1 inactive scratch kappa=ok (.Ok out)) :
    ReachedFinalNumeric base (AspisR1CurrentCaller.InstalledPreparation.retainedDigest D)
      (AspisR1CurrentCaller.FirstComposition.toRetainedPublic pub)
      (AspisR1CurrentCaller.InstalledPreparation.retainedSem sem) := by
  have source := AspisR1CurrentCaller.S1SemanticInstallation.verify_return children
    (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install base)) D pub bytes hash sem verified
  obtain ⟨pre,initial,after,challenges,parsed,publicInit,begin,finish⟩ :=
    S1SemanticVerify.verify_success _ (AspisR1CurrentCaller.InstalledPreparation.retainedDigest D)
      (AspisR1CurrentCaller.FirstComposition.toRetainedPublic pub) bytes hash none _ source
  rw [AspisS1SourceMaskOps.root_copy_commutes,AspisS1SourceFinalOps.root_copy_commutes] at finish
  exact finish_final_numeric (S1SemanticRootCopy.install base)
    (AspisR1CurrentCaller.InstalledPreparation.retainedDigest D)
    (AspisR1CurrentCaller.FirstComposition.toRetainedPublic pub) pre after challenges
    (AspisR1CurrentCaller.InstalledPreparation.retainedSem sem) finish y1 inactive kappa out scratch claimed

#print axioms finish_final_numeric
#print axioms verify_final_numeric
end AspisS1ReachedFinalNumeric
