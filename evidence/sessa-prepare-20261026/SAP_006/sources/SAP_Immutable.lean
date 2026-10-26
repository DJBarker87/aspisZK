import SAP_Cuts
import SAP_CanonicalCarrier
import PAln_OpeningStages
import F3K_SourceQueryDecode
import F3L_RhoCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_Immutable
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared OriginalSerializerInstallation
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning

/-- Source preparation's canonical opening fields; semantic fields are kept
as the actual returned semantic value rather than assumed canonical. -/
theorem fields (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : verifier.candidate.prepare (RowShape_InstalledSlots.verifierOps ops B std)
      D pub proof hash none input=ok (.Ok p,scratch)) :
    ∃ (view : verifier.View) (sem : r1_semantic.Verified H)
      (out : AspisR1PublicPreparation.verifier.Prepared),
      S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
        (ClaimsUnrolledFinish.install std B) D pub view.semantic hash=ok (.Ok sem) ∧
      currentPrepared out=p ∧ out.semantic_alpha=(retainedSem sem).alpha ∧ out.z=(retainedSem sem).z ∧
      (Tx1Q_Carriers.prepared p).variant=.S2 ∧
      (∀ j : Fin 22,((Tx1Q_Carriers.prepared p).queries.val[j.val]'(by simpa [(Tx1Q_Carriers.prepared p).queries.property] using j.isLt)).val<262144) ∧
      OraclePortCkptAbi4Decode.CanonicalWide (CheckpointBytes3Namespaces.toE (Tx1Q_Carriers.prepared p).gamma) ∧
      OraclePortCkptAbi4Decode.CanonicalWide (CheckpointBytes3Namespaces.toE (Tx1Q_Carriers.prepared p).kappa) ∧
      (∀ j : Fin 2,OraclePortCkptAbi4Decode.CanonicalWide (CheckpointBytes3Namespaces.toE
        ((Tx1Q_Carriers.prepared p).alpha.val[j.val]'(by simpa [(Tx1Q_Carriers.prepared p).alpha.property] using j.isLt)))) ∧
      Port3_FlushInstall.Canonical (Tx1Q_Carriers.prepared p).rho ∧
      OraclePortCkptAbi4Decode.CanonicalWide (CheckpointBytes3Namespaces.toE (Tx1Q_Carriers.prepared p).claim) := by
  obtain ⟨stored,initial,expanded,y1,view,sem,read,expand,wide,same,verify,prepare⟩ :=
    SAP_Cuts.buffers ops B std D hash pub proof p input scratch success
  obtain ⟨out,rs,prepared,outEq,scratchEq⟩ := PAln_Borrowed.original_success
    (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed D sem view hash
    input scratch p prepare
  have meaning := prepared_installed_meaning (withOriginalSerializer closedSampling)
    AspisS1M31Embedding.Total.embed (retainedDigest D) (retainedSem sem) (retainedView view) hash
    out rs (mapArray retainedE input) (F3M_InactiveCanonical.source proof expanded y1 view wide) prepared
  have reached := AspisR1PublicPreparation.PreparedScratchReachability.prepare_success _ (retainedDigest D)
    (retainedSem sem) (retainedView view) hash out rs (mapArray retainedE input) prepared
  have variant : (retainedView view).variant=AspisR1PublicPreparation.transport.Variant.S2 := by
    change retainedVariant view.variant=_
    rw [sourceView_variant proof expanded y1 view wide]
    rfl
  obtain ⟨t0,t1,t2,t3,t4,t5,t6,inactive,root,bytes1,bytes2,gamma,kappa,a0,a1,rho,queries,claim,
    seed,first,serialized,second,third,unwrapped,extended1,extended2,fourth,query,last,powers,claimed,output⟩ :=
    PAln_OpeningStages.double_of_reached _ (retainedDigest D) (retainedSem sem) (retainedView view)
      hash out rs variant reached
  have query' : AspisR1PublicPreparation.QueriesModel.queries
      (AspisR1PublicPreparation.Query31ConcreteMaterializedSchedule.concreteBoundaries
        AspisR1PublicPreparation.Query31ConcreteDriverTraceFacts.sourceDefaultState AspisS1M31Embedding.Total.embed)
      (retainedDigest D) t4 31#u8 (retainedView view).final_message=ok (.Ok queries,t5) := query
  obtain ⟨q,_,coordinates⟩ := F3K_SourceQueryDecode.source _ _ _ _ _ _ query'
  have hclaim := meaning.2.2.1
  obtain ⟨final,hzero,hvalues,canonClaim,polynomial⟩ := hclaim
  obtain ⟨alpha0,alpha1,alphaEq,canon0,canon1⟩ := meaning.2.1
  refine ⟨view,sem,out,?_,outEq,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [same];exact verify
  · rw [output];rfl
  · rw [output];rfl
  · rw [←outEq,output]
    change Tx1Q_Carriers.variant (currentVariant (retainedView view).variant)=_
    rw [variant];rfl
  · intro j
    rw [←outEq,output]
    change (queries.val[j.val]'_).val<262144
    rw [coordinates j];exact (q j).isLt
  · rw [←outEq];exact SAP_CanonicalCarrier.wide out.gamma meaning.1.1
  · rw [←outEq];exact SAP_CanonicalCarrier.wide out.kappa meaning.1.2
  · intro j
    rw [←outEq]
    change OraclePortCkptAbi4Decode.CanonicalWide (CheckpointBytes3Namespaces.toE
      (Tx1Q_Carriers.e (currentE (out.alpha.val[j.val]'_))))
    rw [alphaEq]
    fin_cases j
    · exact SAP_CanonicalCarrier.wide _ canon0
    · exact SAP_CanonicalCarrier.wide _ canon1
  · rw [←outEq,output]
    exact F3L_RhoCanonical.scalar _ _ _ _ _ _ last
  · rw [←outEq];exact SAP_CanonicalCarrier.wide out.claim canonClaim

#print axioms fields
end AspisR1.SAP_Immutable
end
