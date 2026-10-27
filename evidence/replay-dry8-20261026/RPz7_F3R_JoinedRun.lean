import RPz7_F3M_InactiveCanonical
import RPz7_CurrentPreparedInstalledMeaning
import RPz7_F3M_SemanticSource
import RPz7_PAln_CurrentPhysical
import RPz7_PAln_OpeningStages
import RPz7_F3R_BothBuffers
import RPz7_F3R_SemanticOnTrace
import RPz7_F3Q_PrepareMap
import PSem_Values
import RPz7_PSem_Root
import RPz7_PSem_SemanticRows
import RPz7_PSem_SemanticTrace
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.F3R_JoinedRun

def storedRoot (proof : Slice U8) : List U8 := (proof.val.drop 16).take 32
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisS1ValuesOwnedInstallation OriginalSerializerInstallation
open MultiproofConeCanonical OraclePortCompactDraft

theorem on_run {CoreError : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 Unit) (hash : Unit)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo D hash pub publicBytes proof split saved) :
    ∃ (expanded y1 : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified Unit)
      (retained : AspisR1PublicPreparation.verifier.Prepared)
      (rs : Array AspisR1PublicPreparation.aspis_core.field.WideExact 29#usize) (pre : AspisR1PublicPreparation.r1_wire.Prefix)
      (t0 t25 : AspisR1PublicPreparation.r1_wire.SemanticTranscript Unit)
      (cs : List (AspisR1PublicPreparation.SourceFull25.Call (retainedDigest D) pre)),
      AspisR1PublicPreparation.PrefixAdapter.parseAccepted expanded=ok (.Ok pre) ∧
      semanticRows 27 0 (slice (bytesOf proof.val) 48 6983)=
        some (pre.records.val.map (fun s => bytesOf s.val)) ∧
      AspisR1PublicPreparation.r1_semantic.public_transcript (retainedDigest D)
        (FirstComposition.toRetainedPublic pub) hash pre.c1_root=ok (.Ok t0) ∧
      pre.c1_root.val=storedRoot proof ∧
      sourceView proof expanded y1=ok (.Ok view) ∧
      view.semantic=expanded ∧
      bytesOf view.y1.val=expand 29 (slice (bytesOf proof.val) 7031 464) ∧
      bytesOf (retainedView view).round0.val=slice (bytesOf proof.val) 7527 224 ∧
      bytesOf (retainedView view).round1.val=slice (bytesOf proof.val) 7783 224 ∧
      bytesOf (retainedView view).final_message.val=slice (bytesOf proof.val) 8007 2048 ∧
      (∀ (root : Array U8 32#usize) (bytes1 bytes2 : alloc.vec.Vec U8),
        core.option.Option.unwrap (retainedView view).folded_root=ok root →
        alloc.vec.Vec.extend_from_slice core.clone.CloneU8
          (alloc.vec.Vec.with_capacity U8 256#usize) (Array.to_slice root)=ok bytes1 →
        alloc.vec.Vec.extend_from_slice core.clone.CloneU8 bytes1 (retainedView view).round1=ok bytes2 →
        bytesOf bytes2.val=slice (bytesOf proof.val) 7751 256) ∧
      PAln_OpeningStages.Double
        (AspisR1ClaimPreparedBridge.concreteBoundaries
          (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries
            (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed))
        (retainedDigest D) (retainedSem sem) (retainedView view) hash retained rs ∧
      currentPrepared retained=run.p ∧ AspisR1ClaimPreparedBridge.mapArray currentE rs=run.scratch ∧
      S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
        (ClaimsUnrolledFinish.install std B) D pub expanded hash=ok (.Ok sem) ∧
      AspisR1ClaimPreparedBridge.OriginalPayloadClaimMeaning (retainedSem sem) (retainedView view).y1
        (AspisR1ClaimPreparedBridge.toClaimE (retainedView view).inactive)
        (AspisR1ClaimPreparedBridge.toClaimE retained.gamma)
        (AspisR1ClaimPreparedBridge.toClaimE retained.kappa)
        (AspisR1ClaimPreparedBridge.toClaimE retained.claim)
        (AspisR1ClaimPreparedBridge.mapArray AspisR1ClaimPreparedBridge.toClaimE rs) ∧
      AspisR1PublicPreparation.SourceFull25.Trace (retainedDigest D) pre t0 t25 cs ∧
      cs.map (fun c => c.row.val)=List.range 25 ∧
      cs.map AspisR1PublicPreparation.SourceFull25.Call.q=AspisR1PublicPreparation.BeginCalls.challengeList (retainedSem sem).challenges ++ (retainedSem sem).alpha.val ∧
      cs.map (fun c => bytesOf c.record.framed.val)=
        (pre.records.val.map (fun s => bytesOf s.val)).take 25 ∧
      ∃ record25 record26 z0 t26 z1 t27,
        AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok record25) ∧
        AspisR1PublicPreparation.FinishModel.circle_validated
          (AspisR1PublicPreparation.S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std B))
          (retainedDigest D) t25 record25=ok (.Ok z0,t26) ∧
        AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre 26#u8=ok (.Ok record26) ∧
        AspisR1PublicPreparation.FinishModel.circle_validated
          (AspisR1PublicPreparation.S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std B))
          (retainedDigest D) t26 record26=ok (.Ok z1,t27) ∧
        (retainedSem sem).transcript=t27 ∧
        (retainedSem sem).z=Array.make 2#usize [z0,z1] ∧
        ∃ init : AspisR1PublicPreparation.SourceGlobalOracleInitial.PublicInitCall (retainedDigest D)
          (FirstComposition.toRetainedPublic pub) pre.c1_root t0,
        AspisR1PublicPreparation.PreparedHashCode.observe
          (AspisR1PublicPreparation.PreparedHashCode.run (SdkD_PrepareSource.code (Op3I_Install.install (Op4P_Install.install (Tx1Q_Execution.base ops reserved query geo))) B std D pub proof hash
            (Array.repeat 29#usize run.zero))).1=
          (AspisR1PublicPreparation.SourceGlobalOracleInitial.initPair init::AspisR1PublicPreparation.SourceDigestLog.sourceLog cs) ++
          (AspisR1PublicPreparation.PreparedHashCode.observe (AspisR1PublicPreparation.PreparedHashCode.run
            (AspisR1PublicPreparation.S1SemanticCode.circleValidated (AspisR1PublicPreparation.S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std B))
              (retainedDigest D) t25 record25)).1 ++
          (AspisR1PublicPreparation.PreparedHashCode.observe (AspisR1PublicPreparation.PreparedHashCode.run
            (AspisR1PublicPreparation.S1SemanticCode.circleValidated (AspisR1PublicPreparation.S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std B))
              (retainedDigest D) t26 record26)).1 ++
          AspisR1PublicPreparation.PreparedHashCode.observe (AspisR1PublicPreparation.PreparedHashCode.run
            (closedPreparationCode D sem view hash (Array.repeat 29#usize run.zero))).1)) := by
  obtain ⟨stored,initial,expanded,storedY1,initialY1,y1,view,sem,read,expand,readY1,expandY1,wide,same,yEq,verify,prepare,prepareLog⟩ :=
    F3R_BothBuffers.on_run ops reserved query geo B std D hash pub publicBytes proof split saved run
  obtain ⟨retained,rs,prepared,out,scratch⟩ := PAln_Borrowed.original_success
    (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed D sem view hash
    (Array.repeat 29#usize run.zero) run.scratch run.p prepare
  have reached := AspisR1PublicPreparation.PreparedScratchReachability.prepare_success _ (retainedDigest D)
    (retainedSem sem) (retainedView view) hash retained rs
    (AspisR1ClaimPreparedBridge.mapArray retainedE (Array.repeat 29#usize run.zero)) prepared
  have canonical := F3M_InactiveCanonical.source proof expanded y1 view wide
  have meaning := AspisR1ClaimPreparedBridge.InstalledMeaning.prepared_installed_meaning
    (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed (retainedDigest D)
    (retainedSem sem) (retainedView view) hash retained rs
    (AspisR1ClaimPreparedBridge.mapArray retainedE (Array.repeat 29#usize run.zero)) canonical prepared
  have y1bytes := PSem_Values.source_expansion storedY1 initialY1 y1 expandY1
  have y1physical := PSem_Slices.range_bytes proof storedY1 7031#usize 7495#usize readY1
  change storedY1.val=(proof.val.drop 7031).take 464 at y1physical
  have y1stored : bytesOf storedY1.val=slice (bytesOf proof.val) 7031 464 := by
    rw [y1physical]
    simp only [bytesOf,List.map_take,List.map_drop,slice]
  have y1length : storedY1.length=464 := by
    have value := PSem_Slices.range_length proof storedY1 7031#usize 7495#usize readY1
    scalar_tac
  rw [y1stored,y1length] at y1bytes
  have y1Frame : bytesOf view.y1.val=OraclePortCompactDraft.expand 29 (slice (bytesOf proof.val) 7031 464) := by
    rw [yEq]
    exact y1bytes
  have sections := PAln_CurrentPhysical.sections proof expanded y1 view wide
  have second := PAln_CurrentPhysical.second proof expanded y1 view wide
  have variant := sourceView_variant proof expanded y1 view wide
  have retainedVariant : (retainedView view).variant=AspisR1PublicPreparation.transport.Variant.S2 := by
    change InstalledPreparation.retainedVariant view.variant=_
    rw [variant]
    rfl
  have opening := PAln_OpeningStages.double_of_reached _ (retainedDigest D) (retainedSem sem)
    (retainedView view) hash retained rs retainedVariant reached
  obtain ⟨pre,t0,t15,t25,cs,parsed,publicInit,trace,rows,challengeValues,frames,circles⟩ :=
    F3M_SemanticSource.values AspisS1ExtractedRoundChildren.children
      (ClaimsUnrolledFinish.install std B) D pub expanded hash sem verify
  have frozen := PSem_SemanticRows.source_rows stored initial expanded pre expand parsed
  have physical := PSem_Slices.range_bytes proof stored 16#usize 7031#usize read
  change stored.val=(proof.val.drop 16).take 7015 at physical
  have wire : bytesOf (stored.val.drop 32)=slice (bytesOf proof.val) 48 6983 := by
    rw [physical,List.drop_take,List.drop_drop]
    simp only [bytesOf,List.map_take,List.map_drop,slice]
  rw [wire] at frozen
  have root := PSem_Root.source_root stored initial expanded pre expand parsed
  have rootPhysical : pre.c1_root.val=storedRoot proof := by
    rw [root,physical]
    simp only [storedRoot,List.take_take]
    rfl
  obtain ⟨r25,r26,z0,t26,z1,t27,read25,circle25,read26,circle26,trEq,zEq⟩ := circles
  have hashEq : hash=() := Subsingleton.elim _ _
  have initHash : t0.hash=() := Subsingleton.elim _ _
  obtain ⟨init⟩ := AspisR1PublicPreparation.SourceGlobalOracleInitial.public_success_has_init_call
    (retainedDigest D) (FirstComposition.toRetainedPublic pub) pre.c1_root t0
    (by simpa only [hashEq,initHash] using publicInit)
  have rawVerified := S1SemanticInstallation.verify_return AspisS1ExtractedRoundChildren.children
    (ClaimsUnrolledFinish.install std B) D pub expanded hash sem verify
  have erased := (AspisR1PublicPreparation.S1SemanticCode.verify_erasure AspisS1ExtractedRoundChildren.children
    (AspisR1PublicPreparation.S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std B)) (retainedDigest D)
    (FirstComposition.toRetainedPublic pub) expanded hash none).trans rawVerified
  rw [hashEq] at erased
  have semanticLog := F3R_SemanticOnTrace.log AspisS1ExtractedRoundChildren.children
    (AspisR1PublicPreparation.S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std B))
    (retainedDigest D) (FirstComposition.toRetainedPublic pub) expanded (retainedSem sem) erased
    pre t0 t25 t26 t27 cs init parsed (by simpa only [hashEq] using publicInit) trace rows
    r25 r26 z0 z1 read25 circle25 read26 circle26
  rw [F3Q_PrepareMap.semantic,same,hashEq,semanticLog] at prepareLog
  refine ⟨expanded,y1,view,sem,retained,rs,pre,t0,t25,cs,parsed,frozen,publicInit,rootPhysical,wide,same,y1Frame,sections.1,sections.2.1,sections.2.2,second,opening,out,scratch,verify,meaning.2.2.1,trace,rows,challengeValues,?_,r25,r26,z0,t26,z1,t27,read25,circle25,read26,circle26,trEq,zEq,init,?_⟩
  · have mapped := congrArg (List.map (fun s : Slice U8 => bytesOf s.val)) frames
    simpa only [List.map_map,List.map_take,Function.comp_def] using mapped
  · simpa only [hashEq,List.append_assoc] using prepareLog

#print axioms on_run
end AspisR1.F3R_JoinedRun
end
