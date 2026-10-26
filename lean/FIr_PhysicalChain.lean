import FIr_PhysicalInitial
import FIr_SourceChain
import FIr_AlphaLiteral
import S1OriginalNewStaticFieldsV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_PhysicalChain
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisS1ValuesOwnedInstallation OriginalSerializerInstallation
open MultiproofConeCanonical OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open RawCutTranscriptRun R0P.Mask AspisV8R19.DuplexFrames
theorem on_run {CoreError H : Type} (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo D hash pub publicBytes proof split saved)
    (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (parsed : OraclePortStoredParserC4.parseReached (bytesOf proof.val) tr=some p)
    (view : LiteralOpeningView.View) (claim : LiteralSemanticPrefix.E)
    (polys : Fin 10 → Polynomial LiteralSemanticPrefix.E)
    (opening : LiteralOpeningView.read (typedRows p q tr)=some view)
    (claimRead : claimOf (SelectedSemanticPrefixFacts.lift view.semantic)=some claim)
    (polyRead : semPolysZ (SelectedSemanticPrefixFacts.lift view.semantic)=some polys)
    (out : AspisR1PublicPreparation.verifier.Prepared) (output : currentPrepared out=run.p)
    (data : RecordedBinaryExperimentBin.SourceInputs)
    (numeric : F3L_SourcePrepared.numeric out=OraclePortCheckpointResumeC5.prepared
      (OraclePortAcceptedContextC6.context p data view) data.data (SelectedChallengeMap.rhoOf data.rho) q)
    (range : ∀ j : Fin 10,FIr_SampleRange.InBase ((view.semantic.map Prod.snd).getD (15+j.val) 0)) :
    ∀ j : Fin 9,(polys j.succ).eval 0+(polys j.succ).eval 1=
      (polys j.castSucc).eval ((view.semantic.map Prod.snd).getD (15+j.castSucc.val) 0) := by
  obtain ⟨stored,initialBytes,expanded,y1,sourceView,sem,readStored,expand,wide,same,verify,prepare⟩ :=
    PSem_SourceCuts.buffers ops reserved query geo B std D hash pub publicBytes proof split saved run
  obtain ⟨pre,before,after,running,record,decoded,initial,entries,values,
    sourceParsed,rounds,read,decode,index,annotated,alpha,full,claimEq,polyEq,chain⟩ :=
    FIq_TypedData.verified (ClaimsUnrolledFinish.install std B) D pub expanded hash sem verify
  have sourceRows := PSem_SemanticRows.source_rows stored initialBytes expanded pre expand sourceParsed
  have physical := PSem_Slices.range_bytes proof stored 16#usize 7031#usize readStored
  change stored.val=(proof.val.drop 16).take 7015 at physical
  have wire : bytesOf (stored.val.drop 32)=slice (bytesOf proof.val) 48 6983 := by
    rw [physical,List.drop_take,List.drop_drop]
    simp only [bytesOf,List.map_take,List.map_drop,slice]
  rw [wire] at sourceRows
  have selected := FIr_PhysicalInitial.parsed_rows (bytesOf proof.val) p tr parsed _ sourceRows
  have aligned := (OraclePortStoredParserC4.parsed _ _ _ parsed).2.2
  have literalRows : semanticRows 27 0 (slice p.wire 48 6983)=some p.semantic := by
    rw [selected.1,selected.2]
    exact sourceRows
  have frames : SemanticPrefixCodec.encodeFull values=
      LiteralSemanticCodecBridge.records ((typedRows p q tr).take 25) := by
    rw [PAln_Records.records_take p q tr aligned literalRows,selected.2]
    have completed : AspisR1PublicPreparation.PrefixAdapter.completedRecords pre=
        (pre.records.val.map (fun s => bytesOf s.val)).take 25 := by
      simp only [AspisR1PublicPreparation.PrefixAdapter.completedRecords,List.map_take]
      rfl
    exact full.trans completed
  have polysSame := Option.some.inj (polyRead.symm.trans (FIr_LiteralValues.polynomials values _ view opening frames))
  have static := originalNew_static (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
    D sem sourceView hash run.p run.scratch (Array.repeat 29#usize run.zero) prepare
  have alphaEq : out.semantic_alpha=(retainedSem sem).alpha :=
    FIr_ChallengeValue.alpha_same out sem.alpha
      ((congrArg (fun p : verifier.Prepared=>p.semantic_alpha) output).trans static.2.2.1)
  intro j
  have challengeEq := FIr_AlphaLiteral.value out (retainedSem sem).alpha alphaEq view p q data numeric j.castSucc (range j.castSucc)
  rw [polysSame,← challengeEq]
  exact FIr_SourceChain.adjacent annotated values full (retainedSem sem).alpha alpha j

#print axioms on_run
end AspisR1.FIr_PhysicalChain
end
