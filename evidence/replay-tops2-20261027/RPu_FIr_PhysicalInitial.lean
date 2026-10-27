import RPu_FIr_SourceInitial
import RPu_FIr_LiteralValues
import RPz7_PSem_SemanticRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_PhysicalInitial
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisS1ValuesOwnedInstallation OriginalSerializerInstallation
open MultiproofConeCanonical OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open RawCutTranscriptRun R0P.Mask AspisV8R19.DuplexFrames

theorem parsed_rows (proof : Bytes) (p : Parsed) (tr : ErasedPrefix)
    (parsed : OraclePortStoredParserC4.parseReached proof tr=some p)
    (rows : List Bytes) (same : semanticRows 27 0 (slice proof 48 6983)=some rows) :
    p.wire=proof ∧ p.semantic=rows := by
  have raw := (OraclePortStoredParserC4.parsed proof tr p parsed).1
  unfold parse at raw
  split at raw
  · cases raw
  · split at raw
    · cases raw
    · rw [same] at raw
      simp only [Option.bind_some,Option.pure_def,Option.some.injEq] at raw
      cases raw
      exact ⟨rfl,rfl⟩

/-- The accepted source's first checked polynomial boundary transported to
any successful literal view of the SAME physical proof and reached rows. -/
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
    (polyRead : semPolysZ (SelectedSemanticPrefixFacts.lift view.semantic)=some polys) :
    (polys 0).eval 0+(polys 0).eval 1=claim := by
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
  have selected := parsed_rows (bytesOf proof.val) p tr parsed _ sourceRows
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
  have claimSame := Option.some.inj (claimRead.symm.trans (FIr_LiteralValues.claim values _ view opening frames))
  have polysSame := Option.some.inj (polyRead.symm.trans (FIr_LiteralValues.polynomials values _ view opening frames))
  rw [polysSame,claimSame,← claimEq]
  exact FIr_SourceInitial.first_boundary (retainedDigest D) pre _ _ entries annotated values full

#print axioms parsed_rows
#print axioms on_run
end AspisR1.FIr_PhysicalInitial
end
