import F3J_NativeInput
import RawJ_RecordCuts
import Uni_Cuts
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.F3J_NativeConstruction
open AspisR1CurrentCaller InstalledPreparation AspisR1PublicPreparation
open S2W_NativeConsolidation MultiproofConeCanonical OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

theorem native {CoreError : Type} (adapter : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (ClaimsUnrolledSdk.sdkOps adapter (Uni_Install.current ops reserved query geo) B std) native1 native2 hashv)
    (id : S2W_ExtractionBoundary.Program) (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (accepted1 : native1 id accounts1 data1=ok (.Ok saved))
    (accepted2 : native2 id accounts2 data2 slot=ok (.Ok ()))
    (w : CanonicalCutEnrichedTranscript.Words) :
    ∃ f s log,
      SourceCuts (ClaimsUnrolledSdk.sdkOps adapter (Uni_Install.current ops reserved query geo) B std)
        accounts1 accounts2 saved f s ∧
      RawJ_RecordCuts.Recorded f s saved log ∧
      S2W_Trace.run (ClaimsUnrolledSdk.sdkOps adapter (Uni_Install.current ops reserved query geo) B std)
        (S2W_Observation.two (ClaimsUnrolledSdk.sdkOps adapter (Uni_Install.current ops reserved query geo) B std)
          id accounts1 data1 accounts2 data2 slot) []=ok (.Ok saved,log) ∧
    ∃ (i : F3_Model.Input) (pre : r1_wire.Prefix) (encoded : alloc.vec.Vec U8),
      i.physical.bytes=bytesOf f.pub.val ∧ i.stored=bytesOf f.proof.val ∧
      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic f.semantic))=ok (.Ok encoded) ∧
      i.semantic.value.pubBytes=bytesOf encoded.val ∧ i.semantic.value.tag=2 ∧
      (∃ decoded,SemanticPublicWire.parsePublic i.semantic.value.pubBytes=some decoded) ∧
      semanticRows 27 0 (slice i.stored 48 6983)=some (pre.records.val.map (fun s => bytesOf s.val)) ∧
      (∀ row, row<33 → LiteralTranscript.valid row (i.proof row)) ∧
      (∃ bound : ∀ row,(rowBytes ⟨i.stored,pre.records.val.map (fun s => bytesOf s.val)⟩ row).length ≤ SelectedTranscriptParams.D,
        ∀ row,LiteralTranscript.erase (i.proof row)=
          if row=0 then .initial (decodeState pre.c1_root)
          else .payload ⟨rowBytes ⟨i.stored,pre.records.val.map (fun s => bytesOf s.val)⟩ row,bound row⟩) ∧
      bytes (decodeState pre.c1_root)=slice i.stored 16 32 := by
  obtain ⟨f,s,log,cuts,recorded,ran⟩ := RawJ_RecordCuts.native _ native1 native2 hashv extraction
    id accounts1 accounts2 data1 data2 slot saved accepted1 accepted2
  have shape := Op3I_Cuts.same_cut_header adapter
    (Op5T_Concrete.current (Uni_Install.base ops reserved query geo)) B std
    accounts1 accounts2 saved f s cuts
  have header := shape.2.2.1
  have length : f.proof.val.length=57607 := by
    simpa only [bytesOf,List.length_map] using ((OraclePortHeader.accepts_iff _).mp header).1
  obtain ⟨run,properties⟩ := Uni_Cuts.tx1 adapter ops reserved query geo B std
    accounts1 accounts2 saved f s cuts length
  have inputCuts : SourceCuts (ClaimsUnrolledSdk.sdkOps adapter
      (Tx1Q_SameCut.dictionary (Op5T_Concrete.current ops) reserved query geo) B std)
      accounts1 accounts2 saved f s := by simpa only [Uni_Install.compose_tx1] using cuts
  exact ⟨f,s,log,cuts,recorded,ran,F3J_NativeInput.from_cut adapter (Op5T_Concrete.current ops)
    reserved query geo B std accounts1 accounts2 saved f s inputCuts recorded.1 run header w⟩

#print axioms native
end AspisR1.F3J_NativeConstruction
end
