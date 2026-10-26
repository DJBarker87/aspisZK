import F3T_Semantic
import F3T_RootAgreement
import F3T_Carried
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_InputAgreement
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open F3T_ByteCarrier F3T_Carried MultiproofConeCanonical OraclePortCompactDraft

theorem from_source_rows {F C : Type} (c : DrvC_Installation.Configuration F C)
    (pub proof : Slice U8) (v : Port1_Driver.Semantic) (encoded : alloc.vec.Vec U8)
    (decode : Port1_Driver.decodeSemantic (DrvC_Installation.sdk c) pub=ok (some v))
    (serialized : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (AspisR1CurrentCaller.FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic v))=ok (.Ok encoded))
    (semantic : LiteralTranscript.Public) (semBytes : semantic.pubBytes=bytesOf encoded.val) (tag : semantic.tag=2)
    (p : Parsed) (parsed : parse (bytesOf proof.val)=some p) (root : State)
    (rootBytes : bytes root=root0 p) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (wire : p.wire=bytesOf proof.val) :
    Carried c (F3J_InputRows.input p root w bound semantic (bytesOf pub.val)) := by
  have fit : 75+(bytesOf encoded.val).length≤SelectedTranscriptParams.L := by
    rw [← semBytes];exact semantic.initFits
  have sem := F3T_Semantic.from_serialization c pub proof v encoded decode serialized fit
  refine ⟨⟨bytesOf pub.val,bytesOf proof.val⟩,?_,rfl,wire,?_⟩
  · congr 1
    cases semantic
    simp only at semBytes tag
    cases (input c ⟨bytesOf pub.val,bytesOf proof.val⟩).semantic.value
    simp only at sem
    congr <;> first | exact semBytes.trans sem.1.symm | exact tag.trans sem.2.symm
  · intro row
    exact F3T_ProofCarriers.from_parse _ p parsed root w bound (F3T_RootAgreement.from_bytes p root rootBytes) row

#print axioms from_source_rows
end AspisR1.F3T_InputAgreement
end
