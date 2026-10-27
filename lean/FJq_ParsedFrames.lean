import FJq_ParsedRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_ParsedFrames
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open Aeneas Aeneas.Std AspisR1PublicPreparation
open MultiproofConeCanonical OraclePortCompactDraft OraclePortStoredDecisionDraftC4
/-- Complete typed source frames and literal frames on the SAME physical
parser result. No independent equality of their decoded polynomials is assumed. -/
theorem value (stored : Bytes) (tr : RawCutTranscriptRun.ErasedPrefix) (p : Parsed)
    (parsed : OraclePortStoredParserC4.parseReached stored tr=some p)
    (q : Fin 22 → Fin 262144) (pre : r1_wire.Prefix) (values : SemanticPrefixCodec.Full)
    (full : SemanticPrefixCodec.encodeFull values=PrefixAdapter.completedRecords pre)
    (records : p.semantic=pre.records.val.map (fun s=>bytesOf s.val)) :
    SemanticPrefixCodec.encodeFull values=
      LiteralSemanticCodecBridge.records ((typedRows p q tr).take 25) := by
  rw [PAln_Records.records_take p q tr (OraclePortStoredParserC4.parsed _ _ _ parsed).2.2
    (FJq_ParsedRows.value stored tr p parsed),records]
  have completed : PrefixAdapter.completedRecords pre=
      (pre.records.val.map (fun s=>bytesOf s.val)).take 25 := by
    simp only [PrefixAdapter.completedRecords,List.map_take]
    rfl
  exact full.trans completed
#print axioms value
end AspisR1.FJq_ParsedFrames
end
