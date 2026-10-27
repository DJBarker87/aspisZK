import Port5Q1_QueryPorts
import Port5Q1_FoldedData
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_ObservedOpening
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open AspisV8R19.DuplexFrames
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
abbrev FE := OraclePortCheckpointAbiC5.E
attribute [local irreducible] FoldedLeafCodec.decodeFolded

theorem quartet (ops : Ops) (decoder : Port5Q1_OpeningValues.SessionAS3 ops)
    (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : MatchingSupport.Data FE)
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some data)
    (wire : parsed.wire=bytesOf proof.val) (proofLength : proof.val.length=57607)
    (recovered : Nat → Option Bytes)
    (authenticated : ∀ pos, pos<22 → recovered (index q 2 pos)=
      some (OraclePortPackedChoiceC4.payload parsed 2 pos))
    (j : Fin 22) (position : a.next.val=j.val)
    (o : Port4C_QueryValues.Observation (Port4C_RowStd.install (Port5Q1_QueryPorts.install ops))
      proof p a out g obs geometry b bout) :
    bytesOf o.opening.val=opening parsed j.val ∧
      ∀ t, Port5Q1_OpeningValues.values o.values t=
        data.V (AspisR1.childIndex (AspisR1.parentIndex (n:=65536) (q j)) t) := by
  obtain ⟨view,run,size,bytes⟩ := Port4B_Opening.opening_exact proof proofLength a.next (by rw [position]; exact j.isLt)
  have same : view=o.opening := Result.ok.inj (run.symm.trans o.opening_read)
  have size1 : o.opening.val.length=832 := same ▸ size
  have bytes1 : bytesOf o.opening.val=opening parsed j.val := by
    rw [same,position,←wire] at bytes
    exact bytes
  have installedDecoder : Port5Q1_OpeningValues.SessionAS3
      (Port4C_RowStd.install (Port5Q1_QueryPorts.install ops)) := ⟨decoder.decode⟩
  have decoded := Port5Q1_OpeningValues.four
    (Port4C_RowStd.install (Port5Q1_QueryPorts.install ops)) installedDecoder o.opening size1 o.values o.values_read
  rw [bytes1] at decoded
  exact ⟨bytes1,Port5Q1_FoldedData.quartet parsed q tr data read recovered authenticated j _ decoded⟩

#print axioms quartet
end AspisR1.Port5Q1_ObservedOpening
end
