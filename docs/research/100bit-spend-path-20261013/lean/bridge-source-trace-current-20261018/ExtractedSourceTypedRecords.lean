import ExtractedSourceTraceIndices
import R1UnifiedSemanticRecoveryCore
import R1InitialWalkTrace
import ExtractedSelectedSourceAgreement
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.SourceTypedRecords
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1 SelectedSourceRecords

abbrev Message := SelectedTranscriptParams.Message

def states {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (initial : r1_wire.SemanticTranscript Hash) (cs : List (SourceFull25.Call D pre))
    (j : Nat) : State := decodeState (SourceTraceIndices.stateAt initial cs j).state

def absorbed {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre)) (j : Nat) : State :=
  (cs[j]?).map (fun c => decodeState c.absorbed) |>.getD 0

def messageAt {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre))
    (bound : ∀ c ∈ cs, (c.record.framed.val.map ExtractedRecordByteValue.rawByte).length ≤ 901)
    (j : Nat) : Message :=
  if h : j < cs.length then message cs[j] (bound cs[j] (List.getElem_mem h))
  else ⟨[], by simp [SelectedTranscriptParams.D]⟩

theorem states_before {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    {initial last : r1_wire.SemanticTranscript Hash} {cs : List (SourceFull25.Call D pre)}
    (run : SourceFull25.Trace D pre initial last cs) (j : Nat) (hj : j < cs.length) :
    states initial cs j = decodeState cs[j].before.state := by
  exact congrArg (fun t => decodeState t.state)
    (SourceTraceIndices.get_before run j cs[j] (List.getElem?_eq_getElem hj))

theorem states_after {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (initial : r1_wire.SemanticTranscript Hash) (cs : List (SourceFull25.Call D pre))
    (j : Nat) (hj : j < cs.length) :
    states initial cs (j+1) = decodeState cs[j].after.state := by
  exact congrArg (fun t => decodeState t.state)
    (SourceTraceIndices.get_after initial cs j cs[j] (List.getElem?_eq_getElem hj))

/-- The raw decoder's typed records are exactly the same source-constructed
records, including their actual carried endpoint states. -/
theorem recs_eq_records {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    {initial last : r1_wire.SemanticTranscript Hash} {cs : List (SourceFull25.Call D pre)}
    (run : SourceFull25.Trace D pre initial last cs)
    (bound : ∀ c ∈ cs, (c.record.framed.val.map ExtractedRecordByteValue.rawByte).length ≤ 901) :
    RawRoundCompletion.recs (states initial cs) (absorbed cs) (messageAt cs bound)
      (fun j => states initial cs (j+1)) cs.length = records cs bound := by
  apply List.ext_getElem
  · simp [RawRoundCompletion.recs, records]
  · intro j hj hk
    have hcs : j < cs.length := by simpa [records] using hk
    simp only [RawRoundCompletion.recs, List.getElem_map, List.getElem_range,
      records, List.getElem_attach]
    rw [states_before run j hcs, states_after initial cs j hcs]
    simp only [absorbed, List.getElem?_eq_getElem hcs, Option.map_some, Option.getD_some,
      messageAt, dif_pos hcs]

theorem raw_decode {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    {initial last : r1_wire.SemanticTranscript Hash} {cs : List (SourceFull25.Call D pre)}
    (run : SourceFull25.Trace D pre initial last cs)
    (bound : ∀ c ∈ cs, (c.record.framed.val.map ExtractedRecordByteValue.rawByte).length ≤ 901) :
    RawRoundDecode.decode SelectedTranscriptParams.params 0
      (InitialWalk.records (states initial cs) (absorbed cs) SelectedTranscriptParams.params.lbl
        (fun j => SelectedTranscriptParams.params.enc (messageAt cs bound j)) cs.length) =
      some (records cs bound) := by
  rw [RawRoundCompletion.decode_records, recs_eq_records run bound]

#print axioms states
#print axioms absorbed
#print axioms messageAt
#print axioms states_before
#print axioms states_after
#print axioms recs_eq_records
#print axioms raw_decode
end AspisR1PublicPreparation.SourceTypedRecords
end
