import ExtractedSelectedSourceRecords
import ExtractedSourceSemanticSampler
import ExtractedSourceDigestOracle
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.SelectedSourceAgreement
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1 SelectedSourceRecords

abbrev Message := SelectedTranscriptParams.Message

def sourceChallenge (q : aspis_core.field.QM31) : AspisWideTower.WideExact :=
  algebraMap AspisV8R15.ExactTowerBase.QM31Exact AspisWideTower.WideExact
    (ExtractedCurrentQM31Exact.decode
      (ExtractedQM31SamplerCarrier.toCurrent (SamplerTransport.toOld q)))

theorem table_getD (H : Addr SelectedTranscriptParams.L → State)
    (T : Table (Addr SelectedTranscriptParams.L) State)
    (hc : ∀ a v, T a = some v → v = H a) (a : Addr SelectedTranscriptParams.L) :
    (T a).getD (H a) = H a := by
  cases he : T a with
  | none => rfl
  | some v => simpa only [Option.getD_some] using hc a v he

theorem pairs_challenge_at (T : Table (Addr SelectedTranscriptParams.L) State)
    (H : Addr SelectedTranscriptParams.L → State) (rs : List (Rec Message))
    (offset i : Nat) (hi : i < rs.length) :
    ((SelectedCompletedSemantic.pairs T H offset rs).map Prod.snd)[i]'(by
      simpa [SelectedCompletedSemantic.pairs, completeRounds_length] using hi) =
      SelectedTranscriptParams.params.σ (offset + i)
        ((T (squeezeA SelectedTranscriptParams.params rs[i].2.1)).getD
          (H (squeezeA SelectedTranscriptParams.params rs[i].2.1))) := by
  induction rs generalizing offset i with
  | nil => simp at hi
  | cons r rs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa [SelectedCompletedSemantic.pairs, completeRounds, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using ih (offset + 1) i (by simpa using hi)

theorem row_at {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre))
    (hr : cs.map SourceFull25.Call.row = ActualFull25.rows)
    (i : Nat) (hi : i < cs.length) : cs[i].row.val = i ∧ i < 25 := by
  have hs : cs.map (fun c => c.row.val) = List.range 25 := by
    calc
      _ = (cs.map SourceFull25.Call.row).map (fun row => row.val) := by
        simp only [List.map_map, Function.comp_def]
      _ = ActualFull25.rows.map (fun row => row.val) := congrArg _ hr
      _ = _ := ActualFull25.rows_schedule
  have hl : cs.length = 25 := by simpa using congrArg List.length hs
  have hi25 : i < 25 := by omega
  have he := congrArg (fun xs : List Nat => xs[i]?.getD 0) hs
  exact ⟨by simpa [hi, hi25] using he, hi25⟩

/-- Completed challenges on a consistent table are the exact reached source q
values. H is constructed from D, not supplied as a sampler/oracle law. -/
theorem source_completed_qs {Hash : Type} {D : aspis_core.Digest32 Hash}
    {pre : r1_wire.Prefix} {before after : r1_wire.SemanticTranscript Hash}
    (cs : List (SourceFull25.Call D pre)) (run : SourceFull25.Trace D pre before after cs)
    (hr : cs.map SourceFull25.Call.row = ActualFull25.rows)
    (bound : ∀ c ∈ cs, (c.record.framed.val.map ExtractedRecordByteValue.rawByte).length ≤ 901)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (T : Table (Addr SelectedTranscriptParams.L) State)
    (hc : ∀ a v, T a = some v → v =
      SourceDigestOracle.oracle D before.hash pubInput root length a) :
    (SelectedCompletedSemantic.pairs T
      (SourceDigestOracle.oracle D before.hash pubInput root length) 0
        (SelectedSourceRecords.records cs bound)).map Prod.snd =
      cs.map (fun c => sourceChallenge c.q) := by
  let H : Addr SelectedTranscriptParams.L → State :=
    SourceDigestOracle.oracle D before.hash pubInput root length
  have hfun := SourceDigestOracle.trace_functional SelectedTranscriptParams.params run
    pubInput root length (fun c hmem => by
      change (SourceDigestAddresses.rawBytes c.record.framed).length ≤ 3717
      have hb := bound c hmem
      change (c.record.framed.val.map ExtractedRecordByteValue.rawByte).length ≤ 901 at hb
      simp only [SourceDigestAddresses.rawBytes, List.length_map] at *
      omega)
  apply List.ext_getElem
  · simp [SelectedCompletedSemantic.pairs, SelectedSourceRecords.records,
      completeRounds_length]
  · intro i hi hj
    have hics : i < cs.length := by simpa using hj
    have hmem : cs[i] ∈ cs := List.getElem_mem hics
    have hrow := row_at cs hr i hics
    have hread := (hfun cs[i] hmem).2.1
    rw [pairs_challenge_at T _ _ 0 i (by
      simpa [SelectedSourceRecords.records] using hics)]
    simp only [SelectedSourceRecords.records, List.getElem_map, List.getElem_attach]
    rw [Nat.zero_add, table_getD _ _ hc,
      SelectedTranscriptParams.params_sigma, SelectedChallengeMap.semantic_row i hrow.2]
    rw [← hread]
    exact (SourceSemanticSampler.call_semChal cs[i]).symm

#print axioms sourceChallenge
#print axioms table_getD
#print axioms pairs_challenge_at
#print axioms row_at
#print axioms source_completed_qs
end AspisR1PublicPreparation.SelectedSourceAgreement
end
