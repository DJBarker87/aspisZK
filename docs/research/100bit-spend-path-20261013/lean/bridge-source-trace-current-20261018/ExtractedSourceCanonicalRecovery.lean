import ExtractedSourceTypedRecovery
import ExtractedSourceObservations
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.SourceCanonicalRecovery
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1 SelectedSourceRecords

private theorem frame_bound {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (c : SourceFull25.Call D pre)
    (h : (c.record.framed.val.map ExtractedRecordByteValue.rawByte).length ≤ 901) :
    (SourceDigestAddresses.rawBytes c.record.framed).length ≤ SelectedTranscriptParams.params.D := by
  change (SourceDigestAddresses.rawBytes c.record.framed).length ≤ 3717
  simp only [SourceDigestAddresses.rawBytes, List.length_map] at *
  omega

/-- A generic budget proof; no concrete transcript is reduced. -/
theorem firstReads_le_length {I A : Type} [DecidableEq I] (t : Table I A)
    (tr : List (I × A)) : firstReads t tr ≤ tr.length := by
  classical
  induction tr generalizing t with
  | nil => simp [firstReads]
  | cons q rest ih =>
    rcases q with ⟨a,v⟩
    have h := ih (put t a v)
    simp only [firstReads, List.length_cons]
    split <;> omega

/-- Recover the same actual25 records from their canonical observation
subtrace. The whole-trace version uses an explicit inclusion and its own
consistency/read-budget/no-hit premises. No runtime583-call equality appears. -/
theorem recover {Hash : Type} (D : aspis_core.Digest32 Hash) (hash : Hash)
    (pre : r1_wire.Prefix) (initial last : r1_wire.SemanticTranscript Hash)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32)
    (hnew : r1_wire.SemanticTranscript.new D hash pubInput root = ok (.Ok initial))
    (hL : 75 + (SourceDigestAddresses.rawBytes pubInput).length ≤ SelectedTranscriptParams.L)
    (hpub : (SourceDigestAddresses.rawBytes pubInput).length < 2^32)
    (cs : List (SourceFull25.Call D pre)) (run : SourceFull25.Trace D pre initial last cs)
    (hr : cs.map SourceFull25.Call.row = ActualFull25.rows)
    (bound : ∀ c ∈ cs, (c.record.framed.val.map ExtractedRecordByteValue.rawByte).length ≤ 901)
    (targetTag : U8) (targetFrame : Slice U8)
    (targetBound : (SourceDigestAddresses.rawBytes targetFrame).length ≤ SelectedTranscriptParams.params.D)
    (targetOutput : TranscriptStep.Bytes32)
    (targetDigest : D.digest last.hash (TranscriptStep.absorbParts last.state targetTag targetFrame) =
      ok targetOutput) :
    ∃ (length : U32) (target : Addr SelectedTranscriptParams.L)
      (tr : List (Addr SelectedTranscriptParams.L × State)),
      let H : Addr SelectedTranscriptParams.L → State := SourceDigestOracle.oracle D hash pubInput root length
      target = absorbA SelectedTranscriptParams.params (decodeState last.state) (decodeByte targetTag)
        (SourceDigestAddresses.rawBytes targetFrame) targetBound ∧
      tr = SourceObservations.relevant SelectedTranscriptParams.params cs
        (fun c hc => frame_bound c (bound c hc))
        (PublicInitFrame.addr (SourceDigestAddresses.rawBytes pubInput) hL (decodeState root),decodeState initial.state)
        (target,decodeState targetOutput) ∧
      tr.length = 77 ∧ (∀ q ∈ tr, q.2 = H q.1) ∧ Read tr target ∧
      ((¬ hitsBad (badColl SelectedTranscriptParams.params 77) emptyTable tr) →
        UnifiedSemanticRecovery.typed SelectedTranscriptParams.params
          (SourceDigestAddresses.rawBytes pubInput) (tableBefore emptyTable tr target) 25
            (decodeState last.state) = some (decodeState root,records cs bound)) ∧
      ∀ (whole : List (Addr SelectedTranscriptParams.L × State)) (Qtot : Nat),
        (∀ q ∈ tr, q ∈ whole) → (∀ q ∈ whole, q.2 = H q.1) →
        firstReads emptyTable whole ≤ Qtot →
        (¬ hitsBad (badColl SelectedTranscriptParams.params Qtot) emptyTable whole) →
        UnifiedSemanticRecovery.typed SelectedTranscriptParams.params
          (SourceDigestAddresses.rawBytes pubInput) (tableBefore emptyTable whole target) 25
            (decodeState last.state) = some (decodeState root,records cs bound) ∧ Read whole target := by
  obtain ⟨length,hhash,hinit,hrecover⟩ := SourceTypedRecovery.recover D hash pre initial last
    pubInput root hnew hL hpub cs run hr bound
  let H : Addr SelectedTranscriptParams.L → State := SourceDigestOracle.oracle D hash pubInput root length
  let target := absorbA SelectedTranscriptParams.params (decodeState last.state) (decodeByte targetTag)
    (SourceDigestAddresses.rawBytes targetFrame) targetBound
  let initialPair : SourceObservations.Observation SelectedTranscriptParams.L :=
    (PublicInitFrame.addr (SourceDigestAddresses.rawBytes pubInput) hL (decodeState root),decodeState initial.state)
  let targetPair : SourceObservations.Observation SelectedTranscriptParams.L := (target,decodeState targetOutput)
  let fb := fun c hc => frame_bound c (bound c hc)
  let tr := SourceObservations.relevant SelectedTranscriptParams.params cs fb initialPair targetPair
  have hhLast : last.hash = hash := (SourceDigestOracle.trace_hashes run).1.trans hhash
  have hd := targetDigest
  rw [hhLast] at hd
  have ht : targetPair.2 = H targetPair.1 := SourceDigestOracle.oracle_at D hash pubInput root length
    (.absorb last.state targetTag targetFrame) target targetOutput
    (SourceDigestAddresses.absorb_address SelectedTranscriptParams.params _ _ _ targetBound) hd
  have hcons : ∀ q ∈ tr, q.2 = H q.1 := by
    have h := SourceObservations.relevant_consistent SelectedTranscriptParams.params run fb pubInput root length
      initialPair targetPair (by simpa only [hhash] using hinit) (by simpa only [hhash] using ht)
    simpa only [hhash] using h
  have hlenCs : cs.length = 25 := by
    have h := (congrArg (List.map (fun row : U8 => row.val)) hr).trans ActualFull25.rows_schedule
    simpa only [List.length_map,List.length_range] using congrArg List.length h
  have hlen : tr.length = 77 := by
    rw [SourceObservations.relevant_length,hlenCs]
  have hi : Read tr initialPair.1 := SourceObservations.read_initial _ _ _ _ _
  have ha : Read tr target := SourceObservations.read_target _ _ _ _ _
  have hrs : ∀ (c : SourceFull25.Call D pre) (hc : c ∈ cs),
      Read tr (SourceTypedRecovery.absorbAddress c (bound c hc)) ∧
      Read tr (advanceA SelectedTranscriptParams.params (decodeState c.absorbed)) := by
    intro c hc
    constructor
    · exact SourceObservations.read_row _ cs fb initialPair targetPair c hc
        (SourceTypedRecovery.absorbAddress c (bound c hc),decodeState c.absorbed)
        (by simp [SourceObservations.row,SourceTypedRecovery.absorbAddress])
    · exact SourceObservations.read_row _ cs fb initialPair targetPair c hc
        (advanceA SelectedTranscriptParams.params (decodeState c.absorbed),decodeState c.after.state)
        (by simp [SourceObservations.row])
  have hp : target.toBytes.take 32 = bytes (decodeState last.state) := toBytes_absorbA _ _ _ _ _
  refine ⟨length,target,tr,rfl,rfl,hlen,hcons,ha,?_,?_⟩
  · intro nohit
    exact hrecover tr 77 target hcons (by simpa only [hlen] using firstReads_le_length emptyTable tr)
      nohit hi hrs ha hp
  · intro whole Qtot included consistent budget nohit
    have haWhole := SourceObservations.read_in_whole tr whole included target ha
    refine ⟨hrecover whole Qtot target consistent budget nohit
      (SourceObservations.read_in_whole tr whole included initialPair.1 hi) ?_ haWhole hp,haWhole⟩
    intro c hc
    exact ⟨SourceObservations.read_in_whole tr whole included _ (hrs c hc).1,
      SourceObservations.read_in_whole tr whole included _ (hrs c hc).2⟩

#print axioms firstReads_le_length
#print axioms recover
end AspisR1PublicPreparation.SourceCanonicalRecovery
end
