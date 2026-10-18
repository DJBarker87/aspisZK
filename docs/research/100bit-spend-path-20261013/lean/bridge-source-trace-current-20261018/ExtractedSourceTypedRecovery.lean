import ExtractedSourceTypedRecords
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.SourceTypedRecovery
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1 SelectedSourceRecords SourceTypedRecords

private theorem source_bound {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (c : SourceFull25.Call D pre)
    (h : (c.record.framed.val.map ExtractedRecordByteValue.rawByte).length ≤ 901) :
    (SourceDigestAddresses.rawBytes c.record.framed).length ≤ SelectedTranscriptParams.params.D := by
  change (SourceDigestAddresses.rawBytes c.record.framed).length ≤ 3717
  simp only [SourceDigestAddresses.rawBytes, List.length_map] at *
  omega

def absorbAddress {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (c : SourceFull25.Call D pre)
    (h : (c.record.framed.val.map ExtractedRecordByteValue.rawByte).length ≤ 901) :
    Addr SelectedTranscriptParams.L :=
  absorbA SelectedTranscriptParams.params (decodeState c.before.state) (decodeByte c.tag)
    (SourceDigestAddresses.rawBytes c.record.framed) (source_bound c h)

theorem messageAt_bytes {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre))
    (bound : ∀ c ∈ cs, (c.record.framed.val.map ExtractedRecordByteValue.rawByte).length ≤ 901)
    (j : Nat) (hj : j < cs.length) :
    SelectedTranscriptParams.params.enc (messageAt cs bound j) =
      SourceDigestAddresses.rawBytes cs[j].record.framed := by
  change (messageAt cs bound j).val = _
  simp only [messageAt, dif_pos hj, message]
  rfl

theorem label_at {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre))
    (hr : cs.map SourceFull25.Call.row = ActualFull25.rows) (j : Nat) (hj : j < cs.length) :
    SelectedTranscriptParams.params.lbl j = decodeByte cs[j].tag := by
  have hrow := SelectedSourceAgreement.row_at cs hr j hj
  apply Fin.ext
  change (SelectedTranscriptParams.label j).val = _
  rw [SelectedTranscriptParams.label_val j (by omega)]
  have ht := cs[j].tag_code
  rw [cs[j].record_row, hrow.1] at ht
  exact ht.symm

/-- Whole-trace form. The actual source constructor supplies initialization
and the D-derived H; source Calls supply all transition equations. Only the
whole trace's consistency/read budget/no-hit and membership of those actual
observations are external. There is no typed-success premise. -/
theorem recover {Hash : Type} (D : aspis_core.Digest32 Hash) (hash : Hash)
    (pre : r1_wire.Prefix) (initial last : r1_wire.SemanticTranscript Hash)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32)
    (hnew : r1_wire.SemanticTranscript.new D hash pubInput root = ok (.Ok initial))
    (hL : 75 + (SourceDigestAddresses.rawBytes pubInput).length ≤ SelectedTranscriptParams.L)
    (hpub : (SourceDigestAddresses.rawBytes pubInput).length < 2^32)
    (cs : List (SourceFull25.Call D pre)) (run : SourceFull25.Trace D pre initial last cs)
    (hr : cs.map SourceFull25.Call.row = ActualFull25.rows)
    (bound : ∀ c ∈ cs, (c.record.framed.val.map ExtractedRecordByteValue.rawByte).length ≤ 901) :
    ∃ length : U32,
      let H : Addr SelectedTranscriptParams.L → State :=
        SourceDigestOracle.oracle D hash pubInput root length
      initial.hash = hash ∧
      decodeState initial.state = H (PublicInitFrame.addr
        (SourceDigestAddresses.rawBytes pubInput) hL (decodeState root)) ∧
      ∀ (tr : List (Addr SelectedTranscriptParams.L × State)) (Qtot : Nat)
        (target : Addr SelectedTranscriptParams.L),
        (∀ q ∈ tr, q.2 = H q.1) → firstReads emptyTable tr ≤ Qtot →
        (¬ hitsBad (badColl SelectedTranscriptParams.params Qtot) emptyTable tr) →
        Read tr (PublicInitFrame.addr (SourceDigestAddresses.rawBytes pubInput) hL (decodeState root)) →
        (∀ (c : SourceFull25.Call D pre) (hc : c ∈ cs),
          Read tr (absorbAddress c (bound c hc)) ∧
          Read tr (advanceA SelectedTranscriptParams.params (decodeState c.absorbed))) →
        Read tr target → target.toBytes.take 32 = bytes (decodeState last.state) →
        UnifiedSemanticRecovery.typed SelectedTranscriptParams.params
          (SourceDigestAddresses.rawBytes pubInput) (tableBefore emptyTable tr target) 25
            (decodeState last.state) = some (decodeState root, records cs bound) := by
  obtain ⟨length,state,hlen,hd,hout⟩ := TranscriptStep.new_success D hash pubInput root initial hnew
  refine ⟨length, by rw [hout], ?_, ?_⟩
  · have hi := SourceDigestOracle.oracle_at D hash pubInput root length .initial _ state
      (SourceDigestAddresses.init_address _ _ _ (SourceDigestAddresses.successful_length _ _ hlen) hL) hd
    simpa only [hout] using hi
  intro tr Qtot target hcons hQ hnohit hinitRead hreads htargetRead htargetBytes
  let H : Addr SelectedTranscriptParams.L → State := SourceDigestOracle.oracle D hash pubInput root length
  have hhash : initial.hash = hash := by rw [hout]
  have hfun := SourceDigestOracle.trace_functional SelectedTranscriptParams.params run pubInput root length
    (fun c hc => source_bound c (bound c hc))
  rw [hhash] at hfun
  have hcount : cs.length = 25 := by
    have h := (congrArg (List.map (fun row : U8 => row.val)) hr).trans ActualFull25.rows_schedule
    simpa only [List.length_map, List.length_range] using congrArg List.length h
  have hroot : states initial cs 0 = H (PublicInitFrame.addr
      (SourceDigestAddresses.rawBytes pubInput) hL (decodeState root)) := by
    have hi := SourceDigestOracle.oracle_at D hash pubInput root length .initial _ state
      (SourceDigestAddresses.init_address _ _ _ (SourceDigestAddresses.successful_length _ _ hlen) hL) hd
    simpa only [states, SourceTraceIndices.zero, hout] using hi
  have habs : ∀ j < cs.length, absorbed cs j = H (absorbA SelectedTranscriptParams.params
      (states initial cs j) (SelectedTranscriptParams.params.lbl j)
      (SelectedTranscriptParams.params.enc (messageAt cs bound j))
      (SelectedTranscriptParams.params.encLen (messageAt cs bound j))) := by
    intro j hj
    simpa only [states_before run j hj, messageAt_bytes cs bound j hj, label_at cs hr j hj,
      absorbed, List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some] using
      (hfun cs[j] (List.getElem_mem hj)).1
  have hstep : ∀ j < cs.length, states initial cs (j+1) =
      H (advanceA SelectedTranscriptParams.params (absorbed cs j)) := by
    intro j hj
    rw [states_after initial cs j hj]
    simpa only [absorbed, List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some] using
      (hfun cs[j] (List.getElem_mem hj)).2.2
  have har : ∀ j < cs.length, Read tr (absorbA SelectedTranscriptParams.params
      (states initial cs j) (SelectedTranscriptParams.params.lbl j)
      (SelectedTranscriptParams.params.enc (messageAt cs bound j))
      (SelectedTranscriptParams.params.encLen (messageAt cs bound j))) := by
    intro j hj
    simpa only [states_before run j hj, messageAt_bytes cs bound j hj, label_at cs hr j hj,
      absorbAddress] using (hreads cs[j] (List.getElem_mem hj)).1
  have hdr : ∀ j < cs.length,
      Read tr (advanceA SelectedTranscriptParams.params (absorbed cs j)) := by
    intro j hj
    simpa only [absorbed, List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some] using
      (hreads cs[j] (List.getElem_mem hj)).2
  have hend : states initial cs cs.length = decodeState last.state :=
    congrArg (fun (t : r1_wire.SemanticTranscript Hash) => decodeState t.state)
      (SourceTraceIndices.endpoint run)
  have hp : target.toBytes.take 32 = bytes (states initial cs cs.length) := by
    rw [hend]; exact htargetBytes
  have hw := InitialWalkTrace.walk_before_next SelectedTranscriptParams.params
    (SourceDigestAddresses.rawBytes pubInput) hpub hL (decodeState root) H tr Qtot hcons hQ hnohit
    cs.length cs.length (by omega) (by omega)
    (states initial cs) (absorbed cs) SelectedTranscriptParams.params.lbl
    (fun j => SelectedTranscriptParams.params.enc (messageAt cs bound j))
    (fun j => SelectedTranscriptParams.params.encLen (messageAt cs bound j))
    hroot hinitRead habs hstep har hdr target htargetRead hp
  rw [hend] at hw
  change (InitialWalk.walk SelectedTranscriptParams.params
    (SourceDigestAddresses.rawBytes pubInput) (tableBefore emptyTable tr target) 25
      (decodeState last.state)).bind _ = _
  rw [← hcount, hw, Option.bind_some]
  dsimp only
  rw [raw_decode run bound]
  rfl

#print axioms absorbAddress
#print axioms messageAt_bytes
#print axioms label_at
#print axioms recover
end AspisR1PublicPreparation.SourceTypedRecovery
end
