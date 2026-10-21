import OraclePortFrozen2Reached
import OraclePortFrameShapesC6
import OraclePortParsedRootsC6
import OraclePortRootBytesC6

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace AspisR1.OraclePortFrozen2Roots
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open OraclePortStoredExperimentC4 OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortFrozen2Reached
attribute [local irreducible] LiteralByteProtocol.protocol LiteralByteSampler.samp

def frameRow (k : Fin 3) : Nat := if k.val = 0 then 0 else if k.val = 1 then 2 else 30
def frames (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) (k : Fin 3) : Bytes :=
  RawCutWordsFromView.frameFromView D (view (run D P H)) (frameRow k)
def selectors (k : Fin 3) : Fin 5 := if k.val = 2 then 3 else 2

theorem erased_index (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (row : Nat) (bound : row < 33) : ∃ c,
      (reached D P H).rounds[row]? = some (LiteralTranscript.erase ((input P H).proof row),c) := by
  refine ⟨(eval H (LiteralByteSampler.samp row
    ((LiteralByteProtocol.protocol D).transcript H (input P H).statement (input P H).proof row)
    ((input P H).proof row)).toProgram).2,?_⟩
  simp only [reached,LiteralTranscript.erasePrefix,transcript,List.getElem?_map,
    LiteralByteRunFacts.transcript_index D H (input P H).statement (input P H).proof 33 row bound,
    Option.map_some]

/-- All three root predicates are bound to the actual reached parser and its
actual sampler frames. No external frame/root identity remains. -/
theorem targets (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (ha : (run D P H).2.2 = true) (p : Parsed) (q : Fin 22 → Fin 262144)
    (parsed : OraclePortStoredParserC4.parseReached (input P H).stored (reached D P H) = some p)
    (query : queries (reached D P H) = some q) :
    ∀ k : Fin 3, BinRawByteCollisionTargets.pred (selectors k) (frames D P H k) =
      some (committedRoot p k.val) := by
  obtain ⟨_,p',q',i,hp,hq,_,_,checked⟩ := OraclePortFrozen2.accepted_details _ _ _ H
    (OraclePortFrozen2Reached.accepted D P H ha)
  have psame : p' = p := Option.some.inj (hp.symm.trans parsed)
  have qsame : q' = q := Option.some.inj (hq.symm.trans query)
  subst p'; subst q'
  have matching := D0TypedChecks.accepted_matching _ i checked
  have aligned := (OraclePortStoredParserC4.parsed _ _ p parsed).2.2
  obtain ⟨_,_,_,⟨root0,c0,row0,bytes0⟩,rows⟩ := aligned
  obtain ⟨c0',at0⟩ := erased_index D P H 0 (by decide)
  have msg0 : LiteralTranscript.erase ((input P H).proof 0) = .initial root0 :=
    congrArg Prod.fst (Option.some.inj (at0.symm.trans row0))
  have root0same := OraclePortRootBytesC6.initial p root0 bytes0.symm
  have h0 : BinRawByteCollisionTargets.pred 2 (frames D P H 0) = some (committedRoot p 0) := by
    change BinRawByteCollisionTargets.pred 2 (RawCutWordsFromView.frameFromView D (view (run D P H)) 0) = _
    rw [OraclePortStoredProjectionC4.frame_eq D decision P H 0 (by decide),root0same]
    exact OraclePortFrameShapesC6.initial_target D H _ _ root0 msg0
  obtain ⟨b2,c2,row2,bytes2⟩ := rows 2 (by decide) (by decide)
  obtain ⟨c2',at2⟩ := erased_index D P H 2 (by decide)
  have msg2 : LiteralTranscript.erase ((input P H).proof 2) = .payload b2 :=
    congrArg Prod.fst (Option.some.inj (at2.symm.trans row2))
  obtain ⟨root1,encoded2⟩ := OraclePortParsedRootsC6.c2_record p q (reached D P H) i.data matching b2 c2 row2
  have record2 : p.semantic[2]?.getD [] = b2.val := by
    simpa only [rowBytes,show (2:Nat) < 27 by decide,ite_true] using bytes2.symm
  have root1same := OraclePortRootBytesC6.second p root1 (record2.trans encoded2)
  have h1 : BinRawByteCollisionTargets.pred 2 (frames D P H 1) = some (committedRoot p 1) := by
    change BinRawByteCollisionTargets.pred 2 (RawCutWordsFromView.frameFromView D (view (run D P H)) 2) = _
    rw [OraclePortStoredProjectionC4.frame_eq D decision P H 2 (by decide),root1same]
    rw [OraclePortFrameShapesC6.ordinary D H _ _ 2 (by decide) (by decide) (by decide) b2 msg2,
      OraclePortFrameShapesC6.absorb_bytes,encoded2,BinRawByteCollisionTargets.pred_tail]
    change BinRawByteCollisionTargets.trailing
      (_ ++ [0,SelectedTranscriptParams.label 2] ++ RecordFrameCodec.frame 1 (bytes root1)) = some root1
    simpa only [RecordFrameCodec.frame,List.append_assoc] using
      BinRawByteCollisionTargets.trailing_frame
        (bytes (UnifiedSampler.stateOf SelectedTranscriptParams.params
          (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H
            (input P H).statement (input P H).proof 2))) ++ [0,SelectedTranscriptParams.label 2] ++
          RecordFrameCodec.header 1 (bytes root1).length) root1
  obtain ⟨b30,c30,row30,bytes30⟩ := rows 30 (by decide) (by decide)
  obtain ⟨c30',at30⟩ := erased_index D P H 30 (by decide)
  have msg30 : LiteralTranscript.erase ((input P H).proof 30) = .payload b30 :=
    congrArg Prod.fst (Option.some.inj (at30.symm.trans row30))
  obtain ⟨payload,encoded30⟩ := OraclePortParsedRootsC6.folded_record p q (reached D P H) i.data matching b30 c30 row30
  have root2same := OraclePortRootBytesC6.folded p payload (bytes30.symm.trans encoded30)
  have h2 : BinRawByteCollisionTargets.pred 3 (frames D P H 2) = some (committedRoot p 2) := by
    change BinRawByteCollisionTargets.pred 3 (RawCutWordsFromView.frameFromView D (view (run D P H)) 30) = _
    rw [OraclePortStoredProjectionC4.frame_eq D decision P H 30 (by decide),root2same]
    rw [OraclePortFrameShapesC6.ordinary D H _ _ 30 (by decide) (by decide) (by decide) b30 msg30,
      OraclePortFrameShapesC6.absorb_bytes,encoded30,BinRawByteCollisionTargets.pred_middle]
    let state := UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H
        (input P H).statement (input P H).proof 30))
    let tail := SelectedFieldSequenceCodec.encodeWide payload.2
    let pre := bytes state ++ [0,SelectedTranscriptParams.label 30] ++
      PublicInitFrame.lengthBytes (bytes payload.1 ++ tail).length
    have prelen : pre.length = 38 := by
      simp only [pre,List.length_append,bytes_length,List.length_cons,List.length_nil,PublicInitFrame.lengthBytes_length]
    have encode : OpeningRecordCodec.encode payload =
        LengthFrameCodec.frame (bytes payload.1 ++ SelectedFieldSequenceCodec.encodeWide payload.2) := by
      cases payload
      rfl
    simpa only [encode,LengthFrameCodec.frame,pre,tail,state,OraclePortFrozen2Reached.input,List.append_assoc] using
      BinRawByteCollisionTargets.fixed_frame 38 pre payload.1 tail prelen
  intro k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2

#print axioms erased_index
#print axioms targets
end AspisR1.OraclePortFrozen2Roots
end
