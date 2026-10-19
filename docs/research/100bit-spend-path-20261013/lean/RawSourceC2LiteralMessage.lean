import RawSourceC2WordBinding
import RawSourceGlobalOracleCoupling

/-! Install the pre-commitment C2 word in the actual row2 literal constructor.
The actual source sampler value/state and global full-word equality all refer
to the same source Call, parsed root, byte oracle and execution log. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawSourceC2LiteralMessage
open Aeneas Aeneas.Std Result AspisR1 AspisR1.TranscriptView
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open SourceDigestAddresses CanonicalCutEnrichedTranscript

def actualC2Word {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (values : SemanticPrefixCodec.Full) (c : SourceFull25.Call D pre)
    (tr : List (Bytes × State)) : LiteralTranscript.C2Word :=
  TypedRecoveredWords.c2Value (rawC2Map tr
    (CommitmentRootFrames.c2Frame (decodeState c.before.state) (SemanticPayloadView.rootAt2 values))
    (SemanticPayloadView.rootAt2 values))

theorem actual_row2_with_causal_word
    {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (values : SemanticPrefixCodec.Full)
    (hfull : SemanticPrefixCodec.encodeFull values = PrefixAdapter.completedRecords pre)
    (cs : List (SourceFull25.Call D pre)) (c : SourceFull25.Call D pre)
    (hc : c ∈ cs) (hrow : c.row.val = 2)
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hsource : SourceDigestLog.sourceLog cs ⊆ tr)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv RawByteCollisionTargets.pred Q) emptyTable tr)
    (hbound : (rawBytes c.record.framed).length ≤ SelectedTranscriptParams.params.D)
    (P : LiteralTranscript.Prefix)
    (hstate : UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix P) = decodeState c.before.state) :
    let mm : SelectedTranscriptParams.Message := ⟨rawBytes c.record.framed,hbound⟩
    let word := actualC2Word values c tr
    LiteralTranscript.valid 2 (.c2 mm word) ∧
      Value.ordinary (SourceLiteralTraceLift.sourceChallenge c) =
        (eval (fun a : Addr SelectedTranscriptParams.L => H a.toBytes)
          (LiteralTranscript.samp 2 P (.c2 mm word)).toProgram).2.1 ∧
      decodeState c.after.state =
        (eval (fun a : Addr SelectedTranscriptParams.L => H a.toBytes)
          (LiteralTranscript.samp 2 P (.c2 mm word)).toProgram).2.2 ∧
      word = TypedRecoveredWords.c2Value (fullC2Map tr (SemanticPayloadView.rootAt2 values)) := by
  let mm : SelectedTranscriptParams.Message := ⟨rawBytes c.record.framed,hbound⟩
  let word := actualC2Word values c tr
  have hsingle : SourceDigestLog.sourceLog [c] ⊆ tr := by
    intro q hq
    rcases List.mem_flatMap.mp hq with ⟨d,hd,hqd⟩
    simp only [List.mem_singleton] at hd
    subst d
    exact hsource (List.mem_flatMap.mpr ⟨c,hc,hqd⟩)
  have hD : ∀ d ∈ [c], (rawBytes d.record.framed).length ≤ SelectedTranscriptParams.D := by
    intro d hd
    simp only [List.mem_singleton] at hd
    subst d
    exact hbound
  have hstep := SourceGlobalOracleCoupling.call_simulates_literal_payload [c] c
    (by simp) H tr hsingle hcons hD 2 (by decide) (by decide) hrow P
    (.c2 mm word) mm rfl hstate rfl
  have hword := (RawSourceC2WordBinding.actual_c2_word_stable values hfull cs c hc hrow
    iv H tr Q hsource hcons hQ hout).2
  exact ⟨by trivial,hstep.1,hstep.2,hword⟩

#print axioms actual_row2_with_causal_word
end AspisR1PublicPreparation.RawSourceC2LiteralMessage
end
