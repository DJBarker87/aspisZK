import Port6AUTH_Accounting
import Port6AUTH_Frames
import OraclePortFrozen2ActualChecks
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6AUTH_SourceCut
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4 OraclePortRuntimeBindingC7
open Port1_StoredCarrier Port6AUTH_Prefix
attribute [local irreducible] originalWith canon lift source LiteralByteProtocol.protocol

/-- Exactly the record fed into source annotation, not the later two-pass log. -/
abbrev first (rust : Verifier) (P : ByteProver) (H : Bytes → State) :=
  eval H (originalWith rust (canon (lift P)))

theorem first_pass_prefix (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : ByteProver) (H : Bytes → State) :
    ∃ tail, (eval H (source D rust P)).1=(first rust P H).1 ++ tail := by
  rw [source_eval,OraclePortFrozen2Join.annotatedWith_eval]
  exact ⟨_,rfl⟩

/-- Collision exclusion on the charged full source record also covers the
first pass used to build words. No second collision event is introduced. -/
theorem clean_first (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : ByteProver) (Q : Nat)
    (H : Bytes → State)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable (eval H (source D rust P)).1) :
    ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable (first rust P H).1 := by
  obtain ⟨tail,eq⟩ := first_pass_prefix D rust P H
  rw [eq] at clean
  exact fun h => clean (TraceAppend.hitsBad_of_prefix _ _ _ _ h)

theorem budget (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : ByteProver) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) (physical : Physical rust)
    (calls : ∀ H i, (eval H (rust i)).1.length ≤ 1161) (H : Bytes → State) :
    firstReads emptyTable (first rust P H).1 ≤ Q+1161 := by
  rw [← Port6AUTH_Accounting.first_reads D rust P physical H]
  exact Port6AUTH_Accounting.budget D rust P Q hq physical calls H

/-- Reconstruct the actual sampler transcript from the FIRST source record.
The producer contract is only source sampler read containment. -/
theorem frame_eq (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : ByteProver) (H : Bytes → State)
    (contains : ∀ a, Read (eval H (RawCutProverCompiler.verifier D (fun _ _ => false)
      (first rust P H).2.1.statement (first rust P H).2.1.proof)).1 a → Read (first rust P H).1 a)
    (row : Nat) (bound : row ≤ 33) :
    RawCutWordsFromView.frameFromView D (view (first rust P H)) row=
      RawCutWordsFromView.frame D H (first rust P H).2.1.statement (first rust P H).2.1.proof row := by
  unfold RawCutWordsFromView.frameFromView RawCutWordsFromView.frame FS2.Protocol.chain
  have transcript := OracleProgramReplay.transcript_eq_of_agrees (LiteralByteProtocol.protocol D)
    (RawCutTranscriptRun.decisionOnBytes (fun _ _ => false)) H
    (OracleProgramReplay.oracleOf (first rust P H).1)
    (first rust P H).2.1.statement (first rust P H).2.1.proof
    (fun a ha => OracleProgramReplay.oracleOf_eq H _
      (FS.eval_consistent H (originalWith rust (canon (lift P)))) a (contains a ha)) row bound
  change _ = _ at transcript
  rw [transcript]

#print axioms first_pass_prefix
#print axioms clean_first
#print axioms budget
#print axioms frame_eq
end AspisR1.Port6AUTH_SourceCut
end
