import AcceptedAdaptiveFiatShamir
import RawAdaptiveCompiledCompletion
import RawCutCompilerLaw

/-! Package actual public-free decoder completion into the adaptive first-read
interface. Formatting is required only when the original verifier accepts.
The collision mass is the existing unrestricted-byte, eleven-target bound.
Source acceptance-to-formatting and the total read budget remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawAdaptiveDecoderInjection
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound

def CommitmentMessages (pf : LiteralProtocol.Proof) : Prop :=
  ∃ (r1 : State) (w1 : LiteralTranscript.C1Word)
    (b2 : LiteralTranscript.BytesMessage) (w2 : LiteralTranscript.C2Word) (r2 : State)
    (b30 : LiteralTranscript.BytesMessage) (w30 : LiteralTranscript.VWord)
    (v30 : OpeningRecordCodec.Payload .second),
    pf 0 = .initial r1 w1 ∧ pf 2 = .c2 b2 w2 ∧ pf 30 = .second b30 w30 ∧
    SemanticRecordCodec.decode ⟨2, by decide⟩ b2.val = some ⟨.c2Root r2, by rfl⟩ ∧
    OpeningRecordCodec.decode .second b30.val = some v30

def kappa (Q : Nat) : ℚ := 12 * (Q : ℚ)^2 / (256^32 : ℚ)

def collision (Q : Nat) (v : RawCutProverCompiler.RunView) : Prop :=
  hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv RawByteCollisionTargets.pred Q)
    emptyTable v.1

def injection (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : RawCutProverCompiler.Prover) (Q : Nat)
    (hQ : ∀ H : Bytes → State, firstReads emptyTable
      (eval H (RawCutProverCompiler.experiment prover (RawCutProverCompiler.verifier decoder d))).1 ≤ Q)
    (hformat : ∀ H : Bytes → State,
      FS2.accepts (eval H (RawCutProverCompiler.experiment prover
        (RawCutProverCompiler.verifier decoder d))) →
      let run := eval H (RawCutProverCompiler.experiment prover (RawCutProverCompiler.verifier decoder d))
      (∀ i < 33, LiteralTranscript.valid i (run.2.1.2 i)) ∧
        run.2.1.1.tag = 2 ∧ CommitmentMessages run.2.1.2) :
    AcceptedAdaptiveFiatShamir.LazyInj (LiteralByteProtocol.protocol decoder)
      (RawAdaptiveLiteralDecoder.decode RawFullPublicSelection.select LiteralTableWordChoice.choose)
      (RawCutProverCompiler.compiled decoder d (RawCutWordsFromView.buildWords decoder) prover)
      (RawCutProverCompiler.verifier decoder d) kappa Q := by
  let cp := RawCutProverCompiler.compiled decoder d (RawCutWordsFromView.buildWords decoder) prover
  have hqc : ∀ H : Bytes → State, firstReads emptyTable
      (eval H (RawCutProverCompiler.experiment cp (RawCutProverCompiler.verifier decoder d))).1 ≤ Q :=
    RawCutCompilerLaw.query_bound_preserved decoder d (RawCutWordsFromView.buildWords decoder) prover Q hQ
  refine { Coll := collision Q, mass := ?_, decodes := ?_ }
  · have hm := RawByteCollisionTargets.mass SelectedTranscriptParams.params.iv Q
      (RawCutProverCompiler.experiment cp (RawCutProverCompiler.verifier decoder d)) hqc
    exact hm
  · intro H hcoll hacc i a hi hfirst
    change i < 33 at hi
    let original := eval H (RawCutProverCompiler.experiment prover (RawCutProverCompiler.verifier decoder d))
    let compiled := eval H (RawCutProverCompiler.experiment cp (RawCutProverCompiler.verifier decoder d))
    let out := RawCompiledTranscript.output decoder d prover H
    change ¬ collision Q compiled at hcoll
    change FS2.accepts compiled at hacc
    have haccOriginal : FS2.accepts original := by
      have hb := (RawCutProverCompiler.public_and_acceptance decoder d
        (RawCutWordsFromView.buildWords decoder) prover H).2
      change compiled.2.2 = original.2.2 at hb
      change compiled.2.2 = true at hacc
      change original.2.2 = true
      rw [← hb]
      exact hacc
    have hout : ¬ collision Q original := by
      intro hbad
      apply hcoll
      unfold collision at hbad ⊢
      have hs := congrArg (fun v : RawCutProverCompiler.RunView => v.1)
        (RawCutProverCompiler.compiled_experiment_eval decoder d
          (RawCutWordsFromView.buildWords decoder) prover H)
      change compiled.1 = original.1 ++ _ at hs
      rw [hs]
      exact TraceAppend.hitsBad_of_prefix _ _ _ _ hbad
    obtain ⟨hvalid,htag,hmessages⟩ := hformat H haccOriginal
    obtain ⟨r1,w1,b2,w2,r2,b30,w30,v30,h0,h2,h30,hp2,hp30⟩ := hmessages
    have hx : compiled.2.1 = out := by
      dsimp only [compiled,cp,RawCompiledTranscript.output,out]
      rw [RawCutProverCompiler.experiment_eval]
    have hframe : firstCell ((LiteralByteProtocol.protocol decoder).chain H out.1 out.2 i) =
        some (RawCutWordsFromView.frame decoder H out.1 out.2 i) :=
      RawFullPublicRun.frame_firstCell decoder H out.1 out.2 i
    change firstCell ((LiteralByteProtocol.protocol decoder).chain H compiled.2.1.1 compiled.2.1.2 i) = some a at hfirst
    rw [hx] at hfirst
    have ha : a = RawCutWordsFromView.frame decoder H out.1 out.2 i :=
      Option.some.inj (hfirst.symm.trans hframe)
    subst a
    have hd := RawAdaptiveCompiledCompletion.actual_compiled_transcript decoder d prover H
      Q (hQ H) hout hvalid htag r1 w1 b2 w2 r2 b30 w30 v30 h0 h2 h30 hp2 hp30 i hi
    change ∃ own pend g,
      RawAdaptiveLiteralDecoder.decode RawFullPublicSelection.select LiteralTableWordChoice.choose
        (RawCutWordsFromView.frame decoder H out.1 out.2 i)
        (tableBefore emptyTable compiled.1 (RawCutWordsFromView.frame decoder H out.1 out.2 i)) =
          some (own,pend,g) ∧
      bfollow g (traceFrom compiled.1 (RawCutWordsFromView.frame decoder H out.1 out.2 i)) own pend
        (tableBefore emptyTable compiled.1 (RawCutWordsFromView.frame decoder H out.1 out.2 i)) =
        some ((LiteralByteProtocol.protocol decoder).transcript H compiled.2.1.1 compiled.2.1.2 i,
          (LiteralByteProtocol.protocol decoder).msg compiled.2.1.2 i,
          (LiteralByteProtocol.protocol decoder).chal H compiled.2.1.1 compiled.2.1.2 i)
    rw [hx]
    exact hd

#print axioms injection
end AspisR1.RawAdaptiveDecoderInjection
end
