import R1FinalSoundnessBinPerQueryR19
import R1LiteralByteRunFacts

/-! An erased decision cannot observe the constructor obligation in R16.
This is an interface countermodel, not a frozen Rust execution. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R16DecisionErasure
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutProverCompiler RawCutTranscriptRun
open RecordedBinaryExperimentBin DecoderInstanceBoundaryBin

/-- Retag byte-carrying messages as second commitments. No bytes change. -/
def retag : LiteralTranscript.Message → LiteralTranscript.Message
  | .initial root word => .initial root word
  | .payload bytes => .second bytes (fun _ => 0)
  | .c2 bytes _ => .second bytes (fun _ => 0)
  | .second bytes word => .second bytes word

def retagProof (pf : LiteralProtocol.Proof) : LiteralProtocol.Proof :=
  fun i => if i = 31 then retag (pf i) else pf i

theorem erase_retag (m : LiteralTranscript.Message) :
    LiteralTranscript.erase (retag m) = LiteralTranscript.erase m := by
  cases m <;> rfl

theorem erase_retagProof (pf : LiteralProtocol.Proof) (i : Nat) :
    LiteralTranscript.erase (retagProof pf i) = LiteralTranscript.erase (pf i) := by
  unfold retagProof
  split
  · exact erase_retag _
  · rfl

theorem retag_invalid31 (w : CanonicalCutEnrichedTranscript.Words)
    (pf : LiteralProtocol.Proof) :
    ¬ LiteralTranscript.valid 31
      (CanonicalCutEnrichedTranscript.enrichMessage w (retagProof pf 31)) := by
  simp only [retagProof]
  cases pf 31 <;> simp [retag, CanonicalCutEnrichedTranscript.enrichMessage,
    LiteralTranscript.valid]

theorem erased_transcript_eq (D : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public)
    (pf pf' : LiteralProtocol.Proof)
    (same : ∀ i, LiteralTranscript.erase (pf' i) = LiteralTranscript.erase (pf i))
    (n : Nat) :
    LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H pub pf' n) =
    LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H pub pf n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change LiteralTranscript.erasePrefix
      (((LiteralByteProtocol.protocol D).transcript H pub pf' n).ext (pf' n)
        (eval H (LiteralByteSampler.samp n
          ((LiteralByteProtocol.protocol D).transcript H pub pf' n) (pf' n)).toProgram).2) =
      LiteralTranscript.erasePrefix
      (((LiteralByteProtocol.protocol D).transcript H pub pf n).ext (pf n)
        (eval H (LiteralByteSampler.samp n
          ((LiteralByteProtocol.protocol D).transcript H pub pf n) (pf n)).toProgram).2)
    rw [LiteralTranscript.erasePrefix_ext, LiteralTranscript.erasePrefix_ext]
    have hs : LiteralByteSampler.samp n
        ((LiteralByteProtocol.protocol D).transcript H pub pf' n) (pf' n) =
        LiteralByteSampler.samp n
        ((LiteralByteProtocol.protocol D).transcript H pub pf n) (pf n) := by
      unfold LiteralByteSampler.samp LiteralTranscript.samp
      rw [ih, same n]
    rw [hs, ih, same n]

theorem acceptance_retag (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof) :
    (eval H (verifier D d pub (retagProof pf))).2 =
      (eval H (verifier D d pub pf)).2 := by
  unfold RawCutProverCompiler.verifier
  rw [FS2.verifier_eval, FS2.verifier_eval]
  change d (LiteralTranscript.erasePrefix
    ((LiteralByteProtocol.protocol D).transcript H pub (retagProof pf) 33))
    (LiteralTranscript.erase (retagProof pf 33)) = _
  rw [erased_transcript_eq D H pub pf (retagProof pf) (erase_retagProof pf) 33,
    erase_retagProof]
  rfl

/-- Every accepted proof has a same-byte, equally accepted retagging for which
no SourceInputs can meet R16, even after binary compiler enrichment. -/
theorem accepted_without_instance (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (accepted : (eval H (verifier D d pub pf)).2 = true) :
    let P : Prover := Program.done (pub, retagProof pf)
    FS2.accepts (eval H (original D d P)) ∧
      ∀ i : SourceInputs, ¬ InstanceFields D d P H i := by
  dsimp only
  constructor
  · change (eval H (original D d (Program.done (pub, retagProof pf)))).2.2 = true
    rw [RawCutProverCompiler.experiment_eval]
    exact (acceptance_retag D d H pub pf).trans accepted
  · intro i fields
    have hrow := fields.2.1
    have hpf : (eval H (original D d (Program.done (pub, retagProof pf)))).2.1.2 =
        retagProof pf := by
      rw [RawCutProverCompiler.experiment_eval]
      rfl
    have hcompiled :
        (annotatedRun D d (Program.done (pub, retagProof pf)) H).2.1.2 =
          RawCutTranscriptRun.proof
            (BinCompiledRunWordStability.wordsFromRun D
              (eval H (original D d (Program.done (pub, retagProof pf)))))
            (retagProof pf) := by
      unfold DecoderInstanceBoundaryBin.annotatedRun
      rw [compiled_experiment_eval]
      dsimp only
      change RawCutTranscriptRun.proof _
        (eval H (original D d (Program.done (pub, retagProof pf)))).2.1.2 = _
      rw [hpf]
    have idx := LiteralByteRunFacts.transcript_index D H
      (compiledPublic D d (Program.done (pub, retagProof pf)) H)
      (annotatedRun D d (Program.done (pub, retagProof pf)) H).2.1.2
      33 31 (by decide)
    have hm := congrArg Prod.fst (Option.some.inj (hrow.symm.trans idx))
    dsimp only at hm
    have hv := fields.2.2.2.1
    rw [hm, hcompiled] at hv
    exact retag_invalid31 _ pf hv

#print axioms erase_retag
#print axioms erase_retagProof
#print axioms retag_invalid31
#print axioms erased_transcript_eq
#print axioms acceptance_retag
#print axioms accepted_without_instance
end AspisR1.R16DecisionErasure
end
