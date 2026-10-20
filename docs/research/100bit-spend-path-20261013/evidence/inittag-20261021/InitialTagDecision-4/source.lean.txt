import RWireCounterexamples

/-! Public-tag admission is a decision obligation, not initial-frame syntax.
Global admission is sufficient but is stronger than the old reachable-run law.
CheckedRejects restricts rejection to the exact clean, checked use domain. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.InitialTagDecision
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutProverCompiler RawCutTranscriptRun RecordedBinaryExperimentBin
attribute [local irreducible] BinCompiledRunWordStability.wordsFromRun
  RawCutProverCompiler.compiled RawCutProverCompiler.verifier RawCutProverCompiler.experiment

/-- The pure byte decision's actual final arguments for this recorded run. -/
def finalPrefix (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State) : ErasedPrefix :=
  LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H
    (eval H (recorded D d P)).2.1.1 (eval H (recorded D d P)).2.1.2 33)

def finalMessage (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State) : ErasedMessage :=
  LiteralTranscript.erase ((eval H (recorded D d P)).2.1.2 33)

def RejectsOtherTags (d : ErasedPrefix → ErasedMessage → Bool) : Prop :=
  ∀ pre message, pre.statement.tag ≠ 2 → d pre message = false

/-- Rejection only on reachable collision-free, format-checked transcripts.
No acceptance antecedent, opening law, or decoder-follow obligation. -/
def CheckedRejects (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat) : Prop :=
  ∀ H : Bytes → State, ¬ binaryCollision Q (eval H (recorded D d P)) →
    RWireCheckedFormat.Format (eval H (recorded D d P)).2.1.2 →
    (finalPrefix D d P H).statement.tag ≠ 2 →
    d (finalPrefix D d P H) (finalMessage D d P H) = false

theorem erased_transcript_tag (D : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (n : Nat) :
    (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H pub pf n)).statement.tag =
      pub.tag := by
  change ((LiteralByteProtocol.protocol D).transcript H pub pf n).statement.tag = pub.tag
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem final_tag (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State) :
    (finalPrefix D d P H).statement.tag = (eval H (recorded D d P)).2.1.1.tag :=
  erased_transcript_tag D H _ _ 33

theorem final_decision (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State) :
    d (finalPrefix D d P H) (finalMessage D d P H) =
      (eval H (recorded D d P)).2.2 := by
  let cp := compiled D d (BinCompiledRunWordStability.wordsFromRun D) P
  have he := RawCutProverCompiler.experiment_eval cp (verifier D d) H
  have hv := FS2.verifier_eval (LiteralByteProtocol.protocol D) (decisionOnBytes d) H
    (eval H cp).2.1 (eval H cp).2.2
  have hpub : (eval H (recorded D d P)).2.1 = (eval H cp).2 := by
    rw [RWireCounterexamples.recorded_eq, he]
  have ha : (eval H (recorded D d P)).2.2 =
      (eval H (verifier D d (eval H cp).2.1 (eval H cp).2.2)).2 := by
    rw [RWireCounterexamples.recorded_eq, he]
  unfold finalPrefix finalMessage
  rw [hpub, ha]
  unfold RawCutProverCompiler.verifier
  rw [hv]
  rfl

theorem checked_of_global (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat)
    (h : RejectsOtherTags d) : CheckedRejects D d P Q := by
  intro H _ _ ht
  exact h _ _ ht

theorem checked_of_initialTag (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat)
    (h : RWireCompletion.InitialTag D d P Q) : CheckedRejects D d P Q := by
  intro H hout hf ht
  rw [final_decision D d P H]
  cases ha : (eval H (recorded D d P)).2.2 with
  | false => rfl
  | true =>
    exact False.elim (ht ((final_tag D d P H).trans
      (h H hout ha (hf.1 0 (by decide)))))

theorem accepted_tag (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat)
    (h : CheckedRejects D d P Q) (H : Bytes → State)
    (hout : ¬ binaryCollision Q (eval H (recorded D d P)))
    (hf : RWireCheckedFormat.Format (eval H (recorded D d P)).2.1.2)
    (ha : FS2.accepts (eval H (recorded D d P))) :
    (eval H (recorded D d P)).2.1.1.tag = 2 := by
  by_contra ht
  have hr := h H hout hf (by rw [final_tag]; exact ht)
  rw [final_decision D d P H, ha] at hr
  cases hr

/-- All byte-valued public tags inhabit the public carrier. -/
theorem public_tags (tag : Fin 256) :
    ∃ pub : LiteralTranscript.Public, pub.tag = tag :=
  ⟨⟨[], by decide, tag⟩, rfl⟩

/-- An actual accepted, clean, valid-row-zero run refutes unconditional tag admission. -/
theorem protocol_counterexample (D : LiteralByteProtocol.Decoder) :
    ¬ RWireCompletion.InitialTag D (fun _ _ => true) (RWireCounterexamples.badProver 0) 1161 := by
  intro h
  obtain ⟨H, ha, hout, _⟩ := RWireCounterexamples.non_two_accepted_counterexample D
  obtain ⟨word, hw⟩ := RWireCounterexamples.bad_initial D 0 H 0
  have ht := h H hout ha (by rw [hw]; trivial)
  rw [RWireCounterexamples.bad_public] at ht
  exact (by decide : (0 : Fin 256) ≠ 2) ht

/-- The old law cannot imply global rejection: the prover may always select 2. -/
theorem global_not_implied (D : LiteralByteProtocol.Decoder) :
    RWireCompletion.InitialTag D (fun _ _ => true) (RWireCounterexamples.badProver 2) 1161 ∧
      ¬ RejectsOtherTags (fun _ _ => true) := by
  refine ⟨(RWireCounterexamples.strict_weakening D).1, ?_⟩
  intro h
  have hf := h ⟨⟨[], by decide, 0⟩, []⟩ (.initial default) (by decide)
  cases hf

/-- The checked-domain decision fact is strictly weaker than InitialTag. -/
theorem checked_strictly_weaker (D : LiteralByteProtocol.Decoder) :
    CheckedRejects D (fun _ _ => true) (RWireCounterexamples.badProver 0) 1161 ∧
      ¬ RWireCompletion.InitialTag D (fun _ _ => true) (RWireCounterexamples.badProver 0) 1161 := by
  refine ⟨?_, protocol_counterexample D⟩
  intro H _ hf _
  obtain ⟨word, hw⟩ := RWireCounterexamples.bad_initial D 0 H 1
  have hv := hf.1 1 (by decide)
  rw [hw] at hv
  cases hv

#print axioms erased_transcript_tag
#print axioms final_tag
#print axioms final_decision
#print axioms checked_of_global
#print axioms checked_of_initialTag
#print axioms accepted_tag
#print axioms public_tags
#print axioms protocol_counterexample
#print axioms global_not_implied
#print axioms checked_strictly_weaker
end AspisR1.InitialTagDecision
end
