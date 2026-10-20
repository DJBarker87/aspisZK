import R9PoolCheckpointCodec
import R16DecisionCheckpoint

/-! Construction-owned staged verifier model. All literal transcript sampling
precedes the pure matching checks; ten checks are saved, twelve are resumed.
The frozen Rust opening-hash schedule and physical checkpoint layout are a
separate source join. The terminal erased-byte decision remains arbitrary. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R9PoolSavedTenModel
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutProverCompiler RawCutTranscriptRun RecordedBinaryExperimentBin
attribute [local instance] Classical.propDecidable

/-- Collect the exact prefix consumed by the existing terminal decision. -/
def rounds (D : LiteralByteProtocol.Decoder) (pf : Proof) :
    Nat → LiteralTranscript.Prefix → Program Bytes State LiteralTranscript.Prefix
  | 0, t => .done t
  | n+1, t =>
    bind ((LiteralByteProtocol.protocol D).samp (33-(n+1)) t (pf (33-(n+1)))).toProgram
      fun c => rounds D pf n (t.ext (pf (33-(n+1))) c)

theorem rounds_decision (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (pf : Proof) (H : Bytes → State)
    (n : Nat) (t : LiteralTranscript.Prefix) :
    eval H (FS2.verifierFrom (LiteralByteProtocol.protocol D) (decisionOnBytes d) pf n t) =
      ((eval H (rounds D pf n t)).1,
       decisionOnBytes d (eval H (rounds D pf n t)).2 (pf 33)) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    simp only [FS2.verifierFrom, rounds, eval_bind]
    rw [ih]
    rfl

abbrev Prepared := (Public × Proof) × LiteralTranscript.Prefix
abbrev Raw := View Bytes State Prepared

def prepare (D : LiteralByteProtocol.Decoder) (P : Prover) : Program Bytes State Prepared :=
  bind P fun xp => bind (rounds D xp.2 33 (FS.emptyPrefix xp.1)) fun t => .done (xp, t)

def base (d : ErasedPrefix → ErasedMessage → Bool) (raw : Raw) : RunView :=
  (raw.1, (raw.2.1, decisionOnBytes d raw.2.2 (raw.2.1.2 33)))

theorem prepare_original (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State) :
    base d (eval H (prepare D P)) = eval H (original D d P) := by
  rw [RawCutProverCompiler.experiment_eval]
  unfold base prepare
  simp only [eval_bind, eval, List.append_nil]
  have hv := rounds_decision D d (eval H P).2.2 H 33 (FS.emptyPrefix (eval H P).2.1)
  change eval H (verifier D d (eval H P).2.1 (eval H P).2.2) = _ at hv
  rw [hv]

/-- Read only the query sampler's successful row-31 result. -/
def queries (t : LiteralTranscript.Prefix) : Option R16DecisionCheckpoint.Queries := do
  let mc ← t.rounds[31]?
  match mc.2.1 with
  | .queries (.ok xs) => LiteralQueryRead.decode xs
  | _ => none

structure Checkpoint where
  raw : Raw
  saved : R16DecisionCheckpoint.Checkpoint

/-- The logical checkpoint retains ghost recording data as well as the
R16/R15 matching state. Ghost data is not claimed to occur in the Rust ABI. -/
def write (raw : Raw) : Option Checkpoint :=
  match LiteralMatchingData.read raw.2.2.rounds with
  | none => none
  | some data => match queries raw.2.2 with
    | none => none
    | some q => match R16DecisionCheckpoint.tx1 data q with
      | none => none
      | some saved => some ⟨raw, saved⟩

theorem write_parts (raw : Raw) (c : Checkpoint) (hc : write raw = some c) :
    ∃ data q, LiteralMatchingData.read raw.2.2.rounds = some data ∧
      queries raw.2.2 = some q ∧ R15WriterModel.Prefix data q 10 ∧
      c = ⟨raw, R16DecisionCheckpoint.write data q⟩ := by
  unfold write at hc
  cases hd : LiteralMatchingData.read raw.2.2.rounds with
  | none => simp only [hd, reduceCtorEq] at hc
  | some data =>
    cases hq : queries raw.2.2 with
    | none => simp only [hd, hq, reduceCtorEq] at hc
    | some q =>
      by_cases hs : R15WriterModel.Prefix data q 10
      · simp only [hd, hq, R16DecisionCheckpoint.tx1, if_pos hs,
          Option.some.injEq] at hc
        exact ⟨data, q, rfl, rfl, hs, hc.symm⟩
      · simp only [hd, hq, R16DecisionCheckpoint.tx1, if_neg hs,
          reduceCtorEq] at hc

theorem write_raw (raw : Raw) (c : Checkpoint) (hc : write raw = some c) :
    c.raw = raw := by
  obtain ⟨data, q, _, _, _, hc⟩ := write_parts raw c hc
  rw [hc]


def stage1 (D : LiteralByteProtocol.Decoder) (P : Prover) :
    Program Bytes State (Option Checkpoint) :=
  bind (OracleProgramRecording.record (prepare D P)) fun raw => .done (write raw)

theorem stage1_eval (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    (eval H (stage1 D P)).2 = write (eval H (prepare D P)) := by
  simp only [stage1, eval_bind, OracleProgramRecording.eval_record, eval]

/-- Resume twelve checks, then the same erased-byte decision. -/
def accepted (d : ErasedPrefix → ErasedMessage → Bool) (c : Checkpoint) : Bool :=
  R16DecisionCheckpoint.tx2 (R16DecisionCheckpoint.resume c.saved) && (base d c.raw).2.2

theorem accepted_decision (d : ErasedPrefix → ErasedMessage → Bool) (c : Checkpoint)
    (ha : accepted d c = true) : (base d c.raw).2.2 = true :=
  (Bool.and_eq_true_iff.mp ha).2

theorem accepted_matching (d : ErasedPrefix → ErasedMessage → Bool)
    (raw : Raw) (c : Checkpoint) (hw : write raw = some c)
    (ha : accepted d c = true) :
    c.saved.next = 10 ∧ ∀ j, MatchingSupport.match0 c.saved.data (c.saved.queries j) := by
  obtain ⟨data, q, _, _, hs, hc⟩ := write_parts raw c hw
  subst c
  have hrest := (Bool.and_eq_true_iff.mp ha).1
  have ht : ∀ j : Fin 22, 10 ≤ j.val → MatchingSupport.match0 data (q j) :=
    (of_decide_eq_true hrest).2
  exact ⟨rfl, R15WriterModel.saved_and_resumed data q hs ht⟩

/-- Compiler recording is reconstructed from the actual stage-1 log. The
second verifier traversal is the existing compiler's replay, not a fresh
independent oracle or an extra charged scan. -/
def resume (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (c : Checkpoint) : Program Bytes State RunView :=
  bind (OracleProgramRecording.record (verifier D d c.raw.2.1.1 c.raw.2.1.2)) fun replay =>
    .done (c.raw.1 ++ replay.1,
      ((c.raw.2.1.1, RawCutTranscriptRun.proof
        (BinCompiledRunWordStability.wordsFromRun D (base d c.raw)) c.raw.2.1.2), accepted d c))

theorem resume_verdict (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (c : Checkpoint) (H : Bytes → State) :
    (eval H (resume D d c)).2.2.2 = accepted d c := by
  simp only [resume, eval_bind, OracleProgramRecording.eval_record, eval]

theorem resume_recorded (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State)
    (c : Checkpoint) (hc : write (eval H (prepare D P)) = some c)
    (ha : (eval H (resume D d c)).2.2.2 = true) :
    (eval H (resume D d c)).2 = eval H (recorded D d P) := by
  have hr := write_raw _ c hc
  have hb : base d c.raw = eval H (original D d P) := by
    rw [hr]; exact prepare_original D d P H
  have hac : accepted d c = true := by rw [← resume_verdict D d c H]; exact ha
  have hd := accepted_decision d c hac
  have hx : c.raw.2.1 = (eval H (original D d P)).2.1 := congrArg (fun v : RunView => v.2.1) hb
  have hl : c.raw.1 = (eval H (original D d P)).1 := congrArg Prod.fst hb
  rw [show recorded D d P = experiment (compiled D d
    (BinCompiledRunWordStability.wordsFromRun D) P) (verifier D d) from rfl,
    compiled_experiment_eval]
  simp only [resume, eval_bind, OracleProgramRecording.eval_record, eval]
  rw [hb, hl, hx, hac]
  have hh : (eval H (original D d P)).2.2 = true := by rw [← hb]; exact hd
  rw [hh]

#print axioms rounds_decision
#print axioms prepare_original
#print axioms write_parts
#print axioms write_raw
#print axioms stage1_eval
#print axioms accepted_decision
#print axioms accepted_matching
#print axioms resume_verdict
#print axioms resume_recorded
end AspisR1.R9PoolSavedTenModel
end
