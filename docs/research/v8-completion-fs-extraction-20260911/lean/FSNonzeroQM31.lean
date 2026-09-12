import FSV7OODSampler

/-! Exact bounded nonzero-QM31 control flow used by the selected V8 source.
This is a deterministic transcript theorem.  It does not assert that an
unseen squeeze is uniform or condition away an exhausted retry. -/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.FSNonzeroQM31
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisV5ComponentCQM31TowerExact
open AspisV8Completion.FSV7OODSampler
abbrev K := QM31Exact

inductive Error where
  | limbExhausted
  | assemblyFailure
  | zeroExhausted
  deriving DecidableEq, Repr

def candidate (tape : Tape) (s : Transcript) : Except Error K × Transcript :=
  let draw := challenge tape s
  match draw.1 with
  | none => (.error .limbExhausted, draw.2)
  | some limbs => match assemble limbs with
    | none => (.error .assemblyFailure, draw.2)
    | some value => (.ok value, draw.2)

def candidateScript (digest : Block) :
    Script (List UInt8) Block (Except Error K × Block) 66 :=
  bind (challengeScript digest) fun draw =>
    match draw.1 with
    | none => .done (.error .limbExhausted, draw.2)
    | some limbs => match assemble limbs with
      | none => .done (.error .assemblyFailure, draw.2)
      | some value => .done (.ok value, draw.2)

theorem run_candidate (tape : Tape) (s : Transcript) :
    run tape (candidateScript s.digest) s.oracle =
      (some ((candidate tape s).1, (candidate tape s).2.digest),
        (candidate tape s).2.oracle) := by
  simp only [candidateScript, run_bind, run_challenge, candidate]
  split
  · rfl
  · split <;> rfl

/-- Three source attempts.  A limb failure aborts immediately; only a
successfully decoded zero consumes another outer attempt. -/
def nonzero (tape : Tape) : Nat → Transcript → Except Error K × Transcript
  | 0, s => (.error .zeroExhausted, s)
  | n+1, s =>
      let draw := candidate tape s
      match draw.1 with
      | .error error => (.error error, draw.2)
      | .ok value => if value = 0 then nonzero tape n draw.2 else (.ok value, draw.2)

def nonzeroScript : (n : Nat) → Block →
    Script (List UInt8) Block (Except Error K × Block) (66*n)
  | 0, digest => .done (.error .zeroExhausted, digest)
  | n+1, digest => bind (candidateScript digest) fun draw =>
      match draw.1 with
      | .error error => .done (.error error, draw.2)
      | .ok value => if value = 0 then nonzeroScript n draw.2
          else .done (.ok value, draw.2)

theorem run_nonzero (tape : Tape) : ∀ n (s : Transcript),
    run tape (nonzeroScript n s.digest) s.oracle =
      (some ((nonzero tape n s).1, (nonzero tape n s).2.digest),
        (nonzero tape n s).2.oracle) := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      simp only [nonzeroScript, run_bind, run_candidate, nonzero]
      split
      · rfl
      · split
        · exact ih _
        · rfl

theorem candidate_not_assembly_failure (tape : Tape) (s : Transcript) :
    (candidate tape s).1 ≠ .error .assemblyFailure := by
  intro failure
  simp only [candidate] at failure
  cases sampled : (challenge tape s).1 with
  | none =>
      simp only [sampled] at failure
      cases failure
  | some limbs =>
      simp only [sampled] at failure
      obtain ⟨value, assembled⟩ := challenge_assembles tape s limbs sampled
      simp only [assembled, reduceCtorEq] at failure

theorem nonzero_success_ne (tape : Tape) : ∀ n (s : Transcript) (value : K),
    (nonzero tape n s).1 = .ok value → value ≠ 0 := by
  intro n
  induction n with
  | zero => intro s value success; cases success
  | succ n ih =>
      intro s value success
      simp only [nonzero] at success
      split at success
      · cases success
      · split at success
        · exact ih _ _ success
        · cases success
          assumption

theorem nonzero_valid (tape : Tape) (n : Nat) (s : Transcript)
    (valid : FSFirstFresh.ValidHistory s.oracle) :
    FSFirstFresh.ValidHistory (nonzero tape n s).2.oracle := by
  have checked := FSFirstFresh.run_valid tape (nonzeroScript n s.digest) s.oracle valid
  simpa only [run_nonzero] using checked

#print axioms run_candidate
#print axioms run_nonzero
#print axioms candidate_not_assembly_failure
#print axioms nonzero_success_ne
#print axioms nonzero_valid
end AspisV8Completion.FSNonzeroQM31
