import FSTranscriptScript
set_option autoImplicit false
namespace AspisV8Completion.FSOODSampler
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
variable {Point : Type}

inductive Error where
  | limbExhausted
  | parameterExhausted
  | distinctExhausted
  deriving DecidableEq, Repr

/-- The pure parameter-to-point arithmetic is explicit, not a claimed Rust
refinement. The chronological loop exactly follows transcript.rs: a failed
QM31 draw aborts immediately; a rejected rational parameter consumes a retry.
All results, including exhaustion, retain the actual transcript state. -/
def circle (decode : List Nat → Option Point) (tape : Tape) :
    Nat → Transcript → Except Error Point × Transcript
  | 0, s => (.error .parameterExhausted, s)
  | n+1, s =>
      let draw := challenge tape s
      match draw.1 with
      | none => (.error .limbExhausted, draw.2)
      | some limbs => match decode limbs with
        | none => circle decode tape n draw.2
        | some point => (.ok point, draw.2)

def circleScript (decode : List Nat → Option Point) : (n : Nat) → Block →
    Script (List UInt8) Block (Except Error Point × Block) (66*n)
  | 0, digest => .done (.error .parameterExhausted, digest)
  | n+1, digest => bind (challengeScript digest) fun draw =>
      match draw.1 with
      | none => .done (.error .limbExhausted, draw.2)
      | some limbs => match decode limbs with
        | none => circleScript decode n draw.2
        | some point => .done (.ok point, draw.2)

/-- Equality includes the full256 cache, chronological call log, fresh-tape
cursor and final digest for arbitrary initial history, including cached calls.
No uniformity or source arithmetic premise is used. -/
theorem run_circle (decode : List Nat → Option Point) (tape : Tape) :
    ∀ n (s : Transcript),
      run tape (circleScript decode n s.digest) s.oracle =
        (some ((circle decode tape n s).1, (circle decode tape n s).2.digest),
          (circle decode tape n s).2.oracle) := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      simp only [circleScript, run_bind, run_challenge, circle]
      split
      · rfl
      · split
        · exact ih _
        · rfl

def distinct [DecidableEq Point] (decode : List Nat → Option Point)
    (first : Point) (tape : Tape) : Nat → Transcript → Except Error Point × Transcript
  | 0, s => (.error .distinctExhausted, s)
  | n+1, s =>
      let draw := circle decode tape 3 s
      match draw.1 with
      | .error error => (.error error, draw.2)
      | .ok point => if point = first then distinct decode first tape n draw.2
          else (.ok point, draw.2)

def distinctScript [DecidableEq Point] (decode : List Nat → Option Point)
    (first : Point) : (n : Nat) → Block →
    Script (List UInt8) Block (Except Error Point × Block) (198*n)
  | 0, digest => .done (.error .distinctExhausted, digest)
  | n+1, digest => bind (circleScript decode 3 digest) fun draw =>
      match draw.1 with
      | .error error => .done (.error error, draw.2)
      | .ok point => if point = first then distinctScript decode first n draw.2
          else .done (.ok point, draw.2)

theorem run_distinct [DecidableEq Point] (decode : List Nat → Option Point)
    (first : Point) (tape : Tape) : ∀ n (s : Transcript),
    run tape (distinctScript decode first n s.digest) s.oracle =
      (some ((distinct decode first tape n s).1,
        (distinct decode first tape n s).2.digest),
        (distinct decode first tape n s).2.oracle) := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      simp only [distinctScript, run_bind, run_circle, distinct]
      split
      · rfl
      · split
        · exact ih _
        · rfl

theorem circle_valid (decode : List Nat → Option Point) (tape : Tape)
    (n : Nat) (s : Transcript) (valid : FSFirstFresh.ValidHistory s.oracle) :
    FSFirstFresh.ValidHistory (circle decode tape n s).2.oracle := by
  have h := FSFirstFresh.run_valid tape (circleScript decode n s.digest) s.oracle valid
  simpa only [run_circle] using h

theorem distinct_valid [DecidableEq Point] (decode : List Nat → Option Point)
    (first : Point) (tape : Tape) (n : Nat) (s : Transcript)
    (valid : FSFirstFresh.ValidHistory s.oracle) :
    FSFirstFresh.ValidHistory (distinct decode first tape n s).2.oracle := by
  have h := FSFirstFresh.run_valid tape (distinctScript decode first n s.digest) s.oracle valid
  simpa only [run_distinct] using h

theorem distinct_success_ne [DecidableEq Point] (decode : List Nat → Option Point)
    (first : Point) (tape : Tape) : ∀ n (s : Transcript) (point : Point),
    (distinct decode first tape n s).1 = .ok point → point ≠ first := by
  intro n
  induction n with
  | zero => intro s point success; cases success
  | succ n ih =>
      intro s point success
      simp only [distinct] at success
      split at success
      · cases success
      · split at success
        · exact ih _ _ success
        · cases success; assumption

#print axioms run_circle
#print axioms run_distinct
#print axioms circle_valid
#print axioms distinct_valid
#print axioms distinct_success_ne
end AspisV8Completion.FSOODSampler
