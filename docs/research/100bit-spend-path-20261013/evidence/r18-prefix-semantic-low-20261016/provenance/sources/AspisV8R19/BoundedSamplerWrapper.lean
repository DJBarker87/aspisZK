import AspisV8R19.SamplerOracleLaws
import AspisV8R19.QM31SamplerInvariants

/-! Bounded source-shaped outer retries. Inner exhaustion is propagated at
once; a rejected successful draw retains its advanced state. -/
set_option autoImplicit false
namespace AspisV8R19.BoundedSamplerWrapper
open DuplexFrames SourceDuplexStep MemoizedProgramLaw OracleProgramOps
open QM31SamplerInvariants SamplerOracleLaws
variable {O E : Type}

def program (accept : List Nat → Option O) (inner outer : E) :
    Nat → State → Program Bytes State (Except E O × State)
  | 0,s => .done (.error outer,s)
  | n+1,s => bind (QM31SamplerProgram.challengeProgram s) (fun r =>
      match r.1 with
      | none => .done (.error inner,r.2)
      | some xs => match accept xs with
        | some y => .done (.ok y,r.2)
        | none => program accept inner outer n r.2)

def run (accept : List Nat → Option O) (inner outer : E) (H : Bytes → State) :
    Nat → State → View Bytes State (Except E O × State)
  | 0,s => ([],(.error outer,s))
  | n+1,s =>
      let r := QM31SamplerProgram.challengeRun H s
      match r.2.1 with
      | none => (r.1,(.error inner,r.2.2))
      | some xs => match accept xs with
        | some y => (r.1,(.ok y,r.2.2))
        | none =>
            let tail := run accept inner outer H n r.2.2
            (r.1 ++ tail.1,tail.2)

theorem exact_run (accept : List Nat → Option O) (inner outer : E)
    (H : Bytes → State) (n : Nat) (s : State) :
    eval H (program accept inner outer n s) = run accept inner outer H n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      simp only [program,eval_bind,QM31SamplerProgram.challenge_exact,run]
      cases h : (QM31SamplerProgram.challengeRun H s).2.1 with
      | none => simp [h,eval]
      | some xs => cases ha : accept xs <;> simp [h,ha,ih,eval]

theorem oracle_law (accept : List Nat → Option O) (inner outer : E)
    (n : Nat) (s : State) :
    CorrectLaw (program accept inner outer n s) (fun H => run accept inner outer H n s) :=
  law_of_exact _ _ (fun H => exact_run accept inner outer H n s)

theorem zero_no_reads (accept : List Nat → Option O) (inner outer : E)
    (H : Bytes → State) (s : State) :
    run accept inner outer H 0 s = ([],(.error outer,s)) := rfl

theorem inner_error_stops (accept : List Nat → Option O) (inner outer : E)
    (H : Bytes → State) (n : Nat) (s : State)
    (h : (QM31SamplerProgram.challengeRun H s).2.1 = none) :
    run accept inner outer H (n+1) s =
      ((QM31SamplerProgram.challengeRun H s).1,
       (.error inner,(QM31SamplerProgram.challengeRun H s).2.2)) := by simp [run,h]

theorem accepted_stops (accept : List Nat → Option O) (inner outer : E)
    (H : Bytes → State) (n : Nat) (s : State) (xs : List Nat) (y : O)
    (h : (QM31SamplerProgram.challengeRun H s).2.1 = some xs)
    (ha : accept xs = some y) :
    run accept inner outer H (n+1) s =
      ((QM31SamplerProgram.challengeRun H s).1,
       (.ok y,(QM31SamplerProgram.challengeRun H s).2.2)) := by simp [run,h,ha]

theorem rejected_retains_trace (accept : List Nat → Option O) (inner outer : E)
    (H : Bytes → State) (n : Nat) (s : State) (xs : List Nat)
    (h : (QM31SamplerProgram.challengeRun H s).2.1 = some xs)
    (ha : accept xs = none) :
    run accept inner outer H (n+1) s =
      ((QM31SamplerProgram.challengeRun H s).1 ++
        (run accept inner outer H n (QM31SamplerProgram.challengeRun H s).2.2).1,
       (run accept inner outer H n (QM31SamplerProgram.challengeRun H s).2.2).2) := by
  simp [run,h,ha]

theorem successful_image (accept : List Nat → Option O) (inner outer : E)
    (H : Bytes → State) (n : Nat) (s : State) (y : O)
    (h : (run accept inner outer H n s).2.1 = .ok y) :
    ∃ xs, xs.length = 4 ∧ (∀ a ∈ xs, a < 2147483647) ∧ accept xs = some y := by
  induction n generalizing s with
  | zero => simp [run] at h
  | succ n ih =>
      cases hr : (QM31SamplerProgram.challengeRun H s).2.1 with
      | none => simp [run,hr] at h
      | some xs =>
          cases ha : accept xs with
          | none => apply ih _; simpa [run,hr,ha] using h
          | some z =>
              have hz : z = y := by simpa [run,hr,ha] using h
              subst z
              have hc := challenge_four_canonical_limbs H s xs hr
              exact ⟨xs,hc.1,hc.2,ha⟩

#print axioms exact_run
#print axioms oracle_law
#print axioms zero_no_reads
#print axioms inner_error_stops
#print axioms accepted_stops
#print axioms rejected_retains_trace
#print axioms successful_image
end AspisV8R19.BoundedSamplerWrapper
