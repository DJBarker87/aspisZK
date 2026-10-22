import R1Z.ProverCommitCoinTape27
import R1Z.ProverCommitProductRun25
/-! Deterministic state initialization and adaptive evaluation preserve the
existing independent-product coupling marginals. No freshness assumption or
law on a post-selected cursor is introduced. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitCursorMarginal27
open R0Z R0Z.FsStatement R0Z.LawTransport
open ProverCommitCoinTape27 ProverCommitProductRun25
variable {Key Answer Value Rest : Type} [DecidableEq Key] [DecidableEq Answer]

def initial (coins : Nat → Answer) (recording : Bool) : State Key Answer :=
  ⟨coins,0,if recording then some (fun _ => none) else none,false⟩

/-- The entire source execution, including final cursor, recordings, collision
flag and ordered history, has the source marginal for any adaptive call tree.
The input tape is decoded from the *source* projection of the product coupling. -/
theorem source_execution [Fintype Rest]
    (coins : Source Rest → Nat → Answer) (recording : Bool)
    (program : Program Key Answer Value) (test : Execution Key Answer Value → ℚ) :
    mean (fun s : Space Rest => test (run reference program
      (initial (coins ((regroup Rest (exchange s)).2)) recording))) =
    mean (fun r : Source Rest => test (run reference program
      (initial (coins r) recording))) :=
  source_marginal (fun r => test (run reference program (initial (coins r) recording)))

/-- The same pushforward law for the source-order implementation of each call. -/
theorem native_source_execution [Fintype Rest]
    (coins : Source Rest → Nat → Answer) (recording : Bool)
    (program : Program Key Answer Value) (test : Execution Key Answer Value → ℚ) :
    mean (fun s : Space Rest => test (run native program
      (initial (coins ((regroup Rest (exchange s)).2)) recording))) =
    mean (fun r : Source Rest => test (run reference program
      (initial (coins r) recording))) := by
  simp only [sequence_preserves]
  exact source_execution coins recording program test

/-- The model ignores independent fuel through its existing projection.
Explicit cursor effects are deterministic pushforwards, not new randomness. -/
theorem model_execution [Fintype Rest] [Nonempty Rest]
    (coins : Space Rest → Nat → Answer) (recording : Bool)
    (program : Program Key Answer Value) (test : Execution Key Answer Value → ℚ) :
    mean (fun s : (cp Rest).S => test (run reference program
      (initial (coins ((cp Rest).toM s)) recording))) =
    mean (fun s : Space Rest => test (run reference program
      (initial (coins s) recording))) :=
  model_marginal Rest (fun s => test (run reference program (initial (coins s) recording)))

#print axioms source_execution
#print axioms native_source_execution
#print axioms model_execution
end R1Z.ProverCommitCursorMarginal27
