import AspisV8H1C2.FiniteTransport
import AspisV8PairedCommitment.ShadowTable

/-!
# Exact finite marginals for the eager/delayed hop

The joint experiment uses one uniform fixed-slot tape. A side which has a
cache hit ignores that slot; a side which needs a fresh answer consumes it.
Thus cached/fresh mismatches retain the cached answer on one side and a fresh
uniform marginal on the other. No agreement is asserted after a bad event.
-/
set_option autoImplicit false
namespace AspisV8PairedCommitment

open AspisV8H1C2

variable {Input Answer Tape EagerOut DelayedOut : Type*}

/-- The exact coupled leaf transition: eager performs an ordinary query while
delayed reserves the same fresh answer without installing its input. -/
def coupledLeafStep [DecidableEq Input]
    (table : Table Input Answer) (input : Input) (fresh : Answer) :
    (Answer × Table Input Answer) × Answer :=
  (queryStep table input fresh, fresh)

theorem coupled_leaf_left_marginal
    [DecidableEq Input] [Fintype Answer] [Nonempty Answer]
    (table : Table Input Answer) (input : Input) :
    SameUniformLaw
      (fun fresh => (coupledLeafStep table input fresh).1)
      (fun fresh => queryStep table input fresh) := by
  exact sameUniformLaw_of_equiv _ _ (Equiv.refl Answer) (fun _ => rfl)

theorem coupled_leaf_right_marginal
    [DecidableEq Input] [Fintype Answer] [Nonempty Answer]
    (table : Table Input Answer) (input : Input) :
    SameUniformLaw
      (fun fresh => (coupledLeafStep table input fresh).2)
      (fun fresh : Answer => fresh) := by
  exact sameUniformLaw_of_equiv _ _ (Equiv.refl Answer) (fun _ => rfl)

theorem coupled_leaf_cached_case [DecidableEq Input]
    (table : Table Input Answer) (input : Input) (old fresh : Answer)
    (cached : table input = some old) :
    coupledLeafStep table input fresh = ((old, table), fresh) := by
  simp [coupledLeafStep, queryStep, cached]

theorem coupled_leaf_fresh_case [DecidableEq Input]
    (table : Table Input Answer) (input : Input) (fresh : Answer)
    (missing : table input = none) :
    coupledLeafStep table input fresh =
      ((fresh, put table input fresh), fresh) := by
  simp [coupledLeafStep, queryStep, missing]

/-- The four cached/fresh rows in the reviewed coupling table. `true` means
the side needs the current fresh slot; `false` means it retains its cache. -/
def coupledAnswerStep (leftFresh rightFresh : Bool)
    (leftCached rightCached fresh : Answer) : Answer × Answer :=
  (if leftFresh then fresh else leftCached,
    if rightFresh then fresh else rightCached)

theorem coupled_answer_left_marginal
    [Fintype Answer] [Nonempty Answer]
    (leftFresh rightFresh : Bool) (leftCached rightCached : Answer) :
    SameUniformLaw
      (fun fresh => (coupledAnswerStep leftFresh rightFresh
        leftCached rightCached fresh).1)
      (fun fresh => if leftFresh then fresh else leftCached) := by
  exact sameUniformLaw_of_equiv _ _ (Equiv.refl Answer) (fun _ => rfl)

theorem coupled_answer_right_marginal
    [Fintype Answer] [Nonempty Answer]
    (leftFresh rightFresh : Bool) (leftCached rightCached : Answer) :
    SameUniformLaw
      (fun fresh => (coupledAnswerStep leftFresh rightFresh
        leftCached rightCached fresh).2)
      (fun fresh => if rightFresh then fresh else rightCached) := by
  exact sameUniformLaw_of_equiv _ _ (Equiv.refl Answer) (fun _ => rfl)

/-- A full coupled continuation is the pair of the two actual deterministic
interpreters on one uniform fixed-slot tape. This remains the construction
after Bad; it does not force their outputs to agree. -/
def jointRun (eager : Tape → EagerOut) (delayed : Tape → DelayedOut) :
    Tape → EagerOut × DelayedOut :=
  fun tape => (eager tape, delayed tape)

theorem joint_run_left_marginal
    [Fintype Tape] [Nonempty Tape]
    (eager : Tape → EagerOut) (delayed : Tape → DelayedOut) :
    SameUniformLaw (fun tape => (jointRun eager delayed tape).1) eager := by
  exact sameUniformLaw_of_equiv _ _ (Equiv.refl Tape) (fun _ => rfl)

theorem joint_run_right_marginal
    [Fintype Tape] [Nonempty Tape]
    (eager : Tape → EagerOut) (delayed : Tape → DelayedOut) :
    SameUniformLaw (fun tape => (jointRun eager delayed tape).2) delayed := by
  exact sameUniformLaw_of_equiv _ _ (Equiv.refl Tape) (fun _ => rfl)

#print axioms coupled_leaf_left_marginal
#print axioms coupled_leaf_right_marginal
#print axioms coupled_answer_left_marginal
#print axioms coupled_answer_right_marginal
#print axioms joint_run_left_marginal
#print axioms joint_run_right_marginal
end AspisV8PairedCommitment
