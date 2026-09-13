import AspisV8PairedCommitment.GoodEvent
import AspisV8PairedCommitment.Marginals

/-!
# Forward witness-retaining commitment hop

This file makes the good-execution induction explicit. It starts from a
forward state, adds deferred eager leaf inputs only when both tables report a
miss, executes ordinary queries outside the deferred set, and atomically
materialises both paired inputs before recording an opening. Executions that
cannot take one of these transitions belong to `bad`; their actual eager and
delayed outcomes remain in the two marginals.

The payload/provider may retain a witness. A source refinement must construct
the per-tape trace and prove its commands are causal and salt-oblivious.
-/
set_option autoImplicit false
namespace AspisV8PairedCommitment

open AspisV8H1C2

variable {Input Answer Obs Coin : Type*}

structure ForwardState (Input Answer Obs : Type*) where
  eager : Table Input Answer
  delayed : Table Input Answer
  hidden : Input → Prop
  eagerView : List Obs
  delayedView : List Obs

def ForwardInvariant (state : ForwardState Input Answer Obs) : Prop :=
  AgreeExcept state.hidden state.eager state.delayed ∧
    state.eagerView = state.delayedView

inductive ForwardStep [DecidableEq Input] [DecidableEq Answer]
    (observe : Answer → Obs) :
    ForwardState Input Answer Obs → ForwardState Input Answer Obs → Prop
  | defer (state : ForwardState Input Answer Obs) (input : Input) (fresh : Answer)
      (eagerMissing : state.eager input = none)
      (delayedMissing : state.delayed input = none) :
      ForwardStep observe state
        { eager := put state.eager input fresh
          delayed := state.delayed
          hidden := fun query => query = input ∨ state.hidden query
          eagerView := state.eagerView ++ [observe fresh]
          delayedView := state.delayedView ++ [observe fresh] }
  | ordinary (state : ForwardState Input Answer Obs) (input : Input) (fresh : Answer)
      (outside : ¬ state.hidden input) :
      ForwardStep observe state
        { eager := (queryStep state.eager input fresh).2
          delayed := (queryStep state.delayed input fresh).2
          hidden := state.hidden
          eagerView := state.eagerView ++ [observe (queryStep state.eager input fresh).1]
          delayedView := state.delayedView ++ [observe (queryStep state.delayed input fresh).1] }
  | materialize (state : ForwardState Input Answer Obs)
      (i j : Input) (a b : Answer) (record : Obs)
      (eagerI : state.eager i = some a) (eagerJ : state.eager j = some b)
      (success : (installPair state.delayed i j a b).2 = true) :
      ForwardStep observe state
        { eager := state.eager
          delayed := (installPair state.delayed i j a b).1
          hidden := fun query => state.hidden query ∧ query ≠ i ∧ query ≠ j
          eagerView := state.eagerView ++ [record]
          delayedView := state.delayedView ++ [record] }
  | emit (state : ForwardState Input Answer Obs) (record : Obs) :
      ForwardStep observe state
        { state with
          eagerView := state.eagerView ++ [record]
          delayedView := state.delayedView ++ [record] }

theorem forward_step_preserves
    [DecidableEq Input] [DecidableEq Answer] (observe : Answer → Obs)
    {before after : ForwardState Input Answer Obs}
    (invariant : ForwardInvariant before)
    (step : ForwardStep observe before after) :
    ForwardInvariant after := by
  rcases invariant with ⟨agree, views⟩
  cases step with
  | defer input fresh eagerMissing delayedMissing =>
      constructor
      · intro query outside
        have notInput : query ≠ input := by
          intro same
          exact outside (Or.inl same)
        have notHidden : ¬ before.hidden query := by
          intro hidden
          exact outside (Or.inr hidden)
        simpa [put, notInput] using agree query notHidden
      · simp [views]
  | ordinary input fresh outside =>
      have transition := ordinary_query_agrees before.hidden before.eager before.delayed
        input fresh agree outside
      exact ⟨transition.2, by rw [views, transition.1]⟩
  | materialize i j a b record eagerI eagerJ success =>
      obtain ⟨_, installedI, installedJ⟩ :=
        accepted_pair_is_safe before.delayed i j a b success
      constructor
      · intro query outside
        by_cases isI : query = i
        · subst query
          exact eagerI.trans installedI.symm
        by_cases isJ : query = j
        · subst query
          exact eagerJ.trans installedJ.symm
        have notHidden : ¬ before.hidden query := by
          intro hidden
          exact outside ⟨hidden, isI, isJ⟩
        calc
          before.eager query = before.delayed query := agree query notHidden
          _ = (installPair before.delayed i j a b).1 query :=
            (pair_install_other_lookup before.delayed i j query a b isI isJ).symm
      · simp [views]
  | emit record =>
      exact ⟨agree, by simp [views]⟩

inductive ForwardTrace [DecidableEq Input] [DecidableEq Answer]
    (observe : Answer → Obs) :
    ForwardState Input Answer Obs → ForwardState Input Answer Obs → Prop
  | refl (state : ForwardState Input Answer Obs) : ForwardTrace observe state state
  | tail {first middle last : ForwardState Input Answer Obs}
      (step : ForwardStep observe first middle)
      (rest : ForwardTrace observe middle last) :
      ForwardTrace observe first last

theorem forward_trace_preserves
    [DecidableEq Input] [DecidableEq Answer] (observe : Answer → Obs)
    {first last : ForwardState Input Answer Obs}
    (invariant : ForwardInvariant first)
    (trace : ForwardTrace observe first last) :
    ForwardInvariant last := by
  induction trace with
  | refl => exact invariant
  | tail step rest ih =>
      exact ih (forward_step_preserves observe invariant step)

def forwardJointView
    (finish : Coin → ForwardState Input Answer Obs) : Coin → List Obs × List Obs :=
  fun coin => ((finish coin).eagerView, (finish coin).delayedView)

/-- Finite wrapper theorem. The coupling is constructed as `forwardJointView`,
its two projections have exactly the standalone eager/delayed marginals, and
the execution induction supplies agreement on every non-bad tape. `bad` tapes,
including aborts, are retained with their actual side-specific outputs. -/
theorem finite_witness_retaining_commitment_hop
    [DecidableEq Input] [DecidableEq Answer] [Fintype Coin] [Nonempty Coin]
    (observe : Answer → Obs)
    (weight : Coin → ℝ) (nonnegative : ∀ coin, 0 ≤ weight coin)
    (start finish : Coin → ForwardState Input Answer Obs)
    (bad : Coin → Bool)
    (initial : ∀ coin, ForwardInvariant (start coin))
    (execution : ∀ coin, bad coin = false →
      ForwardTrace observe (start coin) (finish coin))
    (test : List Obs → Bool) :
    SameUniformLaw
        (fun coin => (forwardJointView finish coin).1)
        (fun coin => (finish coin).eagerView) ∧
      SameUniformLaw
        (fun coin => (forwardJointView finish coin).2)
        (fun coin => (finish coin).delayedView) ∧
      |eventMass weight (fun coin => (finish coin).eagerView) test -
          eventMass weight (fun coin => (finish coin).delayedView) test| ≤
        badMass weight bad := by
  refine ⟨joint_run_left_marginal
      (fun coin => (finish coin).eagerView)
      (fun coin => (finish coin).delayedView),
    joint_run_right_marginal
      (fun coin => (finish coin).eagerView)
      (fun coin => (finish coin).delayedView), ?_⟩
  apply event_gap_le_bad_mass weight nonnegative _ _ bad
  intro coin good
  exact (forward_trace_preserves observe (initial coin) (execution coin good)).2

#print axioms forward_step_preserves
#print axioms forward_trace_preserves
#print axioms finite_witness_retaining_commitment_hop
end AspisV8PairedCommitment
