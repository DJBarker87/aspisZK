import AspisV8PairedCommitment.ForwardHop
import AspisV8H1C2.FiniteTransport
import Mathlib.Data.List.Basic

/-!
Concrete reserve/query/open interpreters, not caller-supplied finish functions.
Runs are uniform fixed-slot finite experiments: each tick enumerates the same
nonempty answer alphabet, retaining repeated outcomes with multiplicity.
-/
set_option autoImplicit false
namespace AspisV8R9
open AspisV8PairedCommitment

inductive Mode where | eager | delayed
inductive Observation (I A : Type) where
  | answer : I → A → Observation I A
  | reserved : Nat → A → Observation I A
  | opened : I → A → I → A → Observation I A
  | emit : Nat → Observation I A
  | abort : Nat → Observation I A
  | halt : Observation I A
inductive Command (I : Type) where
  | query : I → Command I
  | reserve : Nat → I → Command I
  | openPair : Nat → Nat → Command I
  | emit : Nat → Command I
  | halt : Command I

structure Machine (I A : Type) where
  table : Table I A
  pending : Nat → Option (I × A)
  /-- Private proof-side deferred-input set; it is not visible to `policy`. -/
  hidden : I → Prop
  view : List (Observation I A)
  stopped : Bool

variable {I A : Type} [DecidableEq I] [DecidableEq A]

def appendObservation (s : Machine I A) (o : Observation I A) : Machine I A :=
  { s with view := s.view ++ [o] }
def abortMachine (s : Machine I A) (reason : Nat) : Machine I A :=
  { s with view := s.view ++ [.abort reason], stopped := true }

def advance (mode : Mode) (s : Machine I A) (c : Command I) (fresh : A) : Machine I A :=
  if s.stopped then s else
  match c with
  | .halt => { s with view := s.view ++ [.halt], stopped := true }
  | .emit n => appendObservation s (.emit n)
  | .query input =>
      let result := queryStep s.table input fresh
      appendObservation { s with table := result.2 } (.answer input result.1)
  | .reserve slot input =>
      match s.pending slot with
      | some (oldInput, oldAnswer) =>
          if oldInput = input then appendObservation s (.reserved slot oldAnswer)
          else abortMachine s 1
      | none =>
          let result := match mode with
            | .eager => queryStep s.table input fresh
            | .delayed => (fresh, s.table)
          appendObservation
            { s with
              table := result.2
              pending := fun i => if i = slot then some (input, result.1) else s.pending i
              hidden := fun query => query = input ∨ s.hidden query }
            (.reserved slot result.1)
  | .openPair left right =>
      match s.pending left, s.pending right with
      | some (i, a), some (j, b) =>
          if i = j then abortMachine s 2 else
          match mode with
          | .eager => appendObservation
              { s with hidden := fun query => s.hidden query ∧ query ≠ i ∧ query ≠ j }
              (.opened i a j b)
          | .delayed =>
              let installed := installPair s.table i j a b
              if installed.2 then
                appendObservation
                  { s with
                    table := installed.1
                    hidden := fun query => s.hidden query ∧ query ≠ i ∧ query ≠ j }
                  (.opened i a j b)
              else abortMachine s 3
      | _, _ => abortMachine s 4

/-- The scheduler sees only its own past observations. Fixed witness-dependent
parameters may be captured by the policy, but not future random slots. -/
def tick (mode : Mode) (policy : List (Observation I A) → Command I)
    (s : Machine I A) (fresh : A) : Machine I A :=
  advance mode s (policy s.view) fresh

def jointTick (policy : List (Observation I A) → Command I)
    (s : Machine I A × Machine I A) (fresh : A) : Machine I A × Machine I A :=
  (tick .eager policy s.1 fresh, tick .delayed policy s.2 fresh)

def needsFresh (mode : Mode) (s : Machine I A) (command : Command I) : Prop :=
  s.stopped = false ∧ match command with
    | .query input => s.table input = none
    | .reserve slot input => s.pending slot = none ∧
        match mode with
        | .eager => s.table input = none
        | .delayed => True
    | _ => False

/-- A fixed tape slot which the lazy machine does not need is observationally
and state-wise irrelevant. This is the local integration-out fact used by the
fixed-slot uniform experiment; it is proved from the actual command semantics. -/
theorem advance_fresh_irrelevant (mode : Mode) (s : Machine I A)
    (command : Command I) (left right : A)
    (ignored : ¬ needsFresh mode s command) :
    advance mode s command left = advance mode s command right := by
  unfold needsFresh at ignored
  by_cases stopped : s.stopped = true
  · simp [advance, stopped]
  have running : s.stopped = false := Bool.eq_false_of_not_eq_true stopped
  simp only [advance, running, Bool.false_eq_true, ↓reduceIte]
  cases command with
  | halt => rfl
  | emit => rfl
  | openPair first second => rfl
  | query input =>
      have cached : s.table input ≠ none := by
        intro missing
        exact ignored ⟨running, missing⟩
      cases found : s.table input with
      | none => exact (cached found).elim
      | some answer => simp [queryStep, found]
  | reserve slot input =>
      cases pending : s.pending slot with
      | some old => simp [pending]
      | none =>
          cases mode with
          | delayed => exact (ignored ⟨running, pending, trivial⟩).elim
          | eager =>
              have cached : s.table input ≠ none := by
                intro missing
                exact ignored ⟨running, pending, missing⟩
              cases found : s.table input with
              | none => exact (cached found).elim
              | some answer => simp [pending, queryStep, found]

theorem tick_fresh_irrelevant (mode : Mode)
    (policy : List (Observation I A) → Command I) (s : Machine I A)
    (left right : A) (ignored : ¬ needsFresh mode s (policy s.view)) :
    tick mode policy s left = tick mode policy s right := by
  exact advance_fresh_irrelevant mode s (policy s.view) left right ignored

/-- Own list binder, so the proof does not depend on monad notation. -/
def branches {X Y : Type} (xs : List X) (f : X → List Y) : List Y :=
  match xs with
  | [] => []
  | x :: rest => f x ++ branches rest f

theorem map_branches {X Y Z : Type} (xs : List X) (f : X → List Y) (g : Y → Z) :
    (branches xs f).map g = branches xs (fun x => (f x).map g) := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simp [branches, ih]

def runTicks {X : Type} (alphabet : List A) (step : X → A → X) : Nat → X → List X
  | 0, s => [s]
  | n+1, s => branches alphabet (fun a => runTicks alphabet step n (step s a))

theorem project_runTicks {X Y : Type} (alphabet : List A)
    (left : X → A → X) (right : Y → A → Y) (project : X → Y)
    (oneStep : ∀ s a, project (left s a) = right (project s) a)
    (fuel : Nat) (s : X) :
    (runTicks alphabet left fuel s).map project =
      runTicks alphabet right fuel (project s) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ n ih =>
      simp only [runTicks, map_branches]
      have pointwise : (fun a => (runTicks alphabet left n (left s a)).map project) =
          (fun a => runTicks alphabet right n (right (project s) a)) := by
        funext a
        rw [ih, oneStep]
      rw [pointwise]

/-- Exact equality of multiplicity lists, before normalization by
`|alphabet|^fuel`. The right side executes the actual eager interpreter. -/
theorem operational_left_marginal (alphabet : List A)
    (policy : List (Observation I A) → Command I)
    (fuel : Nat) (left right : Machine I A) :
    (runTicks alphabet (jointTick policy) fuel (left, right)).map Prod.fst =
      runTicks alphabet (tick .eager policy) fuel left := by
  exact project_runTicks alphabet (jointTick policy) (tick .eager policy)
    Prod.fst (fun _ _ => rfl) fuel (left, right)

theorem operational_right_marginal (alphabet : List A)
    (policy : List (Observation I A) → Command I)
    (fuel : Nat) (left right : Machine I A) :
    (runTicks alphabet (jointTick policy) fuel (left, right)).map Prod.snd =
      runTicks alphabet (tick .delayed policy) fuel right := by
  exact project_runTicks alphabet (jointTick policy) (tick .delayed policy)
    Prod.snd (fun _ _ => rfl) fuel (left, right)

def runFixedTape {X : Type} (step : X → A → X) (fuel : Nat)
    (initial : X) (tape : Fin fuel → A) : X :=
  (List.finRange fuel).foldl (fun state index => step state (tape index)) initial

theorem project_runFixedTape {X Y : Type}
    (left : X → A → X) (right : Y → A → Y) (project : X → Y)
    (oneStep : ∀ s a, project (left s a) = right (project s) a)
    (fuel : Nat) (initial : X) (tape : Fin fuel → A) :
    project (runFixedTape left fuel initial tape) =
      runFixedTape right fuel (project initial) tape := by
  unfold runFixedTape
  generalize List.finRange fuel = indices
  induction indices generalizing initial with
  | nil => rfl
  | cons index rest ih =>
      simp only [List.foldl_cons]
      rw [ih, oneStep]

def operationalJointFixedTape
    (policy : List (Observation I A) → Command I) (fuel : Nat)
    (initial : Machine I A × Machine I A) (tape : Fin fuel → A) :
    Machine I A × Machine I A :=
  runFixedTape (jointTick policy) fuel initial tape

theorem operational_joint_fixed_left
    (policy : List (Observation I A) → Command I) (fuel : Nat)
    (initial : Machine I A × Machine I A) (tape : Fin fuel → A) :
    (operationalJointFixedTape policy fuel initial tape).1 =
      runFixedTape (tick .eager policy) fuel initial.1 tape := by
  exact project_runFixedTape (jointTick policy) (tick .eager policy) Prod.fst
    (fun _ _ => rfl) fuel initial tape

theorem operational_joint_fixed_right
    (policy : List (Observation I A) → Command I) (fuel : Nat)
    (initial : Machine I A × Machine I A) (tape : Fin fuel → A) :
    (operationalJointFixedTape policy fuel initial tape).2 =
      runFixedTape (tick .delayed policy) fuel initial.2 tape := by
  exact project_runFixedTape (jointTick policy) (tick .delayed policy) Prod.snd
    (fun _ _ => rfl) fuel initial tape

/-- Connection to the repository's exact finite uniform-law API. Unlike R8's
arbitrary `finish`, both sides here are the displayed causal interpreters. -/
theorem operational_fixed_tape_laws [Fintype A] [Nonempty A]
    (policy : List (Observation I A) → Command I) (fuel : Nat)
    (initial : Machine I A × Machine I A) :
    AspisV8H1C2.SameUniformLaw
        (fun tape => (operationalJointFixedTape policy fuel initial tape).1)
        (fun tape => runFixedTape (tick .eager policy) fuel initial.1 tape) ∧
      AspisV8H1C2.SameUniformLaw
        (fun tape => (operationalJointFixedTape policy fuel initial tape).2)
        (fun tape => runFixedTape (tick .delayed policy) fuel initial.2 tape) := by
  constructor
  · exact AspisV8H1C2.sameUniformLaw_of_equiv _ _
      (Equiv.refl (Fin fuel → A))
      (fun tape => (operational_joint_fixed_left policy fuel initial tape).symm)
  · exact AspisV8H1C2.sameUniformLaw_of_equiv _ _
      (Equiv.refl (Fin fuel → A))
      (fun tape => (operational_joint_fixed_right policy fuel initial tape).symm)

#print axioms project_runTicks
#print axioms operational_left_marginal
#print axioms operational_right_marginal
#print axioms advance_fresh_irrelevant
#print axioms operational_fixed_tape_laws
end AspisV8R9
