import Std

/-! Visible attempt events and exhaustion are retained. Equality of complete
paired attempt traces transports stopping behaviour; no IID premise appears. -/
set_option autoImplicit false

namespace AspisV8Privacy

structure RepairAttempt (V N : Type) where
  publicEvents : List N
  released : Option V
  deriving Repr, DecidableEq

structure RepairOutcome (V N : Type) where
  publicEvents : List N
  released : Option V
  attemptsUsed : Nat
  deriving Repr, DecidableEq

def runRepairAttempts {V N : Type} : List (RepairAttempt V N) → RepairOutcome V N
  | [] => ⟨[], none, 0⟩
  | attempt :: rest =>
      match attempt.released with
      | some value => ⟨attempt.publicEvents, some value, 1⟩
      | none =>
          let next := runRepairAttempts rest
          ⟨attempt.publicEvents ++ next.publicEvents, next.released, next.attemptsUsed + 1⟩

theorem repair_attempts_used_le_length {V N : Type} (attempts : List (RepairAttempt V N)) :
    (runRepairAttempts attempts).attemptsUsed ≤ attempts.length := by
  induction attempts with
  | nil => simp [runRepairAttempts]
  | cons attempt rest ih =>
      cases h : attempt.released with
      | some value => simp [runRepairAttempts, h]
      | none => simp only [runRepairAttempts, h, List.length_cons]; omega

theorem equal_attempt_views_preserve_release {V N : Type}
    (left right : List (RepairAttempt V N)) (same : left = right) :
    runRepairAttempts left = runRepairAttempts right := by
  rw [same]

def gateRepairCandidate {C V N : Type} (events : C → List N)
    (gate : C → Bool) (view : C → V) (candidate : C) : RepairAttempt V N :=
  ⟨events candidate, if gate candidate then some (view candidate) else none⟩

theorem gated_attempt_transport {C D V N : Type}
    (leftEvents : C → List N) (rightEvents : D → List N)
    (leftGate : C → Bool) (rightGate : D → Bool)
    (leftView : C → V) (rightView : D → V) (transport : C → D)
    (sameEvents : ∀ c, rightEvents (transport c) = leftEvents c)
    (sameGate : ∀ c, rightGate (transport c) = leftGate c)
    (sameReleased : ∀ c, leftGate c = true → rightView (transport c) = leftView c)
    (candidate : C) :
    gateRepairCandidate rightEvents rightGate rightView (transport candidate) =
      gateRepairCandidate leftEvents leftGate leftView candidate := by
  cases h : leftGate candidate with
  | false => simp [gateRepairCandidate, sameEvents candidate, sameGate candidate, h]
  | true => simp [gateRepairCandidate, sameEvents candidate, sameGate candidate, h,
      sameReleased candidate h]

#print axioms repair_attempts_used_le_length
#print axioms equal_attempt_views_preserve_release
#print axioms gated_attempt_transport

end AspisV8Privacy
