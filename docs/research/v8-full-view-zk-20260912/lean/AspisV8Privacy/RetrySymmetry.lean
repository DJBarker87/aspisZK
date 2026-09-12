import Std

/-! IMPORTED FIRST ATTEMPT; COMPILED IN THIS WORKSTREAM. A finite candidate-tape controller with
explicit exhaustion and consumed length. Uniformity of the ACTUAL SHA-backed
tape is not a premise silently supplied here; it remains a separate hybrid.
-/
set_option autoImplicit false
namespace AspisV8Privacy

structure RetryResult (A : Type) where
  result : Option A
  consumed : Nat
  deriving DecidableEq, Repr

def firstHit {A : Type} : List (Option A) → RetryResult A
  | [] => ⟨none, 0⟩
  | some a :: _ => ⟨some a, 1⟩
  | none :: rest =>
      let r := firstHit rest
      ⟨r.result, r.consumed + 1⟩

def mapRetry {A B : Type} (f : A → B) (r : RetryResult A) : RetryResult B :=
  ⟨r.result.map f, r.consumed⟩

/-- Renaming accepted values preserves stopping/abort behaviour as well as
renaming the output. It is not success-conditioned sampling. -/
theorem firstHit_map {A B : Type} (f : A → B) (tape : List (Option A)) :
    firstHit (tape.map (Option.map f)) = mapRetry f (firstHit tape) := by
  induction tape with
  | nil => rfl
  | cons a rest ih =>
      cases a with
      | some x => rfl
      | none => simp [firstHit, mapRetry, ih]

theorem firstHit_consumed_le {A : Type} (tape : List (Option A)) :
    (firstHit tape).consumed ≤ tape.length := by
  induction tape with
  | nil => simp [firstHit]
  | cons a rest ih =>
      cases a with
      | some x => simp [firstHit]
      | none => simp only [firstHit, List.length_cons]; omega

theorem firstHit_all_rejected {A : Type} (n : Nat) :
    firstHit (List.replicate n (none : Option A)) = ⟨none,n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, firstHit, ih]

#print axioms firstHit_map
#print axioms firstHit_consumed_le
#print axioms firstHit_all_rejected
end AspisV8Privacy
