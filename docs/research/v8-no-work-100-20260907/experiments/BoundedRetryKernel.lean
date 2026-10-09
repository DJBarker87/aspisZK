import RelationCompatibleMoment

/-! Finite retry mass with an arbitrary history update and immediate
ordinary failure. Conditional one-step laws must hold at every history;
this theorem does not infer freshness from transcript labels. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.BoundedRetryKernel
noncomputable section
open Finset
open AspisV8.JointImageGame AspisV8.RelationCompatibleMoment
variable {O H V : Type*} [DecidableEq V]

def hit (draw : H → O → Option (V × H)) (accept : V → Prop)
    [DecidablePred accept] (h : H) (target : V) (coin : O) : ℚ :=
  match draw h coin with
  | none => 0
  | some (value, _) => if accept value ∧ value = target then 1 else 0

def reject (draw : H → O → Option (V × H)) (accept : V → Prop)
    [DecidablePred accept] (h : H) (coin : O) : ℚ :=
  match draw h coin with
  | none => 0
  | some (value, _) => if accept value then 0 else 1

def mass (coins : Finset O) (draw : H → O → Option (V × H))
    (accept : V → Prop) [DecidablePred accept] : Nat → H → V → ℚ
  | 0, _, _ => 0
  | n+1, h, target => avg coins (fun coin =>
      match draw h coin with
      | none => 0
      | some (value, next) =>
          if accept value then (if value = target then 1 else 0)
          else mass coins draw accept n next target)

def geometric : Nat → ℚ → ℚ
  | 0, _ => 0
  | n+1, r => 1 + r*geometric n r

theorem geometric_three (r : ℚ) : geometric 3 r = 1+r+r^2 := by
  simp only [geometric]
  ring

theorem avg_mul_right (coins : Finset O) (f : O → ℚ) (c : ℚ) :
    avg coins (fun coin => f coin*c) = avg coins f*c := by
  simp only [avg, ← Finset.sum_mul]
  ring

/-- A rejected successful value can update all history. Only the stated
history-uniform one-step masses are used; a failure is never retried. -/
theorem mass_eq (coins : Finset O) (draw : H → O → Option (V × H))
    (accept : V → Prop) [DecidablePred accept] (target : V) (u r : ℚ)
    (hitLaw : ∀ h, avg coins (hit draw accept h target) = u)
    (rejectLaw : ∀ h, avg coins (reject draw accept h) = r)
    (n : Nat) (h : H) : mass coins draw accept n h target = u*geometric n r := by
  induction n generalizing h with
  | zero => simp [mass, geometric]
  | succ n ih =>
      have split : mass coins draw accept (n+1) h target =
          avg coins (fun coin => hit draw accept h target coin +
            reject draw accept h coin*(u*geometric n r)) := by
        rw [mass]
        congr 1
        funext coin
        cases drawn : draw h coin with
        | none => simp [hit, reject, drawn]
        | some pair =>
            rcases pair with ⟨value, next⟩
            by_cases accepted : accept value
            · simp [hit, reject, drawn, accepted]
            · simp [hit, reject, drawn, accepted, ih]
      rw [split, avg_add, avg_mul_right, hitLaw, rejectLaw, geometric]
      ring

theorem mass_three (coins : Finset O) (draw : H → O → Option (V × H))
    (accept : V → Prop) [DecidablePred accept] (target : V) (u r : ℚ)
    (hitLaw : ∀ h, avg coins (hit draw accept h target) = u)
    (rejectLaw : ∀ h, avg coins (reject draw accept h) = r) (h : H) :
    mass coins draw accept 3 h target = u*(1+r+r^2) := by
  rw [mass_eq coins draw accept target u r hitLaw rejectLaw, geometric_three]

#print axioms geometric_three
#print axioms avg_mul_right
#print axioms mass_eq
#print axioms mass_three
end
end AspisV8.BoundedRetryKernel
