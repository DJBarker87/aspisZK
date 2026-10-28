import PV_L2D_ZeroTail
import Mathlib.Tactic
set_option autoImplicit false
namespace PV_L2D_IndexedTail
open PV_L2D_ZeroTail

/-- Fuel is a proof device, not an extra native guard. `none` means the fuel
was insufficient while the native loop still wanted another iteration. -/
def loop : Nat → Nat → Nat → (Nat → Nat) → Option (Outcome × List Event)
  | 0, i, end_, _ => if i < end_ then none else some (.ok, [.loopTest i false])
  | n+1, i, end_, cell =>
    if i < end_ then
      if cell i = 0 then
        (loop n (i+1) end_ cell).map (fun r =>
          (r.1, .loopTest i true :: .read i :: .zeroTest i true :: r.2))
      else some (.wrongField, [.loopTest i true, .read i, .zeroTest i false])
    else some (.ok, [.loopTest i false])

/-- Full-result refinement of direct indexed reads to the suffix model.
There is no accepted-run hypothesis and no assumption about limb values. -/
theorem complete (xs : List Nat) (i : Nat) (cell : Nat → Nat)
    (h : ∀ k (hk : k < xs.length), cell (i+k) = xs[k]) :
    loop xs.length i (i+xs.length) cell = some (run i xs) := by
  induction xs generalizing i with
  | nil => simp [loop,run]
  | cons x xs ih =>
    have hx : cell i = x := by
      have h0 := h 0 (by simp)
      change cell (i+0) = x at h0
      exact h0
    have ht : ∀ k (hk : k < xs.length), cell (i+1+k) = xs[k] := by
      intro k hk
      have he := h (k+1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he
    by_cases hz : x=0
    · simp only [List.length_cons, loop, show i < i + (xs.length+1) by omega,
        ite_true, hx, hz]
      rw [show i+(xs.length+1)=(i+1)+xs.length by omega, ih (i+1) ht]
      simp [run,hz]
    · simp [loop, hx, hz, run]
#print axioms complete

theorem array_eight (xs : List Nat) (i : Nat) (cell : Nat → Nat)
    (len : i+xs.length = 8)
    (h : ∀ k (hk : k < xs.length), cell (i+k) = xs[k]) :
    loop xs.length i 8 cell = some (run i xs) := by
  rw [← len]
  exact complete xs i cell h
#print axioms array_eight

theorem honest_eight (xs : List Nat) (i : Nat) (cell : Nat → Nat)
    (len : i+xs.length = 8)
    (h : ∀ k (hk : k < xs.length), cell (i+k) = xs[k])
    (zero : ∀ x ∈ xs, x=0) :
    loop xs.length i 8 cell = some (.ok,passing i xs.length) := by
  rw [array_eight xs i cell len h, complete_passing i xs zero]
#print axioms honest_eight
end PV_L2D_IndexedTail
