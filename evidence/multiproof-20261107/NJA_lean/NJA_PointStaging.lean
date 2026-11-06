import NJA_PointFrame
set_option autoImplicit false
namespace NJA_PointStaging
open NJA_PointFrame
variable {α : Type} {width : Nat}

theorem coordinates (before after : State width α) (i : Fin width) (x : α)
 (native : ∀ k, after k = if k=i then x else before k) : after=write before i x := by
 funext k;exact native k

theorem replay (initial : State width α) (f : Fin width → α → α)
 (steps : Nat → State width α) (start : steps 0=initial)
 (native : ∀ (n : Nat) (h : n<width), ∀ k,
   steps (n+1) k = if k=⟨n,h⟩ then f ⟨n,h⟩ (steps n ⟨n,h⟩) else steps n k)
 (n : Nat) (hn : n≤width) : steps n = run initial f n := by
 induction n with
 | zero => exact start
 | succ n ih =>
   have h : n<width := by omega
   have step := coordinates (steps n) (steps (n+1)) ⟨n,h⟩ (f ⟨n,h⟩ (steps n ⟨n,h⟩)) (native n h)
   rw [step,ih (by omega),run,dif_pos h]

theorem complete (initial : State width α) (f : Fin width → α → α)
 (steps : Nat → State width α) (start : steps 0=initial)
 (native : ∀ (n : Nat) (h : n<width), ∀ k,
   steps (n+1) k = if k=⟨n,h⟩ then f ⟨n,h⟩ (steps n ⟨n,h⟩) else steps n k) :
 steps width = fun i => f i (initial i) := by
 rw [replay initial f steps start native width (by omega),NJA_PointFrame.complete]

#print axioms coordinates
#print axioms replay
#print axioms complete
end NJA_PointStaging
