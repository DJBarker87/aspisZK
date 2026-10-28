import NCI_ResidueBounds
set_option autoImplicit false
namespace AspisR1.NCI_ResidueInvariant
open NCI_ResidueBounds

def fold (x : Nat) := x % 2147483648 + x / 2147483648
def valid (raw terms : Nat) := raw < Boundary + (terms % 4)*MaxProduct
def step (raw product terms : Nat) :=
  if terms % 4 = 3 then fold (raw+product) else raw+product

theorem fold_mod (x : Nat) : fold x % P = x % P := by
  have hx := Nat.mod_add_div x 2147483648
  unfold fold
  generalize hr : x % 2147483648 = r at *
  generalize hq : x / 2147483648 = q at *
  have eq : r+q+2147483647*q = x := by omega
  calc
    (r+q)%P = (r+q+2147483647*q)%P := by simp [P, Nat.add_mod, Nat.mul_mod]
    _ = x%P := congrArg (fun a => a%P) eq

theorem step_mod (raw product terms : Nat) :
    step raw product terms % P = (raw+product)%P := by
  unfold step
  split
  · exact fold_mod _
  · rfl

theorem step_valid (raw product terms : Nat) (hv : valid raw terms)
    (hp : product ≤ MaxProduct) : valid (step raw product terms) (terms+1) := by
  have ht : terms%4<4 := Nat.mod_lt _ (by decide)
  have nowrap := group_nowrap raw product (terms%4) ht hv hp
  unfold step
  split
  · rename_i flush
    have hz : (terms+1)%4=0 := flush_schedule terms flush
    simp only [valid, hz, Nat.zero_mul, Nat.add_zero]
    exact fold_boundary _ nowrap
  · rename_i noflush
    have advance : (terms+1)%4=terms%4+1 := by omega
    simp only [valid,advance]
    exact next_partial _ _ _ hv hp

def run (raw terms : Nat) : List Nat → Nat
  | [] => raw
  | p::ps => run (step raw p terms) (terms+1) ps

theorem run_valid (raw terms : Nat) (ps : List Nat)
    (hv : valid raw terms) (hp : ∀ p ∈ ps, p ≤ MaxProduct) :
    valid (run raw terms ps) (terms+ps.length) := by
  induction ps generalizing raw terms with
  | nil => simpa [run] using hv
  | cons p ps ih =>
    have h := ih (step raw p terms) (terms+1)
      (step_valid raw p terms hv (hp p (by simp))) (by intro q hq; exact hp q (by simp [hq]))
    simpa [run,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem run_mod (raw terms : Nat) (ps : List Nat) :
    run raw terms ps % P = (raw+ps.sum)%P := by
  induction ps generalizing raw terms with
  | nil => simp [run]
  | cons p ps ih =>
    simp only [run, List.sum_cons]
    rw [ih]
    calc
      (step raw p terms+ps.sum)%P = ((raw+p)+ps.sum)%P := by
        rw [Nat.add_mod, step_mod, ← Nat.add_mod]
      _ = (raw+(p+ps.sum))%P := by rw [Nat.add_assoc]
#print axioms fold_mod
#print axioms step_mod
#print axioms step_valid
#print axioms run_valid
#print axioms run_mod
end AspisR1.NCI_ResidueInvariant
