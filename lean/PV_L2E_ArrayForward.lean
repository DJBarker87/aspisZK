import PV_L2E_ArrayMemory
set_option autoImplicit false
namespace PV_L2E_ArrayForward
open PV_L2E_ArrayMemory

def slice (a : Memory) : Nat → Nat → List Nat
  | _,0 => []
  | i,n+1 => a i::slice a (i+1) n

theorem length (a : Memory) (i n : Nat) : (slice a i n).length=n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [slice,ih]

theorem store_outside (a : Memory) (i n j v : Nat) (outside : j<i ∨ i+n≤j) :
    slice (store a j v) i n=slice a i n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    rw [slice,slice,store_elsewhere a j i v (by omega),ih (i+1) (by omega)]

theorem bounds (a : Memory) (i n cap : Nat) (h : ∀ j,i≤j → j<i+n → a j<cap) :
    ∀ x∈slice a i n,x<cap := by
  induction n generalizing i with
  | zero => simp [slice]
  | succ n ih =>
    intro x hx
    simp only [slice,List.mem_cons] at hx
    rcases hx with rfl|hx
    · exact h i (by omega) (by omega)
    · exact ih (i+1) (fun j hj hk => h j (by omega) (by omega)) x hx

#print axioms length
#print axioms store_outside
#print axioms bounds
end PV_L2E_ArrayForward
