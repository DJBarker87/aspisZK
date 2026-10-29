import PV_L2E_Dividend
set_option autoImplicit false
namespace PV_L2E_ArrayMemory
abbrev Memory := Nat → Nat

def store (a : Memory) (i v : Nat) : Memory := fun j => if j=i then v else a j

def backwards (a : Memory) : Nat → List Nat
  | 0 => []
  | n+1 => a n::backwards a n

theorem store_here (a : Memory) (i v : Nat) : store a i v i=v := by simp [store]
theorem store_elsewhere (a : Memory) (i j v : Nat) (h : j≠i) :
    store a i v j=a j := by simp [store,h]

theorem length (a : Memory) (n : Nat) : (backwards a n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [backwards,ih]

/-- A direct array store is retained. It affects exactly one slot and leaves
all lower, not-yet-divided words unchanged. -/
theorem lower_unchanged (a : Memory) (n i v : Nat) (hi : n ≤ i) :
    backwards (store a i v) n=backwards a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [backwards,backwards,store_elsewhere a i n v (by omega),ih (by omega)]

theorem bounds (a : Memory) (n : Nat) (h : ∀ i, i<n → a i<PV_L2D_DivisionBounds.B) :
    ∀ x∈backwards a n,x<PV_L2D_DivisionBounds.B := by
  induction n with
  | zero => simp [backwards]
  | succ n ih =>
    intro x hx
    simp only [backwards,List.mem_cons] at hx
    rcases hx with rfl|hx
    · exact h n (by omega)
    · exact ih (fun i hi => h i (by omega)) x hx

#print axioms store_here
#print axioms store_elsewhere
#print axioms length
#print axioms lower_unchanged
#print axioms bounds
end PV_L2E_ArrayMemory
