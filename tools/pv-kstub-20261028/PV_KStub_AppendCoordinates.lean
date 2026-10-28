import Std
namespace PV_KStub_AppendCoordinates
/-- Value-only append view; no allocator or pointer claim. -/
def appended {α : Type} (prefix tail : Nat → α) (n k : Nat) : α :=
  if k < n then prefix k else tail (k-n)
theorem prefix_frame {α : Type} (prefix tail : Nat → α) (n k : Nat) (h : k<n) :
    appended prefix tail n k = prefix k := by simp only [appended, if_pos h]
theorem tail_value {α : Type} (prefix tail : Nat → α) (n j : Nat) :
    appended prefix tail n (n+j) = tail j := by
  have h : ¬ n+j<n := by omega
  have hs : n+j-n=j := by omega
  simp only [appended, if_neg h, hs]
theorem length_bound (n m : Nat) (hn : n≤2) (hm : m≤1) : n+m≤3 := by omega
#print axioms prefix_frame
#print axioms tail_value
#print axioms length_bound
end PV_KStub_AppendCoordinates
