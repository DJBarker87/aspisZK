import Std
set_option autoImplicit false
namespace NEI_AccumCounterDomains
/-- Global query progress and transaction-local residue terms are independent:
TX2 resets pending terms while retaining the checkpoint's query index. -/
theorem independent (query terms lane : Nat) (hq : query<22) (ht : terms<22)
 (hl : lane<64) :
 query+1≤4096 ∧ terms+1≤4096 ∧ query*64+lane<4096 := by omega

/-- Source basis writes fit the same 256-word array at every reached stage. -/
theorem basis_window (stage lane : Nat) (hs : stage≤32) (hl : lane<stage) :
 lane<256 ∧ stage+lane<64 ∧ stage+lane<256 ∧ stage*2≤64 := by omega

/-- A successful source push retains local terms; its final increment cannot
be justified by equating local terms with the global query counter. -/
theorem local_successor (terms mid : Nat) (same : mid=terms) (bound : terms<22) :
 mid+1≤4096 := by omega
#print axioms independent
#print axioms basis_window
#print axioms local_successor
end NEI_AccumCounterDomains
