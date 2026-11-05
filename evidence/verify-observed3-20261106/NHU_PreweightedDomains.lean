import NHU_Preweighted
set_option autoImplicit false
namespace AspisR1.NHU_PreweightedDomains
/-- The frozen deployed uses are N2/N12/N16/N17 and the optimized shared N33.
Unoptimized N8 and nonshared N33 are disabled by the deployed feature graph. -/
theorem fixed_abi (n : Nat) (present : n=2 ∨ n=12 ∨ n=16 ∨ n=17 ∨ n=33)
 (start : Nat) (bound : start+n≤96) :
 0<n ∧ start≤96 ∧ start/4≤(start+n-1)/4 ∧ (start+n-1)/4<24 := by
 rcases present with h|h|h|h|h <;> subst n <;> omega
/-- Each lane borrow in the native from_fn closure is within the SAME array. -/
theorem source_index (n start group slot : Nat)
 (inside : start≤4*group+slot ∧ 4*group+slot<start+n) :
 4*group+slot-start<n := by omega
#print axioms fixed_abi
#print axioms source_index
end AspisR1.NHU_PreweightedDomains
