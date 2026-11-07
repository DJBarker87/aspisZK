import NLV_Algebra
set_option autoImplicit false
namespace AspisR1.NLV_ObservationIndex
/-- The native u16 index encoding loses NO proof-window coordinate. -/
theorem bound (j : Nat) (inside : j<57607) : j<65536 := by omega
theorem modulo (j : Nat) (inside : j<57607) : j%65536=j :=
 Nat.mod_eq_of_lt (bound j inside)
/-- Independent field selector and coordinate are necessary for frontier
coverage; correlated residues cannot be used to claim all cells. -/
theorem independent (field row col : Nat) (hf : field<9) (hr : row<64) (hc : col<32) :
 ∃ selector coordinate : Nat,selector<576 ∧ coordinate<57607 ∧
 selector%9=field ∧ selector/9=row ∧ coordinate%32=col := by
 refine ⟨9*row+field,col,by omega,by omega,?_,?_,Nat.mod_eq_of_lt hc⟩
 · omega
 · omega
#print axioms bound
#print axioms modulo
#print axioms independent
end AspisR1.NLV_ObservationIndex
