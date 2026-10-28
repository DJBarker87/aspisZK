import Port4C_PrefixMeaning
import Port4C_BatchInverse
import LPf_BaseMultiply
set_option autoImplicit false
namespace NBS_GeometryDomains
open Aeneas Aeneas.Std AspisR1
/-- All real geometry sizes, including empty ranges; no allocation success
or result vector is assumed. TX2 uses start10/end22. -/
theorem sizes (start stop : Nat) (order : start≤stop) (hi : stop≤22) :
    stop-start≤22 ∧ (stop-start)*5≤110 ∧
    (start=10 → stop-start≤12 ∧ (stop-start)*5≤60) := by omega

theorem aligned (u : Nat) (bound : u<262144) :
    u/4*4<262144 ∧ u/4*4+3<262144 ∧
    u/4*4≤u ∧ u≤u/4*4+3 := by omega

/-- A selected record is exactly five consecutive entries in the SAME flat
vector. This also proves the allocation/index arithmetic does not overflow. -/
theorem group (n i j : Nat) (hn : n≤22) (hi : i<n) (hj : j<5) :
    5*i+j<5*n ∧ 5*i+j<110 ∧ 5*i+j<18446744073709551616 := by omega

theorem accessor (start count index : Nat) (lo : start≤index) (hi : index<start+count) :
    index-start<count ∧ start+(index-start)=index := by omega

/-- Accepted zero checks and canonicality imply nonzero natural residues,
so a successful native path never inverts field zero. -/
theorem nonzero (word : Nat) (canonical : word<2147483647) (guard : word≠0) :
    word%2147483647≠0 := by rw [Nat.mod_eq_of_lt canonical];exact guard

#print axioms sizes
#print axioms aligned
#print axioms group
#print axioms accessor
#print axioms nonzero
#print axioms AspisR1.Port4C_PrefixMeaning.total
#print axioms AspisR1.Port4C_BatchInverse.backward_exact
end NBS_GeometryDomains
