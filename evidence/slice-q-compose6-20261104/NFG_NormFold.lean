import NFG_NormNatural
set_option autoImplicit false
namespace NFG_NormFold
/-- Multiplication residues followed by addition have the same norm; the
hypothesis is a local primitive value law, never an assumed inverse result. -/
theorem reduced_nonzero (a b : Nat) (ha : a<2147483647) (hb : b<2147483647)
 (live : ¬(a=0 ∧ b=0)) :
 (((a*a)%2147483647+(b*b)%2147483647)%2147483647)≠0 := by
 rw [←Nat.add_mod]
 exact NFG_NormNatural.nonzero a b ha hb live

theorem backend_domain (a b norm : Nat) (ha : a<2147483647) (hb : b<2147483647)
 (live : ¬(a=0 ∧ b=0))
 (same : norm=((a*a)%2147483647+(b*b)%2147483647)%2147483647) :
 norm<2147483647 ∧ norm≠0 := by
 constructor
 · rw [same];exact Nat.mod_lt _ (by decide)
 · rw [same];exact reduced_nonzero a b ha hb live
#print axioms reduced_nonzero
#print axioms backend_domain
end NFG_NormFold
