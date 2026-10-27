import R1Z.CertSound

/-! Recovered env-J launcher smoke test, not a security theorem. -/
set_option autoImplicit false
namespace R1Z.EJR_Verification

theorem successor_nonzero (n : Nat) : Nat.succ n ≠ 0 := Nat.succ_ne_zero n

#print axioms successor_nonzero
#print axioms R1Z.CertSound.rinvCheck_sound
end R1Z.EJR_Verification
