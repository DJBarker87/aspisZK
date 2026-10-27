import R1Z.PrivacyR1HeadlineDeployedReal

namespace R1Z.EJS_Verification
/-- Non-vacuous infrastructure smoke test; no security premise is discharged. -/
theorem successor_nonzero (n : Nat) : Nat.succ n ≠ 0 := Nat.succ_ne_zero n
#print axioms successor_nonzero
end R1Z.EJS_Verification
