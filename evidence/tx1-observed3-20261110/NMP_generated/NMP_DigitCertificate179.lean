import NMP_PassCertificate179
set_option autoImplicit false
namespace AspisR1.NMP_DigitCertificate179
open SamplerMachineBounds SamplerWordPass SamplerRepeatedPass
/-- Any finite number of passes has a certificate on the SAME starting words.
Only the generic pass theorem is applied; no concrete recurrence is reduced. -/
theorem source (n : Nat) (xs : List UInt32) :
 LPk_Induction.Digits n xs (run n xs).1 (run n xs).2 := by
 obtain ⟨digits,last,trace⟩ := NBL_PassConstruct.digits n xs
 have same := LPk_Induction.digits_join trace
 rw [←same]
 exact trace
#print axioms source
end AspisR1.NMP_DigitCertificate179
