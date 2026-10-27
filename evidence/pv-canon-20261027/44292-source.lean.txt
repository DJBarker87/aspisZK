import R1Z.PV_Canon_Nat
namespace R1Z.PV_Canon
 theorem remainder_canonical (dividend : Nat) : dividend % P < P := by
  exact Nat.mod_lt _ (by unfold P; omega)
 theorem divpass_quotient_bound (remainder word : Nat)
    (hr : remainder < P) (hw : word < 4294967296) :
    (remainder * 4294967296 + word) / P < 4294967296 := by
  have bound : remainder * 4294967296 + word < P * 4294967296 := by
    unfold P at *; omega
  apply (Nat.div_lt_iff_lt_mul (by unfold P; omega)).mpr
  simpa only [Nat.mul_comm] using bound
 theorem divpass_u64_bound (remainder word : Nat)
    (hr : remainder < P) (hw : word < 4294967296) :
    remainder * 4294967296 + word < 18446744073709551616 := by
  unfold P at *; omega
#print axioms remainder_canonical
#print axioms divpass_quotient_bound
#print axioms divpass_u64_bound
end R1Z.PV_Canon
