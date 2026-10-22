import OraclePortCkptAbi2Reached

/-! The source writer permits raw noncanonical QM31 words. Identification
with the C5 exact field requires reached canonicality, not just a byte-wise
writer certificate. This isolates the missing representation obligation. -/
set_option autoImplicit false
namespace AspisR1.OraclePortCkptAbi3Canonical
open OraclePortCompactDraft OraclePortCheckpointPreparedC5

/-- On canonical raw words, the exact-field quotient retains the same bytes. -/
theorem canonical_word_bytes (n : Nat) (canonical : n < 2147483647) :
    le32 n = le32 (n : ZMod 2147483647).val := by
  rw [ZMod.val_natCast_of_lt canonical]

theorem modulus_bytes_ne_zero : le32 2147483647 ≠ le32 0 := by
  intro same
  have decoded := congrArg little same
  rw [little_le32 2147483647 (by omega),little_le32 0 (by omega)] at decoded
  omega

/-- A raw QM31 limb equal to P and the raw zero limb denote the same exact
field element but have different encodings. Arbitrary stored words in the
P6 writer domain therefore cannot all be identified with C5's canonical
encoder by applying the quotient map. No large vector is normalized. -/
theorem not_all_words_canonicalized :
    ¬ (∀ n : Nat, n < 4294967296 → le32 n = le32 (n : ZMod 2147483647).val) := by
  intro bridge
  have same := bridge 2147483647 (by omega)
  simp only [ZMod.natCast_self,ZMod.val_zero] at same
  exact modulus_bytes_ne_zero same

#print axioms canonical_word_bytes
#print axioms modulus_bytes_ne_zero
#print axioms not_all_words_canonicalized
end AspisR1.OraclePortCkptAbi3Canonical
