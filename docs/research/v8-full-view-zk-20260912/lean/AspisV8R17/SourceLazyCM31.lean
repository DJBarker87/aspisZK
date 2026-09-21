import AspisV8R17.RawReducer

/-! Current CM31 raw-product deltas relative to the retained arithmetic
extraction. Reuse the literal two-fold reducer; do not assume old and new
Rust functions are identical. Extraction-to-model equality remains separate. -/
set_option autoImplicit false
namespace AspisV8R17
open RawReducer

theorem lazy_cm31_cross_bounds (a b c d : ℕ)
    (ha : a<P) (hb : b<P) (hc : c<P) (hd : d<P) :
    a+b<2^32 ∧ c+d<2^32 ∧ (a+b)*(c+d)<2^64 := by
  have hl : a+b≤4294967292 := by norm_num [P] at ha hb; omega
  have hr : c+d≤4294967292 := by norm_num [P] at hc hd; omega
  have hp := Nat.mul_le_mul hl hr
  norm_num at hp ⊢
  omega

theorem lazy_cm31_square_bounds (a b : ℕ) (ha : a<P) (hb : b<P) :
    b≤a+P ∧ a+b<2^32 ∧ a+P-b<2^32 ∧ (a+b)*(a+P-b)<2^64 := by
  have hl : a+b≤4294967292 := by norm_num [P] at ha hb; omega
  have hr : a+P-b≤4294967293 := by norm_num [P] at ha hb ⊢; omega
  have hp := Nat.mul_le_mul hl hr
  norm_num [P] at ha hb hp ⊢
  omega

def lazyCM31Cross (a b c d : ℕ) : ℕ := rawReduceU64 ((a+b)*(c+d))
def lazyCM31SquareReal (a b : ℕ) : ℕ := rawReduceU64 ((a+b)*(a+P-b))

theorem lazyCM31Cross_exact (a b c d : ℕ)
    (ha : a<P) (hb : b<P) (hc : c<P) (hd : d<P) :
    lazyCM31Cross a b c d < P ∧
      (lazyCM31Cross a b c d : M31Exact) = ((a : M31Exact)+b)*((c : M31Exact)+d) := by
  have h := (lazy_cm31_cross_bounds a b c d ha hb hc hd).2.2
  refine ⟨rawReduceU64_canonical _ h, ?_⟩
  rw [lazyCM31Cross, rawReduceU64_residue _ h]
  simp only [Nat.cast_mul, Nat.cast_add]

theorem lazyCM31SquareReal_exact (a b : ℕ) (ha : a<P) (hb : b<P) :
    lazyCM31SquareReal a b < P ∧
      (lazyCM31SquareReal a b : M31Exact) = ((a : M31Exact)+b)*((a : M31Exact)-b) := by
  have h := lazy_cm31_square_bounds a b ha hb
  refine ⟨rawReduceU64_canonical _ h.2.2.2, ?_⟩
  rw [lazyCM31SquareReal, rawReduceU64_residue _ h.2.2.2,
    Nat.cast_mul, Nat.cast_add, Nat.cast_sub h.1, Nat.cast_add,
    ZMod.natCast_self, add_zero]

/-- The current cross term equals the former reduce-each-sum implementation
as a canonical WORD, not merely as a congruence class. -/
theorem lazyCM31Cross_eq_old (a b c d : ℕ)
    (ha : a<P) (hb : b<P) (hc : c<P) (hd : d<P) :
    lazyCM31Cross a b c d = rawM31Mul (rawM31Add a b) (rawM31Add c d) := by
  have hnew := lazyCM31Cross_exact a b c d ha hb hc hd
  have hl := rawM31Add_canonical ha hb
  have hr := rawM31Add_canonical hc hd
  have hold := rawM31Mul_canonical hl hr
  have he : (lazyCM31Cross a b c d : M31Exact) =
      (rawM31Mul (rawM31Add a b) (rawM31Add c d) : M31Exact) := by
    rw [hnew.2, rawM31Mul_residue hl hr, residue_rawM31Add ha hb, residue_rawM31Add hc hd]
  rw [ZMod.natCast_eq_natCast_iff] at he
  change lazyCM31Cross a b c d % P = rawM31Mul (rawM31Add a b) (rawM31Add c d) % P at he
  rw [Nat.mod_eq_of_lt hnew.1, Nat.mod_eq_of_lt hold] at he
  exact he

#print axioms lazy_cm31_cross_bounds
#print axioms lazy_cm31_square_bounds
#print axioms lazyCM31Cross_exact
#print axioms lazyCM31SquareReal_exact
#print axioms lazyCM31Cross_eq_old
end AspisV8R17
