import AspisR1BatchedFoldArithmetic

/-! Source-shaped bounds for the private fast_pairing Q::raw/mul formulas.
These are arithmetic lemmas, not an extraction of the private representation.
Products are abstracted with the cap supplied by product_bound. -/
set_option autoImplicit false
namespace AspisR1.R22FastPairingRawRanges
open AspisR1BatchedFoldArithmetic

/-- Both partial folds in Q::raw/mul are at most 3P. -/
theorem partial_le_three_p (x : Nat) (hx : x ≤ 2 * (2^31-1)^2) :
    fold x ≤ 3 * (2^31-1) := by
  have hm := Nat.mod_lt x (show 0 < limbBase by decide)
  unfold fold
  norm_num [limbBase] at hm ⊢
  norm_num at hx
  omega

/-- All sequential wrapping additions and subtractions in the four raw
coordinates fit U64 under the canonical product cap. The inequalities include
the pre-subtraction intermediates, so Nat's saturating subtraction does not
hide an underflow. Plain coefficient multiples also fit U64. -/
theorem raw_ranges
    (ae bf cg dh ch dg af be ag ce bh df ah bg cf de : Nat)
    (hproducts : ∀ x ∈ [ae,bf,cg,dh,ch,dg,af,be,ag,ce,bh,df,ah,bg,cf,de],
      x ≤ (2^31-2)^2) :
    let pp := (2^31-1)^2
    let u := fold (cg + pp - dh)
    let v := fold (ch + dg)
    cg + pp < 2^64 ∧ dh ≤ cg + pp ∧ ch + dg < 2^64 ∧
    ae + pp < 2^64 ∧ bf ≤ ae + pp ∧
    ae + pp - bf + 2*u < 2^64 ∧
    ae + pp - bf + 2*u + 3*(2^31-1) < 2^64 ∧
    v ≤ ae + pp - bf + 2*u + 3*(2^31-1) ∧
    af + be < 2^64 ∧ af + be + u < 2^64 ∧ af + be + u + 2*v < 2^64 ∧
    ag + ce < 2^64 ∧ ag + ce + 2*pp < 2^64 ∧
    bh ≤ ag + ce + 2*pp ∧ df ≤ ag + ce + 2*pp - bh ∧
    ah + bg < 2^64 ∧ ah + bg + cf < 2^64 ∧ ah + bg + cf + de < 2^64 ∧
    2*u < 2^64 ∧ 2*v < 2^64 := by
  have hae := hproducts ae (by simp)
  have hbf := hproducts bf (by simp)
  have hcg := hproducts cg (by simp)
  have hdh := hproducts dh (by simp)
  have hch := hproducts ch (by simp)
  have hdg := hproducts dg (by simp)
  have haf := hproducts af (by simp)
  have hbe := hproducts be (by simp)
  have hag := hproducts ag (by simp)
  have hce := hproducts ce (by simp)
  have hbh := hproducts bh (by simp)
  have hdf := hproducts df (by simp)
  have hah := hproducts ah (by simp)
  have hbg := hproducts bg (by simp)
  have hcf := hproducts cf (by simp)
  have hde := hproducts de (by simp)
  have hu := partial_le_three_p (cg + (2^31-1)^2 - dh) (by omega)
  have hv := partial_le_three_p (ch + dg) (by omega)
  dsimp only
  omega

#print axioms partial_le_three_p
#print axioms raw_ranges
end AspisR1.R22FastPairingRawRanges
