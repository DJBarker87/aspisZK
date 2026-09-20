import AspisV8R16.FibreInterpolation
import AspisV8R16.FinalConsistency

/-! Universal compatible-image construction for raw quotient values and
the folded polynomial. This does NOT impose the H1 active-row restrictions
or G semantic/point/relation observations. -/
set_option autoImplicit false
namespace AspisV8R17
open Polynomial AspisV8R16
variable {F : Type*} [Field F]

private theorem const_mul_degree_lt (k : F) (p : Polynomial F) (m : ℕ)
    (hp : p.degree < m) : (C k * p).degree < m := by
  by_cases hk : k = 0
  · simp [hk]
  · rw [degree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hk)]
    exact hp

private theorem sub_degree_lt (p q : Polynomial F) (m : ℕ)
    (hp : p.degree < m) (hq : q.degree < m) : (p-q).degree < m :=
  lt_of_le_of_lt (degree_sub_le p q) (max_lt hp hq)

/-- Every raw target compatible with a prescribed final polynomial has a
quotient construction for any distinct fibre roots. No generic-rank or
nonexceptional-alpha premise is used. The three nonconstant channels have
degree < n, leaving high quotient image coordinates zero when n < m. -/
theorem compatible_raw_final_coverage {n m : ℕ}
    (t x y v0 v1 v2 v3 : Fin n → F) (alpha : F) (final : Polynomial F)
    (hinj : Function.Injective t) (hnm : n ≤ m)
    (hf : final.degree < m) (h2 : (2 : F) ≠ 0) (h4 : (4 : F) ≠ 0)
    (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (compatible : ∀ i, foldFour (x i) (y i) alpha
      (v0 i) (v1 i) (v2 i) (v3 i) = final.eval (t i)) :
    ∃ a b c d : Polynomial F,
      a.degree < m ∧ b.degree < n ∧ c.degree < n ∧ d.degree < n ∧
      a + C alpha*b + C (alpha^2)*c + C (alpha^3)*d = final ∧
      ∀ i,
        a.eval (t i)+b.eval (t i)*y i+c.eval (t i)*x i+d.eval (t i)*x i*y i=v0 i ∧
        a.eval (t i)-b.eval (t i)*y i+c.eval (t i)*x i-d.eval (t i)*x i*y i=v1 i ∧
        a.eval (t i)-b.eval (t i)*y i-c.eval (t i)*x i+d.eval (t i)*x i*y i=v2 i ∧
        a.eval (t i)+b.eval (t i)*y i-c.eval (t i)*x i-d.eval (t i)*x i*y i=v3 i := by
  obtain ⟨b,hb,eb⟩ := bounded_interpolate t
    (fun i => splitB (y i) (v0 i) (v1 i) (v2 i) (v3 i)) hinj
  obtain ⟨c,hc,ec⟩ := bounded_interpolate t
    (fun i => splitC (x i) (v0 i) (v1 i) (v2 i) (v3 i)) hinj
  obtain ⟨d,hd,ed⟩ := bounded_interpolate t
    (fun i => splitD (x i) (y i) (v0 i) (v1 i) (v2 i) (v3 i)) hinj
  let a := final - C alpha*b - C (alpha^2)*c - C (alpha^3)*d
  have hnm' : (n : WithBot ℕ) ≤ (m : WithBot ℕ) := WithBot.coe_le_coe.mpr hnm
  have ha : a.degree < m := by
    apply sub_degree_lt
    · apply sub_degree_lt
      · exact sub_degree_lt _ _ m hf
          (const_mul_degree_lt alpha b m (lt_of_lt_of_le hb hnm'))
      · exact const_mul_degree_lt (alpha^2) c m (lt_of_lt_of_le hc hnm')
    · exact const_mul_degree_lt (alpha^3) d m (lt_of_lt_of_le hd hnm')
  refine ⟨a,b,c,d,ha,hb,hc,hd,?_,?_⟩
  · dsimp [a]
    ring
  · intro i
    obtain ⟨h0,h1,h2v,h3⟩ := four_slot_inverse (x i) (y i)
      (v0 i) (v1 i) (v2 i) (v3 i) h4 (hx i) (hy i)
    have hfold := fold_channels (x i) (y i) alpha
      (splitA (v0 i) (v1 i) (v2 i) (v3 i))
      (splitB (y i) (v0 i) (v1 i) (v2 i) (v3 i))
      (splitC (x i) (v0 i) (v1 i) (v2 i) (v3 i))
      (splitD (x i) (y i) (v0 i) (v1 i) (v2 i) (v3 i)) h2 (hx i) (hy i)
    rw [h0,h1,h2v,h3,compatible i] at hfold
    have ea : a.eval (t i) = splitA (v0 i) (v1 i) (v2 i) (v3 i) := by
      simp only [a, eval_sub, eval_mul, eval_C, eb, ec, ed]
      rw [hfold]
      ring
    rw [ea,eb,ec,ed]
    exact ⟨h0,h1,h2v,h3⟩

#print axioms compatible_raw_final_coverage
end AspisV8R17
