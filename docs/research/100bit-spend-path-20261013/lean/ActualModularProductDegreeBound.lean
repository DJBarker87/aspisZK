import CompPolyModularRemainderDegree
import CompPoly.Univariate.Raw.Modular
import CompPoly.Univariate.EuclideanAlgorithm

namespace ActualModularProductDegreeBound
open CompPoly Polynomial
variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

private theorem raw_monicNormalize_nonzero {p : CPolynomial.Raw F}
    (hp : p.trim ≠ (0 : CPolynomial.Raw F)) :
    CPolynomial.Raw.monicNormalize p ≠ 0 := by
  unfold CPolynomial.Raw.monicNormalize
  by_cases hz : p.trim == (0 : CPolynomial.Raw F)
  · have heq : p.trim = 0 := by simpa using hz
    exact (hp heq).elim
  · rw [if_neg hz]
    intro h
    have hsize_smul :
        (CPolynomial.Raw.smul (p.trim.leadingCoeff)⁻¹ p.trim).size = p.trim.size := by
      simp [CPolynomial.Raw.smul]
    change CPolynomial.Raw.smul (p.trim.leadingCoeff)⁻¹ p.trim = 0 at h
    rw [h] at hsize_smul
    have : p.trim.size = 0 := by simpa using hsize_smul.symm
    have heq : p.trim = (0 : CPolynomial.Raw F) := Array.eq_empty_of_size_eq_zero this
    exact hp heq

private theorem raw_monicNormalize_trim (p : CPolynomial.Raw F) :
    (CPolynomial.Raw.monicNormalize p).trim = CPolynomial.Raw.monicNormalize p := by
  unfold CPolynomial.Raw.monicNormalize
  let q := p.trim
  by_cases hz : q == (0 : CPolynomial.Raw F)
  · have hq : q = 0 := by simpa using hz
    have hp : p.trim = (#[] : CPolynomial.Raw F) := by simpa [q] using hq
    simp [hp, CPolynomial.Raw.Trim.canonical_empty]
  · have hq : q ≠ (0 : CPolynomial.Raw F) := by
      intro h
      exact hz (by simp [h])
    have hp : ¬p.trim = (#[] : CPolynomial.Raw F) := by
      intro h
      exact hq (by simpa [q] using h)
    simp [hp]
    change (CPolynomial.Raw.mk (Array.map (fun r ↦ q.leadingCoeff⁻¹ * r) p.trim)).trim =
      CPolynomial.Raw.mk (Array.map (fun r ↦ q.leadingCoeff⁻¹ * r) p.trim)
    apply CPolynomial.Raw.Trim.non_zero_map (fun r ↦ q.leadingCoeff⁻¹ * r)
    · intro r hr
      rcases mul_eq_zero.mp hr with hi | hr0
      · have hlead : q.leadingCoeff = 0 := inv_eq_zero.mp hi
        have hcanon : q.trim = q := by simpa [q] using CPolynomial.Raw.Trim.trim_twice p
        have hcrit := (CPolynomial.Raw.Trim.trim_eq_iff_size_eq_zero_or_getLastD_ne_zero
          (p := q)).mp hcanon
        rcases hcrit with he | hl
        · have hempty : q = (#[] : CPolynomial.Raw F) := Array.eq_empty_of_size_eq_zero he
          exact False.elim (hq hempty)
        · unfold CPolynomial.Raw.leadingCoeff at hlead
          rw [hcanon] at hlead
          exact (hl hlead).elim
      · exact hr0
    · simpa [q] using CPolynomial.Raw.Trim.trim_twice p

private theorem raw_monicNormalize_toPoly_eq_normalize (p : CPolynomial.Raw F) :
    (CPolynomial.ofArray (CPolynomial.Raw.monicNormalize p)).toPoly =
      normalize (CPolynomial.ofArray p).toPoly := by
  have h := CPolynomial.monicNormalize_toPoly_eq_normalize (CPolynomial.ofArray p)
  unfold CPolynomial.monicNormalize at h
  unfold CPolynomial.ofArray at h
  rw [show CPolynomial.Raw.monicNormalize p.trim = CPolynomial.Raw.monicNormalize p from by
    unfold CPolynomial.Raw.monicNormalize
    rw [CPolynomial.Raw.Trim.trim_twice]] at h
  exact h

private theorem raw_monicNormalize_poly_monic {p : CPolynomial.Raw F}
    (hp : p.trim ≠ (0 : CPolynomial.Raw F)) :
    (CPolynomial.ofArray (CPolynomial.Raw.monicNormalize p)).toPoly.Monic := by
  rw [raw_monicNormalize_toPoly_eq_normalize]
  have hpC : CPolynomial.ofArray p ≠ 0 := by
    intro h
    have hv := congrArg Subtype.val h
    unfold CPolynomial.ofArray at hv
    exact hp hv
  have hpPoly : (CPolynomial.ofArray p).toPoly ≠ 0 :=
    (CPolynomial.toPoly_eq_zero_iff (CPolynomial.ofArray p)).not.mpr hpC
  exact Polynomial.monic_normalize hpPoly

/-- One selected `mulModWith` call returns a canonical remainder no longer than the
actual normalized modulus. This is the degree-bound invariant used by repeated squaring. -/
theorem mulModWith_size_le_normalized_modulus
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (modulus p q : CPolynomial.Raw F)
    (hmod : modulus.trim ≠ (0 : CPolynomial.Raw F)) :
    (CPolynomial.Raw.mulModWith M D modulus p q).size ≤
      (CPolynomial.Raw.monicNormalize modulus).size := by
  have hzero : ¬modulus.trim == (0 : CPolynomial.Raw F) := by
    intro h
    exact hmod (LawfulBEq.eq_of_beq h)
  have hnormTrim : (CPolynomial.Raw.monicNormalize modulus).trim =
      CPolynomial.Raw.monicNormalize modulus := raw_monicNormalize_trim modulus
  have hnorm0 : CPolynomial.Raw.monicNormalize modulus ≠ 0 :=
    raw_monicNormalize_nonzero hmod
  have hnormMonic : (CPolynomial.ofArray (CPolynomial.Raw.monicNormalize modulus)).monic = true := by
    apply (CPolynomial.monic_toPoly_iff _).mpr
    exact raw_monicNormalize_poly_monic hmod
  have hproductTrim : (M.mul p q).trim = M.mul p q := by
    rw [M.mul_eq_mul]
    exact CPolynomial.Raw.mul_is_trimmed p q
  unfold CPolynomial.Raw.mulModWith
  rw [if_neg hzero]
  rw [D.modByMonic_eq_modByMonic (M.mul p q)
    (CPolynomial.Raw.monicNormalize modulus) hproductTrim hnormTrim]
  exact CompPolyModularRemainderDegree.raw_modByMonic_size_le
    (M.mul p q) (CPolynomial.Raw.monicNormalize modulus)
    hproductTrim hnormTrim hnorm0 hnormMonic


/-- Trimming and coefficient normalization do not change modulus length. -/
theorem monicNormalize_size_eq_trim (modulus : CPolynomial.Raw F)
    (hmod : modulus.trim ≠ (0 : CPolynomial.Raw F)) :
    (CPolynomial.Raw.monicNormalize modulus).size = modulus.trim.size := by
  unfold CPolynomial.Raw.monicNormalize
  have hz : ¬modulus.trim == (0 : CPolynomial.Raw F) := by
    intro h
    exact hmod (LawfulBEq.eq_of_beq h)
  rw [if_neg hz]
  change (Array.map (fun r => modulus.trim.leadingCoeff⁻¹ * r) modulus.trim).size =
    modulus.trim.size
  exact Array.size_map

/-- The actual modular-product output is bounded by the trimmed input modulus size. -/
theorem mulModWith_size_le_trim_modulus
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (modulus p q : CPolynomial.Raw F)
    (hmod : modulus.trim ≠ (0 : CPolynomial.Raw F)) :
    (CPolynomial.Raw.mulModWith M D modulus p q).size ≤ modulus.trim.size := by
  rw [← monicNormalize_size_eq_trim modulus hmod]
  exact mulModWith_size_le_normalized_modulus M D modulus p q hmod

/-- Every accumulator state produced by the real binary modular-exponentiation
recursion stays no longer than the trimmed modulus. The current/base operand may
be arbitrary: each recursive step reduces its square before the next call. -/
theorem powModBinaryAuxWith_size_le (M : CPolynomial.Raw.MulContext F)
    (D : CPolynomial.Raw.ModContext F) (modulus : CPolynomial.Raw F)
    (exponent : Nat) (acc current : CPolynomial.Raw F)
    (hmod : modulus.trim ≠ (0 : CPolynomial.Raw F))
    (hacc : acc.size ≤ (CPolynomial.Raw.monicNormalize modulus).size) :
    (CPolynomial.Raw.powModBinaryAuxWith M D modulus exponent acc current).size ≤
      (CPolynomial.Raw.monicNormalize modulus).size := by
  induction exponent using Nat.strong_induction_on generalizing acc current with
  | h n ih =>
      cases n with
      | zero => simpa [CPolynomial.Raw.powModBinaryAuxWith]
      | succ k =>
          let acc' := if (k + 1) % 2 == 1 then
            CPolynomial.Raw.mulModWith M D modulus acc current else acc
          let current' := CPolynomial.Raw.mulModWith M D modulus current current
          have hrec : (k + 1) / 2 < k + 1 :=
            Nat.div_lt_self (Nat.succ_pos k) (by decide)
          have hacc' : acc'.size ≤ (CPolynomial.Raw.monicNormalize modulus).size := by
            by_cases hodd : (k + 1) % 2 == 1
            · simpa [acc', hodd] using
                mulModWith_size_le_normalized_modulus M D modulus acc current hmod
            · simpa [acc', hodd] using hacc
          have hcurrent' : current'.size ≤ (CPolynomial.Raw.monicNormalize modulus).size := by
            exact mulModWith_size_le_normalized_modulus M D modulus current current hmod
          rw [CPolynomial.Raw.powModBinaryAuxWith]
          change (CPolynomial.Raw.powModBinaryAuxWith M D modulus ((k + 1) / 2)
            acc' current').size ≤ (CPolynomial.Raw.monicNormalize modulus).size
          exact ih ((k + 1) / 2) hrec acc' current' hacc'

/-- The pinned public `powModWith` implementation preserves the same modulus-size
bound for every exponent, including its initial `D.modByMonic 1` reduction. -/
theorem powModWith_size_le (M : CPolynomial.Raw.MulContext F)
    (D : CPolynomial.Raw.ModContext F) (modulus base : CPolynomial.Raw F)
    (exponent : Nat) (hmod : modulus.trim ≠ (0 : CPolynomial.Raw F)) :
    (CPolynomial.Raw.powModWith M D modulus base exponent).size ≤
      (CPolynomial.Raw.monicNormalize modulus).size := by
  have hz : ¬modulus.trim == (0 : CPolynomial.Raw F) := by
    intro h
    exact hmod (LawfulBEq.eq_of_beq h)
  have hnormTrim : (CPolynomial.Raw.monicNormalize modulus).trim =
      CPolynomial.Raw.monicNormalize modulus := raw_monicNormalize_trim modulus
  have hnorm0 : CPolynomial.Raw.monicNormalize modulus ≠ 0 :=
    raw_monicNormalize_nonzero hmod
  have hnormMonic : (CPolynomial.ofArray (CPolynomial.Raw.monicNormalize modulus)).monic = true := by
    apply (CPolynomial.monic_toPoly_iff _).mpr
    exact raw_monicNormalize_poly_monic hmod
  have hOneTrim : (1 : CPolynomial.Raw F).trim = 1 := by
    change CPolynomial.Raw.trim ((#[] : Array F).push (1 : F)) =
      (#[] : Array F).push (1 : F)
    exact CPolynomial.Raw.Trim.push_trim #[] 1 one_ne_zero
  have hOneBound : (D.modByMonic (1 : CPolynomial.Raw F)
      (CPolynomial.Raw.monicNormalize modulus)).size ≤
      (CPolynomial.Raw.monicNormalize modulus).size := by
    rw [D.modByMonic_eq_modByMonic _ _ hOneTrim hnormTrim]
    exact CompPolyModularRemainderDegree.raw_modByMonic_size_le
      (1 : CPolynomial.Raw F) (CPolynomial.Raw.monicNormalize modulus)
      hOneTrim hnormTrim hnorm0 hnormMonic
  unfold CPolynomial.Raw.powModWith
  rw [if_neg hz]
  apply powModBinaryAuxWith_size_le M D modulus exponent _ base hmod
  exact hOneBound

#print axioms mulModWith_size_le_trim_modulus
#print axioms powModBinaryAuxWith_size_le
#print axioms powModWith_size_le

#print axioms mulModWith_size_le_normalized_modulus
end ActualModularProductDegreeBound
