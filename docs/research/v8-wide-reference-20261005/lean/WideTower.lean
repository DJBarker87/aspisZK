import AspisFormal.V5ComponentCQM31TowerExact

/-!
The wide challenge field for the R0 reference design: one more quadratic layer
on the deployed tower, `v^2 = u` where `u^2 = 2 + i`.  Same construction
pattern as `CM31Exact` and `QM31Exact`; the non-square proofs are by norms.
Nothing here concerns a protocol, a sampler or an encoder.
-/
set_option autoImplicit false
namespace AspisWideTower
open AspisV5ComponentCQM31TowerExact

/-- The generator `u` of QM31 over CM31. -/
def wideU : QM31Exact := ⟨0, 1⟩

@[simp] theorem wideU_re : wideU.re = 0 := rfl
@[simp] theorem wideU_im : wideU.im = 1 := rfl

theorem qm31_norm_wideU : QuadraticAlgebra.norm wideU = -qm31R := by
  simp [wideU, QuadraticAlgebra.norm_def]

/-- The generator `i` of CM31 over M31. -/
def cm31I : CM31Exact := ⟨0, 1⟩

theorem cm31I_mul_self : cm31I * cm31I = -1 := by
  ext
  · simp [cm31I]; rfl
  · simp [cm31I]; rfl

/-- `-(2+i)` is a non-square in CM31, because `-1 = i^2` is a square and
`2+i` is not. -/
theorem cm31_neg_qm31R_not_isSquare : ¬ IsSquare (-qm31R) := by
  rintro ⟨z, hz⟩
  apply cm31_qm31R_not_isSquare
  refine ⟨cm31I * z, ?_⟩
  calc
    qm31R = -(-qm31R) := (neg_neg _).symm
    _ = -(z * z) := by rw [hz]
    _ = (cm31I * cm31I) * (z * z) := by rw [cm31I_mul_self]; ring
    _ = cm31I * z * (cm31I * z) := by ring

/-- `u` is a non-square in QM31: the norm of a square is a square, while
`Norm(u) = -(2+i)` is a non-square in CM31. -/
theorem qm31_wideU_not_isSquare : ¬ IsSquare wideU := by
  rintro ⟨z, hz⟩
  apply cm31_neg_qm31R_not_isSquare
  refine ⟨QuadraticAlgebra.norm z, ?_⟩
  calc
    -qm31R = QuadraticAlgebra.norm wideU := qm31_norm_wideU.symm
    _ = QuadraticAlgebra.norm (z * z) := congrArg QuadraticAlgebra.norm hz
    _ = QuadraticAlgebra.norm z * QuadraticAlgebra.norm z :=
      QuadraticAlgebra.norm.map_mul z z

instance wideRootless : Fact
    (∀ z : QM31Exact, z ^ 2 ≠ wideU + 0 * z) := ⟨by
  intro z hz
  apply qm31_wideU_not_isSquare
  refine ⟨z, ?_⟩
  simpa [pow_two] using hz.symm
⟩

/-- The wide challenge field, of degree 8 over M31: `v^2 = u`. -/
abbrev WideExact := QuadraticAlgebra QM31Exact wideU 0

/-- It is a field. -/
noncomputable example : Field WideExact := inferInstance

noncomputable instance wideExactFintype : Fintype WideExact :=
  Fintype.ofEquiv (QM31Exact × QM31Exact) (QuadraticAlgebra.equivProd wideU 0).symm

theorem wideExact_card : Fintype.card WideExact = P ^ 8 := by
  calc
    Fintype.card WideExact = Fintype.card (QM31Exact × QM31Exact) :=
      Fintype.card_congr (QuadraticAlgebra.equivProd wideU 0)
    _ = P ^ 4 * P ^ 4 := by rw [Fintype.card_prod, qm31Exact_card]
    _ = P ^ 8 := by rw [← pow_add]

/-- Every positive natural below the M31 characteristic is nonzero in the wide
field. -/
theorem wideExact_natCast_ne_zero_of_pos_of_lt_characteristic
    (degree : Nat) (degreePositive : 0 < degree) (degreeSmall : degree < P) :
    (degree : WideExact) ≠ 0 := by
  have baseNonzero : (degree : M31Exact) ≠ 0 := by
    intro castZero
    have divides := (CharP.cast_eq_zero_iff M31Exact P degree).mp castZero
    exact (Nat.not_dvd_of_pos_of_lt degreePositive degreeSmall) divides
  intro towerZero
  apply baseNonzero
  apply FaithfulSMul.algebraMap_injective M31Exact WideExact
  calc
    algebraMap M31Exact WideExact (degree : M31Exact) =
        (degree : WideExact) := map_natCast _ degree
    _ = 0 := towerZero
    _ = algebraMap M31Exact WideExact (0 : M31Exact) := (map_zero _).symm

theorem wideExact_two_ne_zero : (2 : WideExact) ≠ 0 := by
  have h := wideExact_natCast_ne_zero_of_pos_of_lt_characteristic 2 (by norm_num)
    (by norm_num [P])
  simpa using h

/-- QM31 embeds in the wide field. -/
theorem qm31_to_wide_injective :
    Function.Injective (algebraMap QM31Exact WideExact) :=
  FaithfulSMul.algebraMap_injective QM31Exact WideExact

#print axioms qm31_wideU_not_isSquare
#print axioms wideExact_card
#print axioms wideExact_natCast_ne_zero_of_pos_of_lt_characteristic
#print axioms wideExact_two_ne_zero
#print axioms qm31_to_wide_injective
end AspisWideTower
