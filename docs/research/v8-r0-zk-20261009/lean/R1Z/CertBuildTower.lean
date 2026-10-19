import R1Z.CertBuildBase
import R0P.CoreExt

/-! D57.3: QM31 limbs as `K₄` elements.  `ψ4 B φ x₀ x₁ x₂ x₃ = pack4 B (φ ∘ x)`
(R0P.CoreExt `pack4`: `x₀ + i·x₁ + u·x₂ + i·u·x₃`).  Under the tower premise
`Tower B : i² = -1 ∧ u² = 2 + i` (the QM31 tower CM31[u]/(u² - (2+i)), the one
decoder fact this layer needs), the QM31 product limbs `qmulZ` map to the `K`
product (`psi4_mul`), so the extracted `qadd/qsub/qmul/vget` are `K`
operations on `ψa` (`psi_qadd`, `psi_qsub`, `psi_qmul`, `psi_vget`).  The
generic `acc_loopG`, `horner_loopG` are the builder loop shapes over `K`. -/

set_option autoImplicit false

namespace R1Z.CertBuild
open Aeneas Aeneas.Std Result R1Z.CertCheck R0P
open scoped BigOperators

variable {K : Type} [Field K] {F : Subfield K} (B : PackBasis F) (φ : ZP →+* ↥F)

/-- `ZP → K` through `F`. -/
def embR : ZP →+* K := (Subfield.subtype F).comp φ

/-- Four limbs as a `K₄` element (`pack4`). -/
def ψ4 (x0 x1 x2 x3 : ZP) : K :=
  embR φ x0 + B.i * embR φ x1 + B.u * embR φ x2 + B.i * B.u * embR φ x3

theorem psi4_pack4 (x0 x1 x2 x3 : ZP) :
    ψ4 B φ x0 x1 x2 x3 = pack4 B (fun k => ((φ (![x0, x1, x2, x3] k) : F) : K)) := by
  simp [ψ4, pack4, embR]

/-- An array's `K₄` value. -/
def ψa (x : A4) : K := ψ4 B φ (ga x 0) (ga x 1) (ga x 2) (ga x 3)

/-- The QM31 tower: `i² = -1`, `u² = 2 + i`. -/
def Tower : Prop := B.i * B.i = -1 ∧ B.u * B.u = 2 + B.i

theorem psi4_mul (hT : Tower B) (x0 x1 x2 x3 y0 y1 y2 y3 : ZP) :
    ψ4 B φ (qmulZ x0 x1 x2 x3 y0 y1 y2 y3 0) (qmulZ x0 x1 x2 x3 y0 y1 y2 y3 1)
      (qmulZ x0 x1 x2 x3 y0 y1 y2 y3 2) (qmulZ x0 x1 x2 x3 y0 y1 y2 y3 3) =
      ψ4 B φ x0 x1 x2 x3 * ψ4 B φ y0 y1 y2 y3 := by
  simp only [ψ4, qmulZ, map_add, map_sub, map_mul, map_ofNat]
  set X0 := embR φ x0
  set X1 := embR φ x1
  set X2 := embR φ x2
  set X3 := embR φ x3
  set Y0 := embR φ y0
  set Y1 := embR φ y1
  set Y2 := embR φ y2
  set Y3 := embR φ y3
  linear_combination
    (-(X1 * Y1 + B.u * X1 * Y3 + X2 * Y3 + B.u * X3 * Y1 + X3 * Y2 + 2 * X3 * Y3 + B.i * X3 * Y3)) * hT.1 +
    (-(X2 * Y2 + B.i * X2 * Y3 + B.i * X3 * Y2 + B.i * B.i * X3 * Y3)) * hT.2

theorem psi_qmul (hT : Tower B) {x y z : A4} (h : R1CertBuild.qmul x y = ok z) :
    ψa B φ z = ψa B φ x * ψa B φ y := by
  obtain ⟨-, hq⟩ := qmul_spec h
  have g0 : ga z 0 = _ := hq 0
  have g1 : ga z 1 = _ := hq 1
  have g2 : ga z 2 = _ := hq 2
  have g3 : ga z 3 = _ := hq 3
  unfold ψa
  rw [g0, g1, g2, g3]
  exact psi4_mul B φ hT _ _ _ _ _ _ _ _

theorem psi_qadd {x y z : A4} (h : R1CertBuild.qadd x y = ok z) :
    ψa B φ z = ψa B φ x + ψa B φ y := by
  obtain ⟨-, g0, g1, g2, g3⟩ := qadd_spec h
  simp only [ψa, ψ4, g0, g1, g2, g3, map_add]
  ring

theorem psi_qsub {x y z : A4} (h : R1CertBuild.qsub x y = ok z) :
    ψa B φ z = ψa B φ x - ψa B φ y := by
  obtain ⟨-, g0, g1, g2, g3⟩ := qsub_spec h
  simp only [ψa, ψ4, g0, g1, g2, g3, map_sub]
  ring

/-- The tower basis element `k` (`tower(k)` in probe.rs). -/
def tb (k : ℕ) : K := if k = 0 then 1 else if k = 1 then B.i else if k = 2 then B.u else if k = 3 then B.i * B.u else 0

/-- Coordinate `q` of `unflat e_{4p+k}`. -/
def Vu (p k q : ℕ) : K := if q = p then tb B k else 0

theorem psi_vget {p k q : Usize} {z : A4} (h : R1CertBuild.vget p k q = ok z) :
    ψa B φ z = Vu B p.val k.val q.val := by
  obtain ⟨-, hv⟩ := vget_spec h
  simp only [ψa, ψ4, hv 0 (by norm_num), hv 1 (by norm_num), hv 2 (by norm_num), hv 3 (by norm_num), Vu, tb]
  by_cases hq : q.val = p.val
  · simp only [hq, true_and, if_true]
    by_cases k0 : k.val = 0
    · simp [k0]
    by_cases k1 : k.val = 1
    · simp [k1]
    by_cases k2 : k.val = 2
    · simp [k2]
    by_cases k3 : k.val = 3
    · simp [k3]
    simp [k0, k1, k2, k3]
  · simp [hq]

theorem psi_zero : ψa B φ (Array.repeat 4#usize 0#u32) = 0 := by
  simp [ψa, ψ4, ga, Array.repeat]

/-! ### Loop shapes over `K` -/

theorem acc_loopG {S : Type} (f : S → K) {G : S → Usize → Result S} {n : ℕ} {T : ℕ → K}
    (hstop : ∀ a i, ¬ i.val < n → G a i = ok a)
    (hstep : ∀ a i r, i.val < n → G a i = ok r →
      ∃ a' i', i'.val = i.val + 1 ∧ G a' i' = ok r ∧ f a' = f a + T i.val) :
    ∀ k a i r, i.val + k = n → G a i = ok r → f r = f a + ∑ j ∈ Finset.Ico i.val n, T j
  | 0, a, i, r, hk, h => by
      rw [hstop a i (by omega)] at h
      rw [← ok_inj h, Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty, add_zero]
  | k + 1, a, i, r, hk, h => by
      obtain ⟨a', i', hi', h', ha⟩ := hstep a i r (by omega) h
      rw [acc_loopG f hstop hstep k a' i' r (by omega) h', ha, hi',
        Finset.sum_eq_sum_Ico_succ_bot (show i.val < n by omega), add_assoc]

theorem horner_loopG {S : Type} (f : S → K) (A : K) {G : S → Usize → Result S} {n : ℕ} {T : ℕ → K}
    (hstop : ∀ a i, ¬ i.val < n → G a i = ok a)
    (hstep : ∀ a i r, i.val < n → G a i = ok r →
      ∃ a' i', i'.val = i.val + 1 ∧ G a' i' = ok r ∧ f a' = f a * A + T i.val) :
    ∀ k a i r, i.val + k = n → G a i = ok r →
      f r = f a * A ^ k + ∑ j ∈ Finset.Ico i.val n, T j * A ^ (n - 1 - j)
  | 0, a, i, r, hk, h => by
      rw [hstop a i (by omega)] at h
      rw [← ok_inj h, Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty, add_zero, pow_zero, mul_one]
  | k + 1, a, i, r, hk, h => by
      obtain ⟨a', i', hi', h', ha⟩ := hstep a i r (by omega) h
      rw [horner_loopG f A hstop hstep k a' i' r (by omega) h', ha, hi',
        Finset.sum_eq_sum_Ico_succ_bot (show i.val < n by omega),
        show n - 1 - i.val = k by omega, pow_succ]
      ring

#print axioms psi4_mul
#print axioms psi_qmul
#print axioms psi_qadd
#print axioms psi_qsub
#print axioms psi_vget
#print axioms psi_zero
#print axioms acc_loopG
#print axioms horner_loopG

end R1Z.CertBuild
