import R1Z.CertBuildTower

/-! D57.3: the extracted `final_value` and `corr` (chain-target builder) as `K`
recursions.  `prevR V A` is probe.rs `last_coeff`'s boundary recursion with each
round evaluated as `((H·α + co₁)·α + co₀)` (`roundK`); `final_value` returns
`prevR V A 10` for the unit vector `V = Vu p k` and `α_j = Alimb al j`. -/

set_option autoImplicit false

namespace R1Z.CertBuild
open Aeneas Aeneas.Std Result R1Z.CertCheck R0P
open scoped BigOperators

variable {K : Type} [Field K] {F : Subfield K} (B : PackBasis F) (φ : ZP →+* ↥F)

/-- `∑_{t=1}^{26} V(1+27j+t)`. -/
def Sk (V : ℕ → K) (j : ℕ) : K := ∑ t ∈ Finset.Ico 1 27, V (1 + 27 * j + t)

/-- `∑_{t<26} V(1+27j+26-t)·A^(25-t)` (coefficients 2..27 at A^0..A^25). -/
def Hk (V : ℕ → K) (j : ℕ) (A : K) : K :=
  ∑ t ∈ Finset.Ico 0 26, V (1 + 27 * j + 26 - t) * A ^ (26 - 1 - t)

/-- One round of `last_coeff` evaluated at `A`. -/
def roundK (V : ℕ → K) (j : ℕ) (prev A : K) : K :=
  (Hk V j A * A + (prev - (V (1 + 27 * j) + V (1 + 27 * j)) - Sk V j)) * A + V (1 + 27 * j)

/-- The boundary recursion. -/
def prevR (V : ℕ → K) (A : ℕ → K) : ℕ → K
  | 0 => V 0
  | j + 1 => roundK V j (prevR V A j) (A j)

/-- `α_j` from the alpha limbs `al[4j..4j+4]`. -/
def Alimb (al : Slice U32) (j : ℕ) : K :=
  ψ4 B φ (gs al (4 * j)) (gs al (4 * j + 1)) (gs al (4 * j + 2)) (gs al (4 * j + 3))

theorem idx_z' {v : Slice U32} {i : Usize} {x : U32} (h : Slice.index_usize v i = ok x) :
    (x.val : ZP) = gs v i.val := by
  rw [(index_ok h).2]; rfl

theorem rsum_spec {p k j : Usize} {r : A4} (h : R1CertBuild.rsum p k j = ok r) :
    ψa B φ r = Sk (Vu B p.val k.val) j.val := by
  unfold R1CertBuild.rsum at h
  have e := acc_loopG (ψa B φ) (G := fun a t => R1CertBuild.rsum_loop p k j a t) (n := 27)
    (T := fun t => Vu B p.val k.val (1 + 27 * j.val + t))
    (fun a t ht => by rw [R1CertBuild.rsum_loop, if_neg (by rw [UScalar.lt_equiv]; simpa using ht)])
    (fun a t r ht h => by
      rw [R1CertBuild.rsum_loop, if_pos (by rw [UScalar.lt_equiv]; simpa using ht)] at h
      obtain ⟨i, hi, h⟩ := bind_eq_ok h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
      obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
      obtain ⟨acc1, hacc, h⟩ := bind_eq_ok h
      obtain ⟨t1, ht1, h⟩ := bind_eq_ok h
      refine ⟨acc1, t1, add_ok ht1, h, ?_⟩
      rw [psi_qadd B φ hacc, psi_vget B φ ha1, add_ok hi2, add_ok hi1, mul_ok hi]
      simp)
    26 _ 1#usize r (by simp) h
  rw [e, psi_zero, zero_add, Sk]
  simp

theorem rhorner_spec (hT : Tower B) {p k j : Usize} {a r : A4} (h : R1CertBuild.rhorner p k j a = ok r) :
    ψa B φ r = Hk (Vu B p.val k.val) j.val (ψa B φ a) := by
  unfold R1CertBuild.rhorner at h
  have e := horner_loopG (ψa B φ) (ψa B φ a) (G := fun acc t => R1CertBuild.rhorner_loop p k j a acc t)
    (n := 26) (T := fun t => Vu B p.val k.val (1 + 27 * j.val + 26 - t))
    (fun acc t ht => by rw [R1CertBuild.rhorner_loop, if_neg (by rw [UScalar.lt_equiv]; simpa using ht)])
    (fun acc t r ht h => by
      rw [R1CertBuild.rhorner_loop, if_pos (by rw [UScalar.lt_equiv]; simpa using ht)] at h
      obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
      obtain ⟨i, hi, h⟩ := bind_eq_ok h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
      obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
      obtain ⟨acc1, hacc, h⟩ := bind_eq_ok h
      obtain ⟨t1, ht1, h⟩ := bind_eq_ok h
      refine ⟨acc1, t1, add_ok ht1, h, ?_⟩
      rw [psi_qadd B φ hacc, psi_qmul B φ hT ha1, psi_vget B φ ha2, (sub_ok hi3).1, add_ok hi2,
        add_ok hi1, mul_ok hi]
      simp)
    26 _ 0#usize r (by simp) h
  rw [e, psi_zero, zero_mul, zero_add, Hk]
  simp

theorem round_spec (hT : Tower B) {p k j : Usize} {prev a r : A4}
    (h : R1CertBuild.round p k j prev a = ok r) :
    ψa B φ r = roundK (Vu B p.val k.val) j.val (ψa B φ prev) (ψa B φ a) := by
  unfold R1CertBuild.round at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨co0, hco0, h⟩ := bind_eq_ok h
  obtain ⟨s, hs, h⟩ := bind_eq_ok h
  obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
  obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
  obtain ⟨co1, hco1, h⟩ := bind_eq_ok h
  obtain ⟨hh, hhh, h⟩ := bind_eq_ok h
  obtain ⟨a3, ha3, h⟩ := bind_eq_ok h
  obtain ⟨a4, ha4, h⟩ := bind_eq_ok h
  obtain ⟨a5, ha5, h⟩ := bind_eq_ok h
  have e0 : ψa B φ co0 = Vu B p.val k.val (1 + 27 * j.val) := by
    rw [psi_vget B φ hco0, add_ok hi1, mul_ok hi]; simp
  rw [psi_qadd B φ h, psi_qmul B φ hT ha5, psi_qadd B φ ha4, psi_qmul B φ hT ha3,
    rhorner_spec B φ hT hhh, psi_qsub B φ hco1, psi_qsub B φ ha2, psi_qadd B φ ha1, rsum_spec B φ hs, e0,
    roundK]

theorem fv_loop (hT : Tower B) (p k : Usize) (al : Slice U32) :
    ∀ (m : ℕ) (prev : A4) (j : Usize) (r : A4), j.val + m = 10 →
      ψa B φ prev = prevR (Vu B p.val k.val) (Alimb B φ al) j.val →
      R1CertBuild.final_value_loop p k al prev j = ok r →
      ψa B φ r = prevR (Vu B p.val k.val) (Alimb B φ al) 10
  | 0, prev, j, r, hm, hp, h => by
      rw [R1CertBuild.final_value_loop, if_neg (by rw [UScalar.lt_equiv]; simp; omega)] at h
      rw [← ok_inj h, hp, show j.val = 10 by omega]
  | m + 1, prev, j, r, hm, hp, h => by
      rw [R1CertBuild.final_value_loop, if_pos (by rw [UScalar.lt_equiv]; simp; omega)] at h
      obtain ⟨i, hi, h⟩ := bind_eq_ok h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
      obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
      obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
      obtain ⟨i6, hi6, h⟩ := bind_eq_ok h
      obtain ⟨i7, hi7, h⟩ := bind_eq_ok h
      obtain ⟨prev1, hprev1, h⟩ := bind_eq_ok h
      obtain ⟨j1, hj1, h⟩ := bind_eq_ok h
      have hj1v : j1.val = j.val + 1 := add_ok hj1
      refine fv_loop hT p k al m prev1 j1 r (by omega) ?_ h
      rw [round_spec B φ hT hprev1, hp, hj1v, prevR]
      congr 1
      obtain ⟨g0, g1, g2, g3⟩ := make_ga i1 i3 i5 i7
      have ei : i.val = 4 * j.val := by rw [mul_ok hi]; simp
      rw [ψa, g0, g1, g2, g3, Alimb, idx_z' hi1, idx_z' hi3, idx_z' hi5, idx_z' hi7, add_ok hi2,
        add_ok hi4, add_ok hi6, ei]
      simp

theorem final_value_spec (hT : Tower B) {p k : Usize} {al : Slice U32} {r : A4}
    (h : R1CertBuild.final_value p k al = ok r) :
    ψa B φ r = prevR (Vu B p.val k.val) (Alimb B φ al) 10 := by
  unfold R1CertBuild.final_value at h
  obtain ⟨prev, hprev, h⟩ := bind_eq_ok h
  refine fv_loop B φ hT p k al 10 prev 0#usize r (by simp) ?_ h
  rw [psi_vget B φ hprev]
  simp [prevR]

/-- The hinv limbs as a `K₄` element. -/
def Hlimb (hinv : Slice U32) : K := ψ4 B φ (gs hinv 0) (gs hinv 1) (gs hinv 2) (gs hinv 3)

theorem corr_spec (hT : Tower B) {i : Usize} {al hinv : Slice U32} {c : A4}
    (h : R1CertBuild.corr i al hinv = ok c) :
    ψa B φ c = prevR (Vu B (i.val / 4) (i.val % 4)) (Alimb B φ al) 10 * Hlimb B φ hinv *
      embR φ 1073741824 := by
  unfold R1CertBuild.corr at h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
  obtain ⟨i6, hi6, h⟩ := bind_eq_ok h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
  have e5 : i5.val = i.val / 4 := by rw [div_ok (by simp) hi5]; simp
  have e6 : i6.val = i.val % 4 := by rw [rem_ok (by simp) hi6]; simp
  rw [psi_qmul B φ hT h, psi_qmul B φ hT ha1, final_value_spec B φ hT ha, e5, e6]
  obtain ⟨g0, g1, g2, g3⟩ := make_ga i1 i2 i3 i4
  obtain ⟨h0, h1, h2, h3⟩ := make_ga (1073741824#u32) 0#u32 0#u32 0#u32
  congr 1
  · congr 1
    rw [ψa, g0, g1, g2, g3, Hlimb, idx_z' hi1, idx_z' hi2, idx_z' hi3, idx_z' hi4]
    simp
  · rw [ψa, h0, h1, h2, h3, ψ4]
    simp

#print axioms rsum_spec
#print axioms rhorner_spec
#print axioms round_spec
#print axioms final_value_spec
#print axioms corr_spec

end R1Z.CertBuild
