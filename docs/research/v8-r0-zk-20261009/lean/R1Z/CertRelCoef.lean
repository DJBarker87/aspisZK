import R1Z.CertRelWeights

/-! D64 hRel (3a): the extracted relation coefficient (builder 4 `pfold`, `lfv`,
`line_fold`, `coef`) is the CertRelK model `coefP` of the builder inputs: openings
`Wl op 2`, `Wl op 3`, the M31 quarter and half, the second dual fold `w2K`, the folded
positions `gN fpos`, the line inverses `li[3ρ + s]` and the stored log-16 node
`x16[ρ]` of relation `ρ`, its kind `rk[ρ]` and query `ru[ρ]`.  Aeneas side only. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertBuild
open Aeneas Aeneas.Std Result R1Z.CertCheck R0P R1Z.CertRel
open scoped BigOperators

variable {K : Type} [Field K] {F : Subfield K} (B : PackBasis F) (φ : ZP →+* ↥F) (w : K)

theorem ueq32 {x : U32} {n : ℕ} {lit : U32} (hl : lit.val = n) : x = lit ↔ x.val = n := by
  rw [UScalar.eq_equiv, hl]

theorem u11 : (11#usize : Usize).val = 11 := by simp
theorem u14 : (14#usize : Usize).val = 14 := by simp

theorem psi_pfold {c inv l r z : A8} (hT : Tower B) (hW : w * w = B.u) (h : R1CertBuild.pfold c inv l r = ok z) :
    ψ8 B φ w z = pfP (embR φ 1073741824) (ψ8 B φ w c) (ψ8 B φ w inv) (ψ8 B φ w l) (ψ8 B φ w r) := by
  unfold R1CertBuild.pfold at h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
  obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
  obtain ⟨a3, ha3, h⟩ := bind_eq_ok h
  obtain ⟨a4, ha4, h⟩ := bind_eq_ok h
  obtain ⟨a5, ha5, h⟩ := bind_eq_ok h
  have hh : ψ8 B φ w a1 = embR φ 1073741824 := by rw [psi_wbase B φ w ha1]; simp
  rw [psi_wadd B φ w h, psi_wmul B φ w hT hW ha2, psi_wmul B φ w hT hW ha5, psi_wmul B φ w hT hW ha4,
    psi_wadd B φ w ha, psi_wsub B φ w ha3, hh, pfP]

theorem flag_iff {p q : Prop} [Decidable p] [Decidable q] (hc : p ↔ q) :
    (if decide p = true then (1 : ZP) else 0) = if q then 1 else 0 := by
  by_cases e : q
  · rw [if_pos (decide_eq_true (hc.2 e)), if_pos e]
  · rw [if_neg (fun h' => e (hc.1 (of_decide_eq_true h'))), if_neg e]

theorem flag_or {x : Usize} :
    (if (decide (x = 7#usize) || decide (x = 11#usize)) = true then (1 : ZP) else 0) =
      if x.val = 7 ∨ x.val = 11 then 1 else 0 := by
  have hc : ((decide (x = 7#usize) || decide (x = 11#usize)) = true) ↔ (x.val = 7 ∨ x.val = 11) := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    rw [ueq u7', ueq u11]
  by_cases e : x.val = 7 ∨ x.val = 11
  · rw [if_pos (hc.2 e), if_pos e]
  · rw [if_neg (fun h' => e (hc.1 h')), if_neg e]

theorem embR_ite (q : Prop) [Decidable q] : embR (K := K) φ (if q then 1 else 0) = if q then 1 else 0 := by
  split_ifs <;> simp

theorem wbase_flag {t lit : Usize} {n : ℕ} (hl : lit.val = n) {i : U32} {z : A8}
    (hi : lift (UScalar.cast_fromBool .U32 (decide (t = lit))) = ok i) (h : R1CertBuild.wbase i = ok z) :
    ψ8 B φ w z = if t.val = n then 1 else 0 := by
  rw [psi_wbase B φ w h, fromBool_zp _ hi, flag_iff (ueq (x := t) hl), embR_ite]

theorem psi_lfv (hT : Tower B) (hW : w * w = B.u) {a i0 i1 i2 z : A8} {t : Usize}
    (h : R1CertBuild.lfv a i0 i1 i2 t = ok z) :
    ψ8 B φ w z = lfvP (embR φ 1073741824) (ψ8 B φ w a) (ψ8 B φ w i0) (ψ8 B φ w i1) (ψ8 B φ w i2) t.val := by
  unfold R1CertBuild.lfv at h
  obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
  obtain ⟨j, hj, h⟩ := bind_eq_ok h
  obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
  obtain ⟨j3, hj3, h⟩ := bind_eq_ok h
  obtain ⟨a3, ha3, h⟩ := bind_eq_ok h
  obtain ⟨a4, ha4, h⟩ := bind_eq_ok h
  obtain ⟨j4, hj4, h⟩ := bind_eq_ok h
  obtain ⟨a5, ha5, h⟩ := bind_eq_ok h
  obtain ⟨j5, hj5, h⟩ := bind_eq_ok h
  obtain ⟨a6, ha6, h⟩ := bind_eq_ok h
  obtain ⟨a7, ha7, h⟩ := bind_eq_ok h
  rw [psi_pfold B φ w hT hW h, psi_wmul B φ w hT hW ha1, psi_pfold B φ w hT hW ha4, psi_pfold B φ w hT hW ha7,
    wbase_flag B φ w u0' hj ha2, wbase_flag B φ w u1' hj3 ha3, wbase_flag B φ w u2' hj4 ha5,
    wbase_flag B φ w u3' hj5 ha6, lfvP]

theorem psi_line_fold (hT : Tower B) (hW : w * w = B.u) {op ru li : Slice U32} {rho p : Usize} {z : A8}
    (h : R1CertBuild.line_fold op ru li rho p = ok z) :
    ψ8 B φ w z = (if p.val / 4 = gN ru rho.val / 4 then 1 else 0) *
      lfvP (embR φ 1073741824) (Wl B φ w op 3) (embR φ (gs li (3 * rho.val))) (embR φ (gs li (3 * rho.val + 1)))
        (embR φ (gs li (3 * rho.val + 2))) (p.val % 4) := by
  unfold R1CertBuild.line_fold at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨v, hv, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
  obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
  obtain ⟨i6, hi6, h⟩ := bind_eq_ok h
  obtain ⟨i7, hi7, h⟩ := bind_eq_ok h
  obtain ⟨a3, ha3, h⟩ := bind_eq_ok h
  obtain ⟨i8, hi8, h⟩ := bind_eq_ok h
  obtain ⟨i9, hi9, h⟩ := bind_eq_ok h
  obtain ⟨a4, ha4, h⟩ := bind_eq_ok h
  obtain ⟨i10, hi10, h⟩ := bind_eq_ok h
  obtain ⟨a5, ha5, h⟩ := bind_eq_ok h
  have e1 : i1.val = gN ru rho.val := by rw [(ok_inj hi1).symm, castUs, (index_ok hi).2]; rfl
  have ev : v.val = gN ru rho.val / 4 := by rw [div_ok (by simp) hv, e1]; simp
  have e2 : i2.val = p.val / 4 := by rw [div_ok (by simp) hi2]; simp
  have e4 : i4.val = 3 * rho.val := by rw [mul_ok hi4]; simp
  have e10 : i10.val = p.val % 4 := by rw [rem_ok (by simp) hi10]; simp
  have hc : (i2 = v) ↔ (p.val / 4 = gN ru rho.val / 4) := by rw [UScalar.eq_equiv, e2, ev]
  have hf : ψ8 B φ w a = if p.val / 4 = gN ru rho.val / 4 then 1 else 0 := by
    rw [psi_wbase B φ w ha, fromBool_zp _ hi3, flag_iff hc, embR_ite]
  rw [psi_wmul B φ w hT hW h, hf, psi_lfv B φ w hT hW ha5, psi_wget B φ w ha1, psi_wbase B φ w ha2,
    psi_wbase B φ w ha3, psi_wbase B φ w ha4, idx_z' hi5, idx_z' hi7, idx_z' hi9, add_ok hi6, add_ok hi8, e4,
    e10, u3']
  simp only [u1', u2']

/-- The line-fold slot function of relation `ρ`. -/
abbrev lfK (op li : Slice U32) (rho : ℕ) : ℕ → K :=
  lfvP (embR φ 1073741824) (Wl B φ w op 3) (embR φ (gs li (3 * rho))) (embR φ (gs li (3 * rho + 1)))
    (embR φ (gs li (3 * rho + 2)))

/-- The natural basis at the stored node of relation `ρ`. -/
abbrev nlK (x16 : Slice U32) (rho : ℕ) : ℕ → K := fun e => natP (embR φ (gs x16 rho)) e 10

/-- **The extracted coefficient is the model `coefP`.** -/
theorem coef_spec (hT : Tower B) (hW : w * w = B.u)
    {al zz tr inact ti op fpos rk ru li x16 : Slice U32} {nf rho i : Usize} {z : A8}
    (h : R1CertBuild.coef al zz tr inact ti op fpos rk ru li x16 nf rho i = ok z) :
    ψ8 B φ w z = coefP nf.val (Wl B φ w op 2) (Wl B φ w op 3) (embR φ 536870912)
      (w2K B φ w al zz tr inact ti op) (gN fpos) (lfK B φ w op li rho.val) (nlK φ x16 rho.val)
      (gN rk rho.val) (gN ru rho.val) i.val := by
  unfold R1CertBuild.coef at h
  obtain ⟨kind, hk, h⟩ := bind_eq_ok h
  have ek : kind.val = gN rk rho.val := by rw [(index_ok hk).2]; rfl
  unfold coefP
  by_cases k0 : kind.val = 0
  · rw [if_pos ((ueq32 (lit := 0#u32) (n := 0) (by simp)).2 k0)] at h
    rw [if_pos (by rw [← ek]; exact k0)]
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
    obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
    rw [psi_wbase B φ w h, add_ok hi3, Nat.cast_add, map_add, fromBool_zp _ hi1, fromBool_zp _ hi2,
      flag_iff (ueq (x := i) u0'), flag_iff (ueq (x := i) u4'), embR_ite, embR_ite]
  rw [if_neg (fun h' => k0 ((ueq32 (lit := 0#u32) (n := 0) (by simp)).1 h'))] at h
  rw [if_neg (by rw [← ek]; exact k0)]
  by_cases k1 : kind.val = 1
  · rw [if_pos ((ueq32 (lit := 1#u32) (n := 1) (by simp)).2 k1)] at h
    rw [if_pos (by rw [← ek]; exact k1)]
    by_cases h7 : i.val < 7
    · rw [if_pos (by rw [UScalar.lt_equiv]; simpa using h7)] at h
      rw [if_pos h7]
      obtain ⟨a, ha, h⟩ := bind_eq_ok h
      obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
      obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
      obtain ⟨a3, ha3, h⟩ := bind_eq_ok h
      obtain ⟨a4, ha4, h⟩ := bind_eq_ok h
      rw [psi_wsub B φ w h, psi_wzero B φ w ha, psi_wmul B φ w hT hW ha4, wq_quarter B φ w ha1,
        psi_wpow B φ w hT hW ha3, psi_wget B φ w ha2, u2']
    · rw [if_neg (by rw [UScalar.lt_equiv]; simpa using h7)] at h
      rw [if_neg h7]
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      rw [psi_wbase B φ w h, fromBool_zp _ hi1, flag_or, embR_ite]
  rw [if_neg (fun h' => k1 ((ueq32 (lit := 1#u32) (n := 1) (by simp)).1 h'))] at h
  rw [if_neg (by rw [← ek]; exact k1)]
  by_cases k2 : kind.val = 2
  · rw [if_pos ((ueq32 (lit := 2#u32) (n := 2) (by simp)).2 k2)] at h
    rw [if_pos (by rw [← ek]; exact k2)]
    by_cases h7 : i.val < 7
    · rw [if_pos (by rw [UScalar.lt_equiv]; simpa using h7)] at h
      rw [if_pos h7, psi_wzero B φ w h]
    rw [if_neg (by rw [UScalar.lt_equiv]; simpa using h7)] at h
    rw [if_neg h7]
    by_cases h14 : i.val < 14
    · rw [if_pos (by rw [UScalar.lt_equiv]; simpa using h14)] at h
      rw [if_pos h14]
      obtain ⟨a, ha, h⟩ := bind_eq_ok h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      rw [psi_wpow B φ w hT hW h, psi_wget B φ w ha, (sub_ok hi1).1, u3', u7']
    rw [if_neg (by rw [UScalar.lt_equiv]; simpa using h14)] at h
    rw [if_neg h14]
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
    have e1 : i1.val = 14 + nf.val := by rw [add_ok hi1]; simp
    by_cases hn : i.val < 14 + nf.val
    · rw [if_pos (by rw [UScalar.lt_equiv, e1]; exact hn)] at h
      rw [if_pos hn, psi_wzero B φ w h]
    · rw [if_neg (by rw [UScalar.lt_equiv, e1]; exact hn)] at h
      rw [if_neg hn]
      obtain ⟨a, ha, h⟩ := bind_eq_ok h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
      obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
      rw [psi_wsub B φ w h, psi_wzero B φ w ha, df2_spec B φ w hT hW ha1, (sub_ok hi2).1, e1]
  rw [if_neg (fun h' => k2 ((ueq32 (lit := 2#u32) (n := 2) (by simp)).1 h'))] at h
  rw [if_neg (by rw [← ek]; exact k2)]
  by_cases k3 : kind.val = 3
  · rw [if_pos ((ueq32 (lit := 3#u32) (n := 3) (by simp)).2 k3)] at h
    rw [if_pos (by rw [← ek]; exact k3)]
    by_cases h14 : i.val < 14
    · rw [if_pos (by rw [UScalar.lt_equiv]; simpa using h14)] at h
      rw [if_pos h14, psi_wzero B φ w h]
    rw [if_neg (by rw [UScalar.lt_equiv]; simpa using h14)] at h
    rw [if_neg h14]
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
    have e1 : i1.val = 14 + nf.val := by rw [add_ok hi1]; simp
    by_cases hn : i.val < 14 + nf.val
    · rw [if_pos (by rw [UScalar.lt_equiv, e1]; exact hn)] at h
      rw [if_pos hn]
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
      obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
      obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
      have e3 : i3.val = gN fpos (i.val - 14) := by rw [(index_ok hi3).2, (sub_ok hi2).1, u14]; rfl
      have e4 : i4.val = gN ru rho.val := by rw [(index_ok hi4).2]; rfl
      have hc : (i3 = i4) ↔ (gN fpos (i.val - 14) = gN ru rho.val) := by rw [UScalar.eq_equiv, e3, e4]
      rw [psi_wbase B φ w h, fromBool_zp _ hi5, flag_iff hc, embR_ite]
    · rw [if_neg (by rw [UScalar.lt_equiv, e1]; exact hn)] at h
      rw [if_neg hn, psi_wzero B φ w h]
  rw [if_neg (fun h' => k3 ((ueq32 (lit := 3#u32) (n := 3) (by simp)).1 h'))] at h
  rw [if_neg (by rw [← ek]; exact k3)]
  by_cases h14 : i.val < 14
  · rw [if_pos (by rw [UScalar.lt_equiv]; simpa using h14)] at h
    rw [if_pos h14, psi_wzero B φ w h]
  rw [if_neg (by rw [UScalar.lt_equiv]; simpa using h14)] at h
  rw [if_neg h14]
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  have e1 : i1.val = 14 + nf.val := by rw [add_ok hi1]; simp
  by_cases hn : i.val < 14 + nf.val
  · rw [if_pos (by rw [UScalar.lt_equiv, e1]; exact hn)] at h
    rw [if_pos hn]
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
    obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
    have e4 : i4.val = gN fpos (i.val - 14) := by
      rw [(ok_inj hi4).symm, castUs, (index_ok hi3).2, (sub_ok hi2).1, u14]; rfl
    rw [psi_line_fold B φ w hT hW h, e4]
  · rw [if_neg (by rw [UScalar.lt_equiv, e1]; exact hn)] at h
    rw [if_neg hn]
    obtain ⟨a, ha, h⟩ := bind_eq_ok h
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
    obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
    obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
    obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
    obtain ⟨a3, ha3, h⟩ := bind_eq_ok h
    rw [psi_wsub B φ w h, psi_wzero B φ w ha, psi_wq B φ w ha3, nat_q_spec B φ hT ha2, (qbase_spec B φ ha1).1,
      idx_z' hi3, (sub_ok hi2).1, e1, natR_P]

#print axioms psi_pfold
#print axioms psi_lfv
#print axioms psi_line_fold
#print axioms coef_spec

end R1Z.CertBuild

end
