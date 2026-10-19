import R1Z.CertRelExtracted
import R1Z.CertLiftBasic

/-! D64 hRel (1): the WideExact model.  aspis-core `field/wide_exact.rs`:
`W = QM31[v]/(v² - u)`, `u = (0, 0, 1, 0)` the QM31 generator, limbs
`(c0.c0.a, c0.c0.b, c0.c1.a, c0.c1.b, c1.c0.a, c1.c0.b, c1.c1.a, c1.c1.b)`, i.e. the
lower QM31 then the upper one.  With `w : K` the image of `v`, an 8-limb array reads
as `ψ8 x = ψ4(x₀..x₃) + ψ4(x₄..x₇)·w` (the RfDec `wideDecode` shape).  Under the tower
premise `Tower B` and the WideExact premise `w·w = B.u` (`v² = u`) the extracted
`wmul` is the `K` product (`psi_wmul`); `wadd/wsub/wq/wbase/wzero/wunit/wget/wpow`
are the corresponding `K` operations.  `repr_psi8`: for a limb basis
`wb k = wtb k` (tower basis, then tower basis times `w`), the `wb`-coordinates of
`ψ8 x` are the limbs. -/

set_option autoImplicit false

namespace R1Z.CertBuild
open Aeneas Aeneas.Std Result R1Z.CertCheck R0P
open scoped BigOperators

variable {K : Type} [Field K] {F : Subfield K} (B : PackBasis F) (φ : ZP →+* ↥F) (w : K)

abbrev A8 := Array U32 8#usize

/-- Limb `k` of a WideExact array, in `ZP`. -/
def g8 (x : A8) (k : ℕ) : ZP := ((x.val[k]!).val : ZP)

/-- A WideExact array as a `K` value. -/
def ψ8 (x : A8) : K :=
  ψ4 B φ (g8 x 0) (g8 x 1) (g8 x 2) (g8 x 3) + ψ4 B φ (g8 x 4) (g8 x 5) (g8 x 6) (g8 x 7) * w

/-- The WideExact limb basis element `m`. -/
def wtb (m : ℕ) : K := if m < 4 then tb B m else tb B (m - 4) * w

/-- The WideExact value of the slice limbs `s[8i..8i+8]`. -/
def Wl (s : Slice U32) (i : ℕ) : K :=
  ψ4 B φ (gs s (8 * i)) (gs s (8 * i + 1)) (gs s (8 * i + 2)) (gs s (8 * i + 3)) +
    ψ4 B φ (gs s (8 * i + 4)) (gs s (8 * i + 5)) (gs s (8 * i + 6)) (gs s (8 * i + 7)) * w

theorem aidxN {n : Usize} {x : Array U32 n} {i : Usize} {v : U32} (h : Array.index_usize x i = ok v) :
    v = x.val[i.val]! := by
  unfold Array.index_usize at h
  rw [Array.getElem?_Usize_eq] at h
  cases hc : x.val[i.val]? with
  | none => rw [hc] at h; cases h
  | some y =>
    rw [hc] at h
    cases h
    rw [List.getElem!_eq_getElem?_getD, hc]
    rfl

theorem a8 {x : A8} {v : U32} {i : Usize} (h : Array.index_usize x i = ok v) (k : ℕ) (hk : i.val = k) :
    (v.val : ZP) = g8 x k := by
  rw [aidxN h, hk]; rfl

theorem make8 (a0 a1 a2 a3 a4 a5 a6 a7 : U32) :
    g8 (Array.make 8#usize [a0, a1, a2, a3, a4, a5, a6, a7]) 0 = (a0.val : ZP) ∧
    g8 (Array.make 8#usize [a0, a1, a2, a3, a4, a5, a6, a7]) 1 = (a1.val : ZP) ∧
    g8 (Array.make 8#usize [a0, a1, a2, a3, a4, a5, a6, a7]) 2 = (a2.val : ZP) ∧
    g8 (Array.make 8#usize [a0, a1, a2, a3, a4, a5, a6, a7]) 3 = (a3.val : ZP) ∧
    g8 (Array.make 8#usize [a0, a1, a2, a3, a4, a5, a6, a7]) 4 = (a4.val : ZP) ∧
    g8 (Array.make 8#usize [a0, a1, a2, a3, a4, a5, a6, a7]) 5 = (a5.val : ZP) ∧
    g8 (Array.make 8#usize [a0, a1, a2, a3, a4, a5, a6, a7]) 6 = (a6.val : ZP) ∧
    g8 (Array.make 8#usize [a0, a1, a2, a3, a4, a5, a6, a7]) 7 = (a7.val : ZP) := by
  simp [g8, Array.make]

theorem u4' : (4#usize : Usize).val = 4 := by simp
theorem u5' : (5#usize : Usize).val = 5 := by simp
theorem u6' : (6#usize : Usize).val = 6 := by simp
theorem u7' : (7#usize : Usize).val = 7 := by simp

theorem psi_wlo {x : A8} {z : A4} (h : R1CertBuild.wlo x = ok z) :
    ψa B φ z = ψ4 B φ (g8 x 0) (g8 x 1) (g8 x 2) (g8 x 3) := by
  unfold R1CertBuild.wlo at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  rw [← ok_inj h]
  obtain ⟨g0, g1, g2, g3⟩ := make_ga i i1 i2 i3
  rw [ψa, g0, g1, g2, g3, a8 hi 0 u0', a8 hi1 1 u1', a8 hi2 2 u2', a8 hi3 3 u3']

theorem psi_whi {x : A8} {z : A4} (h : R1CertBuild.whi x = ok z) :
    ψa B φ z = ψ4 B φ (g8 x 4) (g8 x 5) (g8 x 6) (g8 x 7) := by
  unfold R1CertBuild.whi at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  rw [← ok_inj h]
  obtain ⟨g0, g1, g2, g3⟩ := make_ga i i1 i2 i3
  rw [ψa, g0, g1, g2, g3, a8 hi 4 u4', a8 hi1 5 u5', a8 hi2 6 u6', a8 hi3 7 u7']

theorem psi_wmk {a b : A4} {z : A8} (h : R1CertBuild.wmk a b = ok z) :
    ψ8 B φ w z = ψa B φ a + ψa B φ b * w := by
  unfold R1CertBuild.wmk at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
  obtain ⟨i6, hi6, h⟩ := bind_eq_ok h
  obtain ⟨i7, hi7, h⟩ := bind_eq_ok h
  rw [← ok_inj h]
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := make8 i i1 i2 i3 i4 i5 i6 i7
  rw [ψ8, g0, g1, g2, g3, g4, g5, g6, g7, ai hi 0 u0', ai hi1 1 u1', ai hi2 2 u2', ai hi3 3 u3',
    ai hi4 0 u0', ai hi5 1 u1', ai hi6 2 u2', ai hi7 3 u3']
  rfl

theorem psi_wadd {x y z : A8} (h : R1CertBuild.wadd x y = ok z) :
    ψ8 B φ w z = ψ8 B φ w x + ψ8 B φ w y := by
  unfold R1CertBuild.wadd at h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
  obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
  obtain ⟨a3, ha3, h⟩ := bind_eq_ok h
  obtain ⟨a4, ha4, h⟩ := bind_eq_ok h
  obtain ⟨a5, ha5, h⟩ := bind_eq_ok h
  rw [psi_wmk B φ w h, psi_qadd B φ ha2, psi_qadd B φ ha5, psi_wlo B φ ha, psi_wlo B φ ha1,
    psi_whi B φ ha3, psi_whi B φ ha4, ψ8, ψ8]
  ring

theorem psi_wsub {x y z : A8} (h : R1CertBuild.wsub x y = ok z) :
    ψ8 B φ w z = ψ8 B φ w x - ψ8 B φ w y := by
  unfold R1CertBuild.wsub at h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
  obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
  obtain ⟨a3, ha3, h⟩ := bind_eq_ok h
  obtain ⟨a4, ha4, h⟩ := bind_eq_ok h
  obtain ⟨a5, ha5, h⟩ := bind_eq_ok h
  rw [psi_wmk B φ w h, psi_qsub B φ ha2, psi_qsub B φ ha5, psi_wlo B φ ha, psi_wlo B φ ha1,
    psi_whi B φ ha3, psi_whi B φ ha4, ψ8, ψ8]
  ring

theorem psi_u : ψa B φ (Array.make 4#usize [0#u32, 0#u32, 1#u32, 0#u32]) = B.u := by
  obtain ⟨g0, g1, g2, g3⟩ := make_ga (0#u32) 0#u32 1#u32 0#u32
  simp [ψa, ψ4, g0, g1, g2, g3]

/-- **The WideExact product is the `K` product** (`v² = u`). -/
theorem psi_wmul (hT : Tower B) (hW : w * w = B.u) {x y z : A8} (h : R1CertBuild.wmul x y = ok z) :
    ψ8 B φ w z = ψ8 B φ w x * ψ8 B φ w y := by
  unfold R1CertBuild.wmul at h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  obtain ⟨b, hb, h⟩ := bind_eq_ok h
  obtain ⟨c, hc, h⟩ := bind_eq_ok h
  obtain ⟨d, hd, h⟩ := bind_eq_ok h
  obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
  obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
  obtain ⟨a3, ha3, h⟩ := bind_eq_ok h
  obtain ⟨a4, ha4, h⟩ := bind_eq_ok h
  obtain ⟨a5, ha5, h⟩ := bind_eq_ok h
  obtain ⟨a6, ha6, h⟩ := bind_eq_ok h
  obtain ⟨a7, ha7, h⟩ := bind_eq_ok h
  rw [psi_wmk B φ w h, psi_qadd B φ ha4, psi_qmul B φ hT ha1, psi_qmul B φ hT ha3, psi_qmul B φ hT ha2,
    psi_qadd B φ ha7, psi_qmul B φ hT ha5, psi_qmul B φ hT ha6, psi_u, psi_wlo B φ ha, psi_whi B φ hb,
    psi_wlo B φ hc, psi_whi B φ hd, ψ8, ψ8]
  linear_combination (-(ψ4 B φ (g8 x 4) (g8 x 5) (g8 x 6) (g8 x 7) *
    ψ4 B φ (g8 y 4) (g8 y 5) (g8 y 6) (g8 y 7))) * hW

theorem psi_wq {a : A4} {z : A8} (h : R1CertBuild.wq a = ok z) : ψ8 B φ w z = ψa B φ a := by
  unfold R1CertBuild.wq at h
  rw [psi_wmk B φ w h, psi_zero, zero_mul, add_zero]

theorem psi_wbase {v : U32} {z : A8} (h : R1CertBuild.wbase v = ok z) : ψ8 B φ w z = embR φ (v.val : ZP) := by
  unfold R1CertBuild.wbase at h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  rw [psi_wq B φ w h, (qbase_spec B φ ha).1]

theorem psi_wzero {z : A8} (h : R1CertBuild.wzero = ok z) : ψ8 B φ w z = 0 := by
  unfold R1CertBuild.wzero at h
  rw [psi_wq B φ w h, psi_zero]

theorem psi_wget {op : Slice U32} {i : Usize} {z : A8} (h : R1CertBuild.wget op i = ok z) :
    ψ8 B φ w z = Wl B φ w op i.val := by
  unfold R1CertBuild.wget at h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
  obtain ⟨i6, hi6, h⟩ := bind_eq_ok h
  obtain ⟨i7, hi7, h⟩ := bind_eq_ok h
  obtain ⟨i8, hi8, h⟩ := bind_eq_ok h
  obtain ⟨i9, hi9, h⟩ := bind_eq_ok h
  obtain ⟨i10, hi10, h⟩ := bind_eq_ok h
  obtain ⟨i11, hi11, h⟩ := bind_eq_ok h
  obtain ⟨i12, hi12, h⟩ := bind_eq_ok h
  obtain ⟨i13, hi13, h⟩ := bind_eq_ok h
  obtain ⟨i14, hi14, h⟩ := bind_eq_ok h
  obtain ⟨i15, hi15, h⟩ := bind_eq_ok h
  obtain ⟨i16, hi16, h⟩ := bind_eq_ok h
  rw [← ok_inj h]
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := make8 i2 i4 i6 i8 i10 i12 i14 i16
  have e1 : i1.val = 8 * i.val := by rw [mul_ok hi1]; simp
  rw [ψ8, g0, g1, g2, g3, g4, g5, g6, g7, idx_z' hi2, idx_z' hi4, idx_z' hi6, idx_z' hi8, idx_z' hi10,
    idx_z' hi12, idx_z' hi14, idx_z' hi16, add_ok hi3, add_ok hi5, add_ok hi7, add_ok hi9, add_ok hi11,
    add_ok hi13, add_ok hi15, e1, Wl]
  simp

theorem psi_wpow (hT : Tower B) (hW : w * w = B.u) {x : A8} {e : Usize} {z : A8}
    (h : R1CertBuild.wpow x e = ok z) : ψ8 B φ w z = ψ8 B φ w x ^ e.val := by
  unfold R1CertBuild.wpow at h
  obtain ⟨one, hone, h⟩ := bind_eq_ok h
  obtain ⟨acc, hacc, h⟩ := bind_eq_ok h
  have E := horner_loopG (ψ8 B φ w) (ψ8 B φ w x) (G := fun acc t => R1CertBuild.wpow_loop x e acc t)
    (n := e.val) (T := fun _ => 0)
    (fun a t ht => by rw [R1CertBuild.wpow_loop, if_neg (by rw [UScalar.lt_equiv]; exact ht)])
    (fun a t res ht h => by
      rw [R1CertBuild.wpow_loop, if_pos (by rw [UScalar.lt_equiv]; exact ht)] at h
      obtain ⟨acc1, hacc1, h⟩ := bind_eq_ok h
      obtain ⟨t1, ht1, h⟩ := bind_eq_ok h
      exact ⟨acc1, t1, add_ok ht1, h, by rw [psi_wmul B φ w hT hW hacc1, add_zero]⟩)
    e.val acc 0#usize z (by simp) h
  rw [E, psi_wq B φ w hacc, qone_spec B φ hone]
  simp

theorem fromBool_zp (b : Bool) {i : U32} (h : lift (UScalar.cast_fromBool .U32 b) = ok i) :
    (i.val : ZP) = if b then 1 else 0 := by
  have e := ok_inj h
  rw [← e, fromBool32]
  cases b <;> simp

theorem psi_wunit {m : Usize} {z : A8} (hm : m.val < 8) (h : R1CertBuild.wunit m = ok z) :
    ψ8 B φ w z = wtb B w m.val := by
  unfold R1CertBuild.wunit at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
  obtain ⟨i6, hi6, h⟩ := bind_eq_ok h
  obtain ⟨i7, hi7, h⟩ := bind_eq_ok h
  rw [← ok_inj h]
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := make8 i i1 i2 i3 i4 i5 i6 i7
  have hb : ∀ (n : ℕ) (lit : Usize), lit.val = n → decide (m = lit) = decide (m.val = n) := by
    intro n lit hl
    exact decide_eq_decide.2 (ueq hl)
  rw [ψ8, g0, g1, g2, g3, g4, g5, g6, g7, fromBool_zp _ hi, fromBool_zp _ hi1, fromBool_zp _ hi2,
    fromBool_zp _ hi3, fromBool_zp _ hi4, fromBool_zp _ hi5, fromBool_zp _ hi6, fromBool_zp _ hi7,
    hb 0 _ u0', hb 1 _ u1', hb 2 _ u2', hb 3 _ u3', hb 4 _ u4', hb 5 _ u5', hb 6 _ u6', hb 7 _ u7']
  unfold wtb tb
  rcases (by omega : m.val = 0 ∨ m.val = 1 ∨ m.val = 2 ∨ m.val = 3 ∨ m.val = 4 ∨ m.val = 5 ∨
    m.val = 6 ∨ m.val = 7) with e | e | e | e | e | e | e | e <;> simp [e, ψ4]

/-- The `wb`-coordinates of `ψ8 x` are its limbs, for the WideExact limb basis. -/
theorem repr_psi8 (wb : Module.Basis (Fin 8) F K) (hwb : ∀ k : Fin 8, wb k = wtb B w k.val)
    (x : A8) (k : Fin 8) : wb.repr (ψ8 B φ w x) k = φ (g8 x k.val) := by
  have hs : ∀ (s : F) (b : K), s • b = (s : K) * b := fun s b => rfl
  have he : ∀ y : ZP, embR φ y = ((φ y : F) : K) := fun y => rfl
  have w0 : wb 0 = 1 := by rw [hwb]; rfl
  have w1 : wb 1 = B.i := by rw [hwb]; rfl
  have w2 : wb 2 = B.u := by rw [hwb]; rfl
  have w3 : wb 3 = B.i * B.u := by rw [hwb]; rfl
  have w4 : wb 4 = 1 * w := by rw [hwb]; rfl
  have w5 : wb 5 = B.i * w := by rw [hwb]; rfl
  have w6 : wb 6 = B.u * w := by rw [hwb]; rfl
  have w7 : wb 7 = B.i * B.u * w := by rw [hwb]; rfl
  have e : ψ8 B φ w x = ∑ j : Fin 8, φ (g8 x j.val) • wb j := by
    rw [Fin.sum_univ_eight]
    show _ = φ (g8 x 0) • wb 0 + φ (g8 x 1) • wb 1 + φ (g8 x 2) • wb 2 + φ (g8 x 3) • wb 3 +
      φ (g8 x 4) • wb 4 + φ (g8 x 5) • wb 5 + φ (g8 x 6) • wb 6 + φ (g8 x 7) • wb 7
    rw [w0, w1, w2, w3, w4, w5, w6, w7]
    simp only [hs, ψ8, ψ4, he]
    ring
  rw [e, Module.Basis.repr_sum_self]

#print axioms psi_wlo
#print axioms psi_whi
#print axioms psi_wmk
#print axioms psi_wadd
#print axioms psi_wsub
#print axioms psi_wmul
#print axioms psi_wq
#print axioms psi_wbase
#print axioms psi_wzero
#print axioms psi_wget
#print axioms psi_wpow
#print axioms psi_wunit
#print axioms repr_psi8

end R1Z.CertBuild
