import R1Z.CertBuildExtracted
import R1Z.CertCheckBase

/-! D57.3: M31 and QM31-limb specs of the extracted builder arithmetic
(`R1CertBuild.fadd/fsub/fmul/qadd/qsub/qmul/vget`).  Every result is canonical
(`< P`) and its `ZP` value is the field operation; `qmul` computes the QM31
product limbs of CM31[u]/(u² - (2+i)). -/

set_option autoImplicit false

namespace R1Z.CertBuild
open Aeneas Aeneas.Std Result R1Z.CertCheck
open scoped BigOperators

theorem PB_val : R1CertBuild.P.val = PN := by
  unfold R1CertBuild.P
  rfl

theorem PB_ne : R1CertBuild.P.val ≠ 0 := by rw [PB_val]; norm_num

theorem modPB {x z : U64} (h : x % R1CertBuild.P = ok z) : z.val < PN ∧ (z.val : ZP) = (x.val : ZP) := by
  have e := rem_ok PB_ne h
  rw [PB_val] at e
  rw [e]
  exact ⟨Nat.mod_lt _ (by norm_num), ZMod.natCast_mod _ _⟩

theorem PBZ : ((R1CertBuild.P.val : ℕ) : ZP) = 0 := by rw [PB_val]; exact ZMod.natCast_self PN

/-- A canonical M31 result. -/
def Canon (z : U32) (v : ZP) : Prop := z.val < PN ∧ (z.val : ZP) = v

theorem out32 {x : U64} (hx : x.val < PN) : (UScalar.cast .U32 x).val = x.val :=
  cast32 x (lt_trans hx (by norm_num))

theorem fadd_spec {x y z : U32} (h : R1CertBuild.fadd x y = ok z) :
    Canon z ((x.val : ZP) + (y.val : ZP)) := by
  unfold R1CertBuild.fadd at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  have ez := (ok_inj h).symm
  obtain ⟨hlt, hv⟩ := modPB hi3
  rw [ez]
  unfold Canon
  rw [out32 hlt]
  refine ⟨hlt, ?_⟩
  rw [hv, add_ok hi2, Nat.cast_add, (ok_inj hi).symm, (ok_inj hi1).symm, cast64, cast64]

theorem fmul_spec {x y z : U32} (h : R1CertBuild.fmul x y = ok z) :
    Canon z ((x.val : ZP) * (y.val : ZP)) := by
  unfold R1CertBuild.fmul at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  have ez := (ok_inj h).symm
  obtain ⟨hlt, hv⟩ := modPB hi3
  rw [ez]
  unfold Canon
  rw [out32 hlt]
  refine ⟨hlt, ?_⟩
  rw [hv, mul_ok hi2, Nat.cast_mul, (ok_inj hi).symm, (ok_inj hi1).symm, cast64, cast64]

theorem fsub_spec {x y z : U32} (h : R1CertBuild.fsub x y = ok z) :
    Canon z ((x.val : ZP) - (y.val : ZP)) := by
  unfold R1CertBuild.fsub at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
  obtain ⟨i6, hi6, h⟩ := bind_eq_ok h
  have ez := (ok_inj h).symm
  obtain ⟨hlt, hv⟩ := modPB hi6
  rw [ez]
  unfold Canon
  rw [out32 hlt]
  refine ⟨hlt, ?_⟩
  obtain ⟨e5, hle⟩ := sub_ok hi5
  rw [hv, e5, Nat.cast_sub hle, add_ok hi2, Nat.cast_add, PBZ, add_zero, (modPB hi1).2,
    (modPB hi4).2, (ok_inj hi).symm, (ok_inj hi3).symm, cast64, cast64]

/-! ### QM31 limb arrays -/

abbrev A4 := Array U32 4#usize

/-- Limb `k` of a QM31 array, in `ZP`. -/
def ga (x : A4) (k : ℕ) : ZP := ((x.val[k]!).val : ZP)

/-- All four limbs canonical. -/
def CanonA (x : A4) : Prop := ∀ k, k < 4 → (x.val[k]!).val < PN

theorem aidx_ok {x : A4} {i : Usize} {v : U32} (h : Array.index_usize x i = ok v) : v = x.val[i.val]! := by
  unfold Array.index_usize at h
  rw [Array.getElem?_Usize_eq] at h
  cases hc : x.val[i.val]? with
  | none => rw [hc] at h; cases h
  | some y =>
    rw [hc] at h
    cases h
    rw [List.getElem!_eq_getElem?_getD, hc]
    rfl

theorem make_get (a b c d : U32) :
    (Array.make 4#usize [a, b, c, d]).val[0]! = a ∧ (Array.make 4#usize [a, b, c, d]).val[1]! = b ∧
    (Array.make 4#usize [a, b, c, d]).val[2]! = c ∧ (Array.make 4#usize [a, b, c, d]).val[3]! = d := by
  simp [Array.make]

theorem make_canon {a b c d : U32} (ha : a.val < PN) (hb : b.val < PN) (hc : c.val < PN)
    (hd : d.val < PN) : CanonA (Array.make 4#usize [a, b, c, d]) := by
  intro k hk
  obtain ⟨e0, e1, e2, e3⟩ := make_get a b c d
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · rw [e0]; exact ha
  · rw [e1]; exact hb
  · rw [e2]; exact hc
  · rw [e3]; exact hd

theorem make_ga (a b c d : U32) :
    ga (Array.make 4#usize [a, b, c, d]) 0 = (a.val : ZP) ∧ ga (Array.make 4#usize [a, b, c, d]) 1 = (b.val : ZP) ∧
    ga (Array.make 4#usize [a, b, c, d]) 2 = (c.val : ZP) ∧ ga (Array.make 4#usize [a, b, c, d]) 3 = (d.val : ZP) := by
  obtain ⟨e0, e1, e2, e3⟩ := make_get a b c d
  exact ⟨by rw [ga, e0], by rw [ga, e1], by rw [ga, e2], by rw [ga, e3]⟩

theorem ai {x : A4} {v : U32} {i : Usize} (h : Array.index_usize x i = ok v) (k : ℕ) (hk : i.val = k) :
    (v.val : ZP) = ga x k := by
  rw [aidx_ok h, hk]; rfl

/-- The limbwise statement of a binary limb operation. -/
def Limbwise (f : ZP → ZP → ZP) (x y z : A4) : Prop :=
  CanonA z ∧ ∀ k, k < 4 → ga z k = f (ga x k) (ga y k)

theorem u0' : (0#usize : Usize).val = 0 := by simp
theorem u1' : (1#usize : Usize).val = 1 := by simp
theorem u2' : (2#usize : Usize).val = 2 := by simp
theorem u3' : (3#usize : Usize).val = 3 := by simp

theorem limb4 {z : A4} {f0 f1 f2 f3 : ZP} {a b c d : U32} (hz : z = Array.make 4#usize [a, b, c, d])
    (ha : Canon a f0) (hb : Canon b f1) (hc : Canon c f2) (hd : Canon d f3) :
    CanonA z ∧ ga z 0 = f0 ∧ ga z 1 = f1 ∧ ga z 2 = f2 ∧ ga z 3 = f3 := by
  subst hz
  obtain ⟨g0, g1, g2, g3⟩ := make_ga a b c d
  exact ⟨make_canon ha.1 hb.1 hc.1 hd.1, g0.trans ha.2, g1.trans hb.2, g2.trans hc.2, g3.trans hd.2⟩

theorem qadd_spec {x y z : A4} (h : R1CertBuild.qadd x y = ok z) :
    CanonA z ∧ ga z 0 = ga x 0 + ga y 0 ∧ ga z 1 = ga x 1 + ga y 1 ∧
      ga z 2 = ga x 2 + ga y 2 ∧ ga z 3 = ga x 3 + ga y 3 := by
  unfold R1CertBuild.qadd at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
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
  have s2 := fadd_spec hi2
  have s5 := fadd_spec hi5
  have s8 := fadd_spec hi8
  have s11 := fadd_spec hi11
  rw [ai hi 0 u0', ai hi1 0 u0'] at s2
  rw [ai hi3 1 u1', ai hi4 1 u1'] at s5
  rw [ai hi6 2 u2', ai hi7 2 u2'] at s8
  rw [ai hi9 3 u3', ai hi10 3 u3'] at s11
  exact limb4 (ok_inj h).symm s2 s5 s8 s11

theorem qsub_spec {x y z : A4} (h : R1CertBuild.qsub x y = ok z) :
    CanonA z ∧ ga z 0 = ga x 0 - ga y 0 ∧ ga z 1 = ga x 1 - ga y 1 ∧
      ga z 2 = ga x 2 - ga y 2 ∧ ga z 3 = ga x 3 - ga y 3 := by
  unfold R1CertBuild.qsub at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
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
  have s2 := fsub_spec hi2
  have s5 := fsub_spec hi5
  have s8 := fsub_spec hi8
  have s11 := fsub_spec hi11
  rw [ai hi 0 u0', ai hi1 0 u0'] at s2
  rw [ai hi3 1 u1', ai hi4 1 u1'] at s5
  rw [ai hi6 2 u2', ai hi7 2 u2'] at s8
  rw [ai hi9 3 u3', ai hi10 3 u3'] at s11
  exact limb4 (ok_inj h).symm s2 s5 s8 s11

/-- The QM31 product limbs (`qmul`). -/
def qmulZ (x0 x1 x2 x3 y0 y1 y2 y3 : ZP) : Fin 4 → ZP := fun k =>
  match k with
  | 0 => x0 * y0 - x1 * y1 + 2 * (x2 * y2 - x3 * y3) - (x2 * y3 + x3 * y2)
  | 1 => x0 * y1 + x1 * y0 + (x2 * y2 - x3 * y3) + 2 * (x2 * y3 + x3 * y2)
  | 2 => x0 * y2 - x1 * y3 + x2 * y0 - x3 * y1
  | 3 => x0 * y3 + x1 * y2 + x2 * y1 + x3 * y0

theorem canon_eq {z : U32} {v w : ZP} (h : Canon z v) (e : v = w) : Canon z w := e ▸ h

theorem qmul_spec {x y z : A4} (h : R1CertBuild.qmul x y = ok z) :
    CanonA z ∧ ∀ k : Fin 4, ga z k = qmulZ (ga x 0) (ga x 1) (ga x 2) (ga x 3) (ga y 0) (ga y 1) (ga y 2) (ga y 3) k := by
  unfold R1CertBuild.qmul at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
  obtain ⟨p, hp, h⟩ := bind_eq_ok h
  obtain ⟨i6, hi6, h⟩ := bind_eq_ok h
  obtain ⟨i7, hi7, h⟩ := bind_eq_ok h
  obtain ⟨q, hq, h⟩ := bind_eq_ok h
  obtain ⟨i8, hi8, h⟩ := bind_eq_ok h
  obtain ⟨i9, hi9, h⟩ := bind_eq_ok h
  obtain ⟨i10, hi10, h⟩ := bind_eq_ok h
  obtain ⟨i11, hi11, h⟩ := bind_eq_ok h
  obtain ⟨i12, hi12, h⟩ := bind_eq_ok h
  obtain ⟨i13, hi13, h⟩ := bind_eq_ok h
  obtain ⟨i14, hi14, h⟩ := bind_eq_ok h
  obtain ⟨i15, hi15, h⟩ := bind_eq_ok h
  obtain ⟨i16, hi16, h⟩ := bind_eq_ok h
  obtain ⟨r0, hr0, h⟩ := bind_eq_ok h
  obtain ⟨i17, hi17, h⟩ := bind_eq_ok h
  obtain ⟨i18, hi18, h⟩ := bind_eq_ok h
  obtain ⟨i19, hi19, h⟩ := bind_eq_ok h
  obtain ⟨i20, hi20, h⟩ := bind_eq_ok h
  obtain ⟨i21, hi21, h⟩ := bind_eq_ok h
  obtain ⟨r1, hr1, h⟩ := bind_eq_ok h
  obtain ⟨i22, hi22, h⟩ := bind_eq_ok h
  obtain ⟨i23, hi23, h⟩ := bind_eq_ok h
  obtain ⟨i24, hi24, h⟩ := bind_eq_ok h
  obtain ⟨i25, hi25, h⟩ := bind_eq_ok h
  obtain ⟨i26, hi26, h⟩ := bind_eq_ok h
  obtain ⟨i27, hi27, h⟩ := bind_eq_ok h
  obtain ⟨r2, hr2, h⟩ := bind_eq_ok h
  obtain ⟨i28, hi28, h⟩ := bind_eq_ok h
  obtain ⟨i29, hi29, h⟩ := bind_eq_ok h
  obtain ⟨i30, hi30, h⟩ := bind_eq_ok h
  obtain ⟨i31, hi31, h⟩ := bind_eq_ok h
  obtain ⟨i32, hi32, h⟩ := bind_eq_ok h
  obtain ⟨i33, hi33, h⟩ := bind_eq_ok h
  obtain ⟨r3, hr3, h⟩ := bind_eq_ok h
  have X0 := ai hi8 0 u0'
  have X1 := ai hi11 1 u1'
  have X2 := ai hi 2 u2'
  have X3 := ai hi3 3 u3'
  have Y0 := ai hi9 0 u0'
  have Y1 := ai hi12 1 u1'
  have Y2 := ai hi1 2 u2'
  have Y3 := ai hi4 3 u3'
  have Ep := (fsub_spec hp).2
  rw [(fmul_spec hi2).2, (fmul_spec hi5).2, X2, X3, Y2, Y3] at Ep
  have Eq := (fadd_spec hq).2
  rw [(fmul_spec hi6).2, (fmul_spec hi7).2, X2, X3, Y2, Y3] at Eq
  have S0 := fsub_spec hr0
  have S1 := fadd_spec hr1
  have S2 := fsub_spec hr2
  have S3 := fadd_spec hr3
  rw [(fadd_spec hi16).2, (fsub_spec hi14).2, (fmul_spec hi10).2, (fmul_spec hi13).2,
    (fadd_spec hi15).2, Ep, Eq, X0, X1, Y0, Y1] at S0
  rw [(fadd_spec hi20).2, (fadd_spec hi19).2, (fmul_spec hi17).2, (fmul_spec hi18).2,
    (fadd_spec hi21).2, Ep, Eq, X0, X1, Y0, Y1] at S1
  rw [(fadd_spec hi26).2, (fsub_spec hi24).2, (fmul_spec hi22).2, (fmul_spec hi23).2,
    (fmul_spec hi25).2, (fmul_spec hi27).2, X0, X1, X2, X3, Y0, Y1, Y2, Y3] at S2
  rw [(fadd_spec hi32).2, (fadd_spec hi30).2, (fmul_spec hi28).2, (fmul_spec hi29).2,
    (fmul_spec hi31).2, (fmul_spec hi33).2, X0, X1, X2, X3, Y0, Y1, Y2, Y3] at S3
  obtain ⟨hc, g0, g1, g2, g3⟩ := limb4 (ok_inj h).symm S0 S1 S2 S3
  refine ⟨hc, fun k => ?_⟩
  fin_cases k
  · simp only [qmulZ, Fin.zero_eta, Fin.isValue, Fin.val_zero]; rw [g0]; ring
  · simp only [qmulZ, Fin.mk_one, Fin.isValue, Fin.val_one]; rw [g1]; ring
  · simp only [qmulZ, Fin.reduceFinMk, Fin.isValue, Fin.val_two]; rw [g2]
  · simp only [qmulZ, Fin.reduceFinMk, Fin.isValue]; rw [g3]

theorem fromBool32 (b : Bool) : (UScalar.cast_fromBool .U32 b).val = b.toNat :=
  UScalar.cast_fromBool_val_eq _ _

theorem vget_spec {p k q : Usize} {z : A4} (h : R1CertBuild.vget p k q = ok z) :
    CanonA z ∧ ∀ l, l < 4 → ga z l = if q.val = p.val ∧ k.val = l then 1 else 0 := by
  unfold R1CertBuild.vget at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  have cb : ∀ (l : ℕ) (hl : l < 4) (w : U32) (lit : Usize), lit.val = l →
      lift (UScalar.cast_fromBool .U32 (decide (q = p) && decide (k = lit))) = ok w →
      Canon w (if q.val = p.val ∧ k.val = l then 1 else 0) := by
    intro l hl w lit hlit hw
    have e : (decide (q = p) && decide (k = lit)) = decide (q.val = p.val ∧ k.val = l) := by
      rw [Bool.decide_and]
      congr 1
      · exact decide_eq_decide.2 (UScalar.eq_equiv q p)
      · exact decide_eq_decide.2 (by rw [UScalar.eq_equiv, hlit])
    rw [(ok_inj hw).symm]
    unfold Canon
    rw [fromBool32, e]
    by_cases hc : q.val = p.val ∧ k.val = l
    · rw [decide_eq_true hc, if_pos hc]; simp [PN]
    · rw [decide_eq_false hc, if_neg hc]; simp [PN]
  have c0 := cb 0 (by norm_num) i 0#usize u0' hi
  have c1 := cb 1 (by norm_num) i1 1#usize u1' hi1
  have c2 := cb 2 (by norm_num) i2 2#usize u2' hi2
  have c3 := cb 3 (by norm_num) i3 3#usize u3' hi3
  obtain ⟨hc, g0, g1, g2, g3⟩ := limb4 (ok_inj h).symm c0 c1 c2 c3
  refine ⟨hc, fun l hl => ?_⟩
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
  · exact g0
  · exact g1
  · exact g2
  · exact g3

#print axioms fadd_spec
#print axioms fsub_spec
#print axioms fmul_spec
#print axioms qadd_spec
#print axioms qsub_spec
#print axioms qmul_spec
#print axioms vget_spec

end R1Z.CertBuild
