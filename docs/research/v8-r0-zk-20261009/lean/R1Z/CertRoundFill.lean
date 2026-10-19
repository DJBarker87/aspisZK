import R1Z.CertColExtracted
import R1Z.CertRelWeights
import R1Z.CertLiftEntry
import R1Z.CertBuildFill
import R1Z.CertRoundK

/-! D72.2 (hRent, hGent): the extracted round-column writer `fill_round` (c3/build builder 5)
fills `pb.round` / `pb.ground` with the CertRoundK model `srcRoundR`.

Pure part (namespace `R1Z.CertRound`, Mathlib only): the closed form of the Rust power loop
`pcR` (`pcR_closed`: coefficient `d` of `(b + w X)^e` is `b^(e-d) · C(e,d) · w^d`), the
`b`-sum of `round_row` as one loop over the ten bits (`bsum_eq`) and the bit test
(`bit_eq`).  Aeneas part (namespace `R1Z.CertBuild`): one specification per extracted
function, each loop by the generic `acc_loopG`/`mul_loopG` invariant or a structural
induction on the remaining iterations; nothing is unfolded on concrete sizes.
`fill_round_entries` is the statement `check_sound_gbat`'s `hRent`/`hGent` consume. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertRound

open scoped BigOperators

variable {K : Type} [Field K]

/-- Closed form of the Rust power loop. -/
theorem pcR_closed (b w : K) : ∀ e d, pcR b w e d =
    if d ≤ e then b ^ (e - d) * (((e.choose d : ℕ) : K) * w ^ d) else 0
  | 0, d => by
      cases d with
      | zero => simp [pcR]
      | succ d => simp [pcR]
  | e + 1, 0 => by
      rw [pcR, pcR_closed b w e 0]
      simp [pow_succ]
  | e + 1, d + 1 => by
      rw [pcR, if_neg (Nat.succ_ne_zero d), Nat.add_sub_cancel, pcR_closed b w e (d + 1), pcR_closed b w e d]
      rcases Nat.lt_trichotomy d e with hlt | heq | hgt
      · obtain ⟨m, rfl⟩ : ∃ m, e = d + 1 + m := ⟨e - (d + 1), by omega⟩
        rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
          show d + 1 + m - (d + 1) = m by omega, show d + 1 + m - d = m + 1 by omega,
          show d + 1 + m + 1 - (d + 1) = m + 1 by omega, Nat.choose_succ_succ' (d + 1 + m) d]
        push_cast
        ring
      · subst heq
        simp [Nat.choose_self, pow_succ]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        ring

/-- The `b` of round `j` as one sum over the ten bits. -/
theorem bsum_eq (A : ℕ → K) (fam j r : ℕ) (hj : j ≤ 10) :
    ∑ i ∈ Finset.range 10, (if i < j then A i * wR fam i
      else if j < i ∧ bitR r i = true then wR fam i else 0) = bR A fam j r := by
  have hsplit : ∀ i, (if i < j then A i * wR fam i else if j < i ∧ bitR r i = true then wR fam i else (0 : K)) =
      (if i < j then A i * wR fam i else 0) + (if j < i ∧ bitR r i = true then wR fam i else 0) := by
    intro i
    by_cases h1 : i < j
    · rw [if_pos h1, if_pos h1, if_neg (by omega), add_zero]
    · rw [if_neg h1, if_neg h1, zero_add]
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib, bR]
  congr 1
  have h0 : ∑ i ∈ Finset.Ico j 10, (if i < j then A i * wR fam i else 0) = 0 :=
    Finset.sum_eq_zero (fun i hi => if_neg (by rw [Finset.mem_Ico] at hi; omega))
  have h1 : ∑ i ∈ Finset.range j, (if i < j then A i * wR fam i else 0) = ∑ i ∈ Finset.range j, A i * wR fam i :=
    Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.1 hi))
  rw [← Finset.sum_range_add_sum_Ico _ hj, h0, h1, add_zero]

/-- The Rust bit test. -/
theorem bit_eq (r i : ℕ) : r / 2 ^ (9 - i) % 2 = 1 ↔ bitR r i = true := by
  rw [bitR, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]

#print axioms pcR_closed
#print axioms bsum_eq
#print axioms bit_eq

end R1Z.CertRound

namespace R1Z.CertBuild
open Aeneas Aeneas.Std Result R1Z.CertCheck R0P R1Z.CertRound
open scoped BigOperators

variable {K : Type} [Field K] {F : Subfield K} (B : PackBasis F) (φ : ZP →+* ↥F)

/-! ### Scalar helpers -/

theorem u10 : (10#usize : Usize).val = 10 := by simp

theorem tb_tbR (k : ℕ) : tb B k = tbR B.i B.u k := rfl

theorem fpow_loop_spec (x : U32) (e : Usize) :
    ∀ (k : ℕ) (acc : U32) (t : Usize) (z : U32), t.val + k = e.val →
      R1CertBuild.fpow_loop x e acc t = ok z → (z.val : ZP) = (acc.val : ZP) * (x.val : ZP) ^ k
  | 0, acc, t, z, hk, h => by
      rw [R1CertBuild.fpow_loop, if_neg (by rw [UScalar.lt_equiv]; omega)] at h
      rw [← ok_inj h, pow_zero, mul_one]
  | k + 1, acc, t, z, hk, h => by
      rw [R1CertBuild.fpow_loop, if_pos (by rw [UScalar.lt_equiv]; omega)] at h
      obtain ⟨acc1, hacc1, h⟩ := bind_eq_ok h
      obtain ⟨t1, ht1, h⟩ := bind_eq_ok h
      rw [fpow_loop_spec x e k acc1 t1 z (by rw [add_ok ht1]; simp; omega) h, (fmul_spec hacc1).2, pow_succ]
      ring

theorem fpow_spec {x : U32} {e : Usize} {z : U32} (h : R1CertBuild.fpow x e = ok z) :
    (z.val : ZP) = (x.val : ZP) ^ e.val := by
  rw [fpow_loop_spec x e e.val 1#u32 0#usize z (by simp) h]
  simp

theorem binom_loop_spec (e d : Usize) :
    ∀ (k : ℕ) (acc : U64) (i : Usize) (z : U64), i.val + k = d.val → acc.val = e.val.choose i.val →
      R1CertBuild.binom_loop e d acc i = ok z → z.val = e.val.choose d.val
  | 0, acc, i, z, hk, ha, h => by
      rw [R1CertBuild.binom_loop, if_neg (by rw [UScalar.lt_equiv]; omega)] at h
      rw [← ok_inj h, ha, show i.val = d.val by omega]
  | k + 1, acc, i, z, hk, ha, h => by
      rw [R1CertBuild.binom_loop, if_pos (by rw [UScalar.lt_equiv]; omega)] at h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
      obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
      obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
      obtain ⟨acc1, hacc1, h⟩ := bind_eq_ok h
      have e1 := sub_ok hi1
      have e2 : i2.val = i1.val := by rw [(ok_inj hi2).symm, castUs64]
      have e3 : i3.val = acc.val * i2.val := mul_ok hi3
      have e4 : i4.val = i.val + 1 := by rw [add_ok hi4]; simp
      have e5 : i5.val = i4.val := by rw [(ok_inj hi5).symm, castUs64]
      have e6 : acc1.val = i3.val / i5.val := div_ok (by rw [e5, e4]; omega) hacc1
      refine binom_loop_spec e d k acc1 i4 z (by omega) ?_ h
      rw [e6, e3, e2, e5, e4, e1.1, ha, ← Nat.choose_succ_right_eq e.val i.val, Nat.mul_div_cancel _ (by omega)]

theorem binom_spec {e d : Usize} {z : U32} (h : R1CertBuild.binom e d = ok z) :
    (z.val : ZP) = ((e.val.choose d.val : ℕ) : ZP) := by
  unfold R1CertBuild.binom at h
  obtain ⟨acc, hacc, h⟩ := bind_eq_ok h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  have ea := binom_loop_spec e d d.val 1#u64 0#usize acc (by simp) (by simp) hacc
  obtain ⟨hlt, hv⟩ := modPB hi
  rw [(ok_inj h).symm, out32 hlt, hv, ea]

theorem famr_spec {c v : Usize} (h : R1CertBuild.famr c = ok v) : v.val = famR c.val := by
  unfold R1CertBuild.famr at h
  unfold famR
  by_cases e : c.val = 10
  · rw [if_pos ((ueq (lit := 10#usize) (n := 10) (by simp)).2 e)] at h
    obtain rfl := ok_inj h
    rw [if_pos e]; simp
  · rw [if_neg (fun h' => e ((ueq (lit := 10#usize) (n := 10) (by simp)).1 h'))] at h
    obtain rfl := ok_inj h
    rw [if_neg e]; simp

theorem famr_le {c v : Usize} (h : R1CertBuild.famr c = ok v) : v.val ≤ 16 := by
  rw [famr_spec h]
  unfold famR
  split_ifs <;> omega

theorem EXP_get {i v : Usize} (hi : i.val < 10) (h : Array.index_usize R1CertBuild.EXP i = ok v) :
    v.val = expR i.val := by
  rw [aidx_ok' h]
  unfold R1CertBuild.EXP expR
  rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨
    i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9) with e | e | e | e | e | e | e | e | e | e <;>
    simp [e, Array.make]

theorem exr_spec {c v : Usize} (h : R1CertBuild.exr c = ok v) : v.val = exR c.val := by
  unfold R1CertBuild.exr at h
  unfold exR
  by_cases e10 : c.val = 10
  · rw [if_pos ((ueq (lit := 10#usize) (n := 10) (by simp)).2 e10)] at h
    obtain rfl := ok_inj h
    rw [if_pos e10]; simp
  · rw [if_neg (fun h' => e10 ((ueq (lit := 10#usize) (n := 10) (by simp)).1 h'))] at h
    rw [if_neg e10]
    by_cases hl : c.val < 10
    · rw [if_pos (by rw [UScalar.lt_equiv]; simpa using hl)] at h
      exact EXP_get hl h
    · rw [if_neg (by rw [UScalar.lt_equiv]; simpa using hl)] at h
      obtain rfl := ok_inj h
      unfold expR
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      simp

theorem rotr_spec {c : Usize} {z : A4} (h : R1CertBuild.rotr c = ok z) : ψa B φ z = rotR B.i B.u c.val := by
  unfold R1CertBuild.rotr at h
  unfold rotR
  by_cases e10 : c.val = 10
  · rw [if_pos ((ueq (lit := 10#usize) (n := 10) (by simp)).2 e10)] at h
    rw [if_pos e10, qone_spec B φ h]
  · rw [if_neg (fun h' => e10 ((ueq (lit := 10#usize) (n := 10) (by simp)).1 h'))] at h
    rw [if_neg e10]
    obtain ⟨i, hi, h⟩ := bind_eq_ok h
    rw [tbq_spec B φ h, rem_ok (by simp) hi, tb_tbR B]
    simp

theorem wr_spec {fam i : Usize} {z : U32} (hf : fam.val ≤ 16) (hi : i.val < 10) (h : R1CertBuild.wr fam i = ok z) :
    embR φ (z.val : ZP) = wR (K := K) fam.val i.val := by
  unfold R1CertBuild.wr at h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
  obtain ⟨i6, hi6, h⟩ := bind_eq_ok h
  have e6 : i6.val = 3 + 22 * i.val + fam.val * (17 + 8 * i.val) := by
    rw [add_ok hi6, add_ok hi2, mul_ok hi1, mul_ok hi5, add_ok hi4, mul_ok hi3]
    simp
  have hb : i6.val < 2 ^ 32 := by
    rw [e6]
    have : fam.val * (17 + 8 * i.val) ≤ 16 * (17 + 8 * 9) := Nat.mul_le_mul hf (by omega)
    omega
  rw [(ok_inj h).symm, castU32 i6 hb, e6, embR_nat, wR]

theorem bitr_spec {r i v : Usize} (hi : i.val < 10) (h : R1CertBuild.bitr r i = ok v) :
    v.val = r.val / 2 ^ (9 - i.val) % 2 := by
  unfold R1CertBuild.bitr at h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  have hp2 := P2_get hi hi1
  have hne : i1.val ≠ 0 := by rw [hp2]; positivity
  rw [rem_ok (by simp) h, div_ok hne hi2, hp2]
  simp

/-- The bit branch of the Rust code (`bitr r i == 1`). -/
theorem bit_true {r i v : Usize} (hi : i.val < 10) (h : R1CertBuild.bitr r i = ok v) :
    v = 1#usize ↔ bitR r.val i.val = true := by
  rw [ueq (lit := 1#usize) (n := 1) (by simp), bitr_spec hi h, bit_eq]

/-- `cast_fromBool (c == lit)` in `K`. -/
theorem embR_flagU {lit : Usize} {n : ℕ} (hl : lit.val = n) {c : Usize} {i : U32}
    (h : lift (UScalar.cast_fromBool .U32 (decide (c = lit))) = ok i) :
    embR (K := K) φ (i.val : ZP) = if c.val = n then 1 else 0 := by
  rw [fromBool_zp _ h]
  by_cases e : c.val = n
  · rw [if_pos (decide_eq_true ((ueq hl).2 e)), if_pos e, map_one]
  · rw [if_neg (by simpa using fun h' => e ((ueq hl).1 h')), if_neg e, map_zero]

/-- `cast_fromBool (c == 10 && d == 0)` in `K`. -/
theorem embR_flag2 {c d : Usize} {i : U32}
    (h : lift (UScalar.cast_fromBool .U32 (decide (c = 10#usize) && decide (d = 0#usize))) = ok i) :
    embR (K := K) φ (i.val : ZP) = if c.val = 10 ∧ d.val = 0 then 1 else 0 := by
  rw [fromBool_zp _ h]
  have q1 := ueq (x := c) (lit := 10#usize) (n := 10) (by simp)
  have q2 := ueq (x := d) (lit := 0#usize) (n := 0) (by simp)
  by_cases e1 : c.val = 10 <;> by_cases e2 : d.val = 0 <;> simp [q1, q2, e1, e2]

/-! ### `round_row` pieces -/

theorem pcoef_spec (hT : Tower B) {b : A4} {w : U32} {e d : Usize} {z : A4}
    (h : R1CertBuild.pcoef b w e d = ok z) :
    ψa B φ z = pcR (ψa B φ b) (embR φ (w.val : ZP)) e.val d.val := by
  rw [pcR_closed]
  unfold R1CertBuild.pcoef at h
  by_cases hd : d.val ≤ e.val
  · rw [if_pos (by rw [UScalar.le_equiv]; exact hd)] at h
    rw [if_pos hd]
    obtain ⟨i, hi, h⟩ := bind_eq_ok h
    obtain ⟨a, ha, h⟩ := bind_eq_ok h
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
    obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
    obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
    rw [psi_qmul B φ hT h, qpow_spec B φ hT ha, (qbase_spec B φ ha1).1, (fmul_spec hi3).2, binom_spec hi1,
      fpow_spec hi2, (sub_ok hi).1, map_mul, map_pow, embR_nat φ (e.val.choose d.val)]
  · rw [if_neg (by rw [UScalar.le_equiv]; exact hd)] at h
    rw [if_neg hd, ← ok_inj h, psi_zero]

theorem pgv_spec (hT : Tower B) {c : Usize} {b pref : A4} {w : U32} {d : Usize} {z : A4}
    (h : R1CertBuild.pgv c b w pref d = ok z) :
    ψa B φ z = pgR c.val (ψa B φ b) (embR φ (w.val : ZP)) d.val * ψa B φ pref * rotR B.i B.u c.val := by
  unfold R1CertBuild.pgv at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
  obtain ⟨g, hg, h⟩ := bind_eq_ok h
  obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
  obtain ⟨a3, ha3, h⟩ := bind_eq_ok h
  rw [psi_qmul B φ hT h, psi_qmul B φ hT ha2, rotr_spec B φ ha3, psi_qadd B φ hg, pcoef_spec B φ hT ha,
    (qbase_spec B φ ha1).1, embR_flag2 φ hi1, exr_spec hi, pgR]

theorem bwt_spec {fam r i : Usize} {z : U32} (hf : fam.val ≤ 16) (hi : i.val < 10)
    (h : R1CertBuild.bwt fam r i = ok z) :
    embR φ (z.val : ZP) = if bitR r.val i.val = true then wR (K := K) fam.val i.val else 0 := by
  unfold R1CertBuild.bwt at h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  by_cases e1 : bitR r.val i.val = true
  · rw [if_pos ((bit_true hi hi1).2 e1)] at h
    rw [if_pos e1, wr_spec φ hf hi h]
  · rw [if_neg (fun h' => e1 ((bit_true hi hi1).1 h'))] at h
    obtain rfl := ok_inj h
    rw [if_neg e1]
    simp

theorem boolw_spec {fam r : Usize} {z : A4} (hf : fam.val ≤ 16) (h : R1CertBuild.boolw fam r = ok z) :
    ψa B φ z = boolR fam.val r.val := by
  unfold R1CertBuild.boolw at h
  have E := acc_loopG (ψa B φ) (G := fun acc i => R1CertBuild.boolw_loop fam r acc i) (n := 10)
    (T := fun i => if bitR r.val i = true then wR fam.val i else 0)
    (fun a i hi => by rw [R1CertBuild.boolw_loop, if_neg (by rw [UScalar.lt_equiv]; simpa using hi)])
    (fun a i res hi h => by
      rw [R1CertBuild.boolw_loop, if_pos (by rw [UScalar.lt_equiv]; simpa using hi)] at h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
      obtain ⟨acc1, hacc1, h⟩ := bind_eq_ok h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
      refine ⟨acc1, i2, add_ok hi2, h, ?_⟩
      have hi10 : i.val < 10 := by simpa using hi
      rw [psi_qadd B φ hacc1, (qbase_spec B φ ha1).1, bwt_spec φ hf hi10 hi1])
    10 (Array.repeat 4#usize 0#u32) 0#usize z (by simp) h
  rw [E, psi_zero, zero_add, boolR]
  simp only [u0', Finset.range_eq_Ico]

theorem rr0_spec (hT : Tower B) {c r : Usize} {z : A4} (h : R1CertBuild.rr0 c r = ok z) :
    ψa B φ z = rotR B.i B.u c.val * boolR (famR c.val) r.val ^ exR c.val + (if c.val = 10 then 1 else 0) := by
  unfold R1CertBuild.rr0 at h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
  obtain ⟨a3, ha3, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨a4, ha4, h⟩ := bind_eq_ok h
  rw [psi_qadd B φ h, psi_qmul B φ hT ha3, rotr_spec B φ ha, qpow_spec B φ hT ha2, boolw_spec B φ (famr_le hi) ha1,
    exr_spec hi1, famr_spec hi, (qbase_spec B φ ha4).1, embR_flagU φ (lit := 10#usize) (n := 10) (by simp) hi2]

theorem bterm_spec (hT : Tower B) {al : Slice U32} {fam j r i : Usize} {z : A4} (hf : fam.val ≤ 16) (hi : i.val < 10)
    (h : R1CertBuild.bterm al fam j r i = ok z) :
    ψa B φ z = if i.val < j.val then Alimb B φ al i.val * wR fam.val i.val
      else if j.val < i.val ∧ bitR r.val i.val = true then wR fam.val i.val else 0 := by
  unfold R1CertBuild.bterm at h
  by_cases c1 : i.val < j.val
  · rw [if_pos (by rw [UScalar.lt_equiv]; exact c1)] at h
    obtain ⟨a, ha, h⟩ := bind_eq_ok h
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
    obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
    rw [if_pos c1, psi_qmul B φ hT h, aget_spec B φ ha, (qbase_spec B φ ha1).1, wr_spec φ hf hi hi2]
  · rw [if_neg (by rw [UScalar.lt_equiv]; exact c1)] at h
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
    rw [if_neg c1]
    by_cases c2 : j.val < i.val ∧ bitR r.val i.val = true
    · have hc : (decide (j < i) && decide (i2 = 1#usize)) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by rw [UScalar.lt_equiv]; exact c2.1, (bit_true hi hi2).2 c2.2⟩
      rw [if_pos hc] at h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
      rw [if_pos c2, (qbase_spec B φ h).1, wr_spec φ hf hi hi3]
    · have hc : ¬ ((decide (j < i) && decide (i2 = 1#usize)) = true) := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        rintro ⟨h1, h2⟩
        exact c2 ⟨by rw [UScalar.lt_equiv] at h1; exact h1, (bit_true hi hi2).1 h2⟩
      rw [if_neg hc] at h
      rw [if_neg c2, ← ok_inj h, psi_zero]

theorem bsum_spec (hT : Tower B) {al : Slice U32} {fam j r : Usize} {z : A4} (hf : fam.val ≤ 16)
    (h : R1CertBuild.bsum al fam j r = ok z) :
    ψa B φ z = ∑ i ∈ Finset.range 10, (if i < j.val then Alimb B φ al i * wR fam.val i
      else if j.val < i ∧ bitR r.val i = true then wR fam.val i else 0) := by
  unfold R1CertBuild.bsum at h
  have E := acc_loopG (ψa B φ) (G := fun acc i => R1CertBuild.bsum_loop al fam j r acc i) (n := 10)
    (T := fun i => if i < j.val then Alimb B φ al i * wR fam.val i
      else if j.val < i ∧ bitR r.val i = true then wR fam.val i else 0)
    (fun a i hi => by rw [R1CertBuild.bsum_loop, if_neg (by rw [UScalar.lt_equiv]; simpa using hi)])
    (fun a i res hi h => by
      rw [R1CertBuild.bsum_loop, if_pos (by rw [UScalar.lt_equiv]; simpa using hi)] at h
      obtain ⟨t, ht, h⟩ := bind_eq_ok h
      obtain ⟨acc1, hacc1, h⟩ := bind_eq_ok h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      refine ⟨acc1, i1, add_ok hi1, h, ?_⟩
      have hi10 : i.val < 10 := by simpa using hi
      rw [psi_qadd B φ hacc1, bterm_spec B φ hT hf hi10 ht])
    10 (Array.repeat 4#usize 0#u32) 0#usize z (by simp) h
  rw [E, psi_zero, zero_add]
  simp only [u0', Finset.range_eq_Ico]

theorem pfac_spec {al : Slice U32} {r i : Usize} {z : A4} (hi : i.val < 10) (h : R1CertBuild.pfac al r i = ok z) :
    ψa B φ z = if bitR r.val i.val = true then Alimb B φ al i.val else 1 - Alimb B φ al i.val := by
  unfold R1CertBuild.pfac at h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  by_cases e1 : bitR r.val i.val = true
  · rw [if_pos ((bit_true hi hi1).2 e1)] at h
    rw [if_pos e1, aget_spec B φ h]
  · rw [if_neg (fun h' => e1 ((bit_true hi hi1).1 h'))] at h
    obtain ⟨a, ha, h⟩ := bind_eq_ok h
    obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
    rw [if_neg e1, psi_qsub B φ h, qone_spec B φ ha, aget_spec B φ ha1]

theorem prefr_spec (hT : Tower B) {al : Slice U32} {j r : Usize} {z : A4} (hj : j.val ≤ 10)
    (h : R1CertBuild.prefr al j r = ok z) : ψa B φ z = prefR (Alimb B φ al) j.val r.val := by
  unfold R1CertBuild.prefr at h
  obtain ⟨one, hone, h⟩ := bind_eq_ok h
  have h1 := qone_spec B φ hone
  have E := mul_loopG (ψa B φ) (G := fun acc i => R1CertBuild.prefr_loop al j r acc i) (n := j.val)
    (T := fun i => if bitR r.val i = true then Alimb B φ al i else 1 - Alimb B φ al i)
    (fun a i hi => by rw [R1CertBuild.prefr_loop, if_neg (by rw [UScalar.lt_equiv]; exact hi)])
    (fun a i res hi h => by
      rw [R1CertBuild.prefr_loop, if_pos (by rw [UScalar.lt_equiv]; exact hi)] at h
      obtain ⟨x, hx, h⟩ := bind_eq_ok h
      obtain ⟨acc1, hacc1, h⟩ := bind_eq_ok h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      refine ⟨acc1, i1, add_ok hi1, h, ?_⟩
      rw [psi_qmul B φ hT hacc1, pfac_spec B φ (by omega) hx])
    j.val one 0#usize z (by simp) h
  rw [E, h1, mul_one, prefR]
  simp only [u0', Finset.range_eq_Ico]

theorem coeffr_spec {k v : Usize} (h : R1CertBuild.coeffr k = ok v) : v.val = coeffR k.val := by
  unfold R1CertBuild.coeffr at h
  unfold coeffR
  by_cases k0 : k.val = 0
  · rw [if_pos ((ueq (lit := 0#usize) (n := 0) (by simp)).2 k0)] at h
    obtain rfl := ok_inj h
    rw [if_pos k0]; simp
  · rw [if_neg (fun h' => k0 ((ueq (lit := 0#usize) (n := 0) (by simp)).1 h'))] at h
    rw [if_neg k0, add_ok h]; simp

theorem pgv1_spec (hT : Tower B) {c : Usize} {b pref : A4} {w : U32} {d : Usize} {z : A4}
    (h : R1CertBuild.pgv1 c b w pref d = ok z) :
    ψa B φ z = if d.val = 0 then 0 else
      pgR c.val (ψa B φ b) (embR φ (w.val : ZP)) (d.val - 1) * ψa B φ pref * rotR B.i B.u c.val := by
  unfold R1CertBuild.pgv1 at h
  by_cases d0 : d.val = 0
  · rw [if_pos ((ueq (lit := 0#usize) (n := 0) (by simp)).2 d0)] at h
    rw [if_pos d0, ← ok_inj h, psi_zero]
  · rw [if_neg (fun h' => d0 ((ueq (lit := 0#usize) (n := 0) (by simp)).1 h'))] at h
    obtain ⟨i, hi, h⟩ := bind_eq_ok h
    rw [if_neg d0, pgv_spec B φ hT h, (sub_ok hi).1]
    simp

theorem fullv_spec {bit : Usize} {v0 v1 z : A4} (h : R1CertBuild.fullv bit v0 v1 = ok z) :
    ψa B φ z = if bit.val = 1 then ψa B φ v1 else ψa B φ v0 - ψa B φ v1 := by
  unfold R1CertBuild.fullv at h
  by_cases e1 : bit.val = 1
  · rw [if_pos ((ueq (lit := 1#usize) (n := 1) (by simp)).2 e1)] at h
    rw [if_pos e1, ← ok_inj h]
  · rw [if_neg (fun h' => e1 ((ueq (lit := 1#usize) (n := 1) (by simp)).1 h'))] at h
    rw [if_neg e1, psi_qsub B φ h]

/-- Entry `p ≥ 1` of `round_row(a, r, c)`. -/
theorem rr_ent_spec (hT : Tower B) {al : Slice U32} {c r p : Usize} {z : A4} (hp1 : 1 ≤ p.val) (hp : p.val < 271)
    (h : R1CertBuild.rr_ent al c r p = ok z) : ψa B φ z = rrowR (Alimb B φ al) B.i B.u c.val r.val p.val := by
  unfold R1CertBuild.rr_ent at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨j, hj, h⟩ := bind_eq_ok h
  obtain ⟨k, hk, h⟩ := bind_eq_ok h
  obtain ⟨fam, hfam, h⟩ := bind_eq_ok h
  obtain ⟨b, hb, h⟩ := bind_eq_ok h
  obtain ⟨pref, hpref, h⟩ := bind_eq_ok h
  obtain ⟨w, hw, h⟩ := bind_eq_ok h
  obtain ⟨d, hd, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨v0, hv0, h⟩ := bind_eq_ok h
  obtain ⟨v1, hv1, h⟩ := bind_eq_ok h
  have ei : i.val = p.val - 1 := by rw [(sub_ok hi).1]; simp
  have ej : j.val = (p.val - 1) / 27 := by rw [div_ok (by simp) hj, ei]; simp
  have ek : k.val = (p.val - 1) % 27 := by rw [rem_ok (by simp) hk, ei]; simp
  have hj10 : j.val < 10 := by rw [ej]; omega
  have ef := famr_spec hfam
  have hf := famr_le hfam
  have ed := coeffr_spec hd
  have eb : ψa B φ b = bR (Alimb B φ al) (famR c.val) j.val r.val := by
    rw [bsum_spec B φ hT hf hb, bsum_eq _ _ _ _ (by omega), ef]
  have ew : embR φ (w.val : ZP) = wR (K := K) (famR c.val) j.val := by rw [wr_spec φ hf hj10 hw, ef]
  have ep : ψa B φ pref = prefR (Alimb B φ al) j.val r.val := prefr_spec B φ hT (by omega) hpref
  have e0 : ψa B φ v0 = pgR c.val (bR (Alimb B φ al) (famR c.val) j.val r.val) (wR (famR c.val) j.val) d.val *
      prefR (Alimb B φ al) j.val r.val * rotR B.i B.u c.val := by
    rw [pgv_spec B φ hT hv0, eb, ew, ep]
  have e1 : ψa B φ v1 = if d.val = 0 then 0 else
      pgR c.val (bR (Alimb B φ al) (famR c.val) j.val r.val) (wR (famR c.val) j.val) (d.val - 1) *
        prefR (Alimb B φ al) j.val r.val * rotR B.i B.u c.val := by
    rw [pgv1_spec B φ hT hv1, eb, ew, ep]
  have hbit := bitr_spec hj10 hi1
  unfold rrowR
  rw [if_neg (by omega), ← ej, ← ek, ← ed]
  unfold fullR
  rw [fullv_spec B φ h, e0, e1]
  by_cases eb1 : bitR r.val j.val = true
  · rw [if_pos eb1, if_pos (by rw [hbit]; exact (bit_eq r.val j.val).2 eb1)]
  · rw [if_neg eb1, if_neg (fun h' => eb1 ((bit_eq r.val j.val).1 (by rw [← hbit]; exact h')))]

theorem rr_spec (hT : Tower B) {al : Slice U32} {c r p : Usize} {z : A4} (hp : p.val < 271)
    (h : R1CertBuild.rr al c r p = ok z) : ψa B φ z = rrowR (Alimb B φ al) B.i B.u c.val r.val p.val := by
  unfold R1CertBuild.rr at h
  by_cases p0 : p.val = 0
  · rw [if_pos ((ueq (lit := 0#usize) (n := 0) (by simp)).2 p0)] at h
    rw [rr0_spec B φ hT h]
    unfold rrowR
    rw [if_pos p0]
  · rw [if_neg (fun h' => p0 ((ueq (lit := 0#usize) (n := 0) (by simp)).1 h'))] at h
    exact rr_ent_spec B φ hT (by omega) hp h

/-! ### `tail_row` -/

theorem mr_spec {co v : Usize} (h : R1CertBuild.mr co = ok v) : v.val = mR co.val := by
  unfold R1CertBuild.mr at h
  unfold mR
  by_cases c28 : co.val < 28
  · rw [if_pos (by rw [UScalar.lt_equiv]; simpa using c28)] at h
    obtain rfl := ok_inj h
    rw [if_pos c28]; simp
  · rw [if_neg (by rw [UScalar.lt_equiv]; simpa using c28)] at h
    obtain rfl := ok_inj h
    rw [if_neg c28]; simp

theorem esr_spec {d : Usize} {es : U32} (h : R1CertBuild.esr d = ok es) :
    embR (K := K) φ (es.val : ZP) = if d.val = 0 then 2 else 1 := by
  unfold R1CertBuild.esr at h
  by_cases d0 : d.val = 0
  · rw [if_pos ((ueq (lit := 0#usize) (n := 0) (by simp)).2 d0)] at h
    obtain rfl := ok_inj h
    rw [if_pos d0, embR_nat]
    simp
  · rw [if_neg (fun h' => d0 ((ueq (lit := 0#usize) (n := 0) (by simp)).1 h'))] at h
    obtain rfl := ok_inj h
    rw [if_neg d0, embR_nat]
    simp

theorem kkr_spec {d v : Usize} (h : R1CertBuild.kkr d = ok v) :
    v.val = if d.val = 0 then 0 else d.val - 1 := by
  unfold R1CertBuild.kkr at h
  by_cases d0 : d.val = 0
  · rw [if_pos ((ueq (lit := 0#usize) (n := 0) (by simp)).2 d0)] at h
    obtain rfl := ok_inj h
    rw [if_pos d0]; simp
  · rw [if_neg (fun h' => d0 ((ueq (lit := 0#usize) (n := 0) (by simp)).1 h'))] at h
    rw [if_neg d0, (sub_ok h).1]; simp

theorem p2_cast {i : Usize} {v : Usize} {u : U32} (hi : i.val < 10) (h : Array.index_usize R1CertBuild.P2 i = ok v)
    (hu : lift (UScalar.cast .U32 v) = ok u) : (u.val : ZP) = ((2 ^ (9 - i.val) : ℕ) : ZP) := by
  have hp2 := P2_get hi h
  have hb : v.val < 2 ^ 32 := by
    rw [hp2]
    exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega : 9 - i.val ≤ 9)) (by norm_num)
  rw [(ok_inj hu).symm, castU32 v hb, hp2]

theorem tmid_spec {d j k : Usize} {z : A4} (hj : j.val < 10) (h : R1CertBuild.tmid d j k = ok z) :
    ψa B φ z = if d.val ≠ 1 ∧ k.val = (if d.val = 0 then 0 else d.val - 1) then ((2 ^ (9 - j.val) : ℕ) : K)
      else 0 := by
  unfold R1CertBuild.tmid at h
  obtain ⟨kk, hkk, h⟩ := bind_eq_ok h
  have ekk := kkr_spec hkk
  have hcond : ((d != 1#usize) && decide (k = kk)) = true ↔
      (d.val ≠ 1 ∧ k.val = if d.val = 0 then 0 else d.val - 1) := by
    simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, ne_eq]
    rw [ueq (lit := 1#usize) (n := 1) (by simp), UScalar.eq_equiv, ekk]
  by_cases c3 : d.val ≠ 1 ∧ k.val = if d.val = 0 then 0 else d.val - 1
  · rw [if_pos (hcond.2 c3)] at h
    rw [if_pos c3]
    obtain ⟨i, hi, h⟩ := bind_eq_ok h
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
    rw [(qbase_spec B φ h).1, p2_cast hj hi hi1, embR_nat]
  · rw [if_neg (fun h' => c3 (hcond.1 h'))] at h
    rw [if_neg c3, ← ok_inj h, psi_zero]

theorem tcell_spec (hT : Tower B) {al : Slice U32} {co j k : Usize} {z : A4} (hj : j.val < 10)
    (h : R1CertBuild.tcell al co j k = ok z) : ψa B φ z = tcellR (Alimb B φ al) co.val j.val k.val := by
  unfold R1CertBuild.tcell at h
  obtain ⟨m, hm, h⟩ := bind_eq_ok h
  have em := mr_spec hm
  have hm9 : m.val ≤ 9 := by rw [em]; unfold mR; split_ifs <;> omega
  unfold tcellR
  rw [← em]
  by_cases c1 : j.val < m.val
  · rw [if_pos (by rw [UScalar.lt_equiv]; exact c1)] at h
    rw [if_pos c1]
    by_cases k0 : k.val = 0
    · rw [if_pos ((ueq (lit := 0#usize) (n := 0) (by simp)).2 k0)] at h
      rw [if_pos k0]
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
      obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
      obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
      obtain ⟨i6, hi6, h⟩ := bind_eq_ok h
      have e1 : i1.val = co.val % 28 := by rw [rem_ok (by simp) hi1]; simp
      have e3 : i3.val = j.val + 1 := by rw [add_ok hi3]; simp
      rw [(qbase_spec B φ h).1, (fmul_spec hi6).2, map_mul, esr_spec φ hi2, e1, p2_cast (by omega) hi4 hi5, e3,
        show 9 - (j.val + 1) = 8 - j.val by omega, embR_nat]
    · rw [if_neg (fun h' => k0 ((ueq (lit := 0#usize) (n := 0) (by simp)).1 h'))] at h
      rw [if_neg k0, ← ok_inj h, psi_zero]
  · rw [if_neg (by rw [UScalar.lt_equiv]; exact c1)] at h
    rw [if_neg c1]
    by_cases c2 : j.val = m.val
    · rw [if_pos (by rw [UScalar.eq_equiv]; exact c2)] at h
      rw [if_pos c2]
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      have e1 : i1.val = co.val % 28 := by rw [rem_ok (by simp) hi1]; simp
      rw [tmid_spec B φ hj h, e1]
    · rw [if_neg (by rw [UScalar.eq_equiv]; exact c2)] at h
      rw [if_neg c2]
      by_cases k0 : k.val = 0
      · rw [if_pos ((ueq (lit := 0#usize) (n := 0) (by simp)).2 k0)] at h
        rw [if_pos k0]
        obtain ⟨a, ha, h⟩ := bind_eq_ok h
        obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
        obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
        obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
        obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
        have e1 : i1.val = co.val % 28 := by rw [rem_ok (by simp) hi1]; simp
        rw [psi_qmul B φ hT h, qpow_spec B φ hT ha1, aget_spec B φ ha, (qbase_spec B φ ha2).1, p2_cast hj hi2 hi3,
          embR_nat, e1]
      · rw [if_neg (fun h' => k0 ((ueq (lit := 0#usize) (n := 0) (by simp)).1 h'))] at h
        rw [if_neg k0, ← ok_inj h, psi_zero]

theorem trow_spec (hT : Tower B) {al : Slice U32} {co p : Usize} {z : A4}
    (h : R1CertBuild.trow al co p = ok z) : ψa B φ z = trowR (Alimb B φ al) co.val p.val := by
  unfold R1CertBuild.trow at h
  unfold trowR
  by_cases c56 : 56 ≤ co.val
  · rw [if_pos (by rw [UScalar.le_equiv]; simpa using c56)] at h
    rw [if_pos c56, ← ok_inj h, psi_zero]
  · rw [if_neg (by rw [UScalar.le_equiv]; simpa using c56)] at h
    rw [if_neg c56]
    by_cases p0 : p.val = 0
    · rw [if_pos ((ueq (lit := 0#usize) (n := 0) (by simp)).2 p0)] at h
      rw [if_pos p0]
      obtain ⟨i, hi, h⟩ := bind_eq_ok h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
      have ei : i.val = co.val % 28 := by rw [rem_ok (by simp) hi]; simp
      rw [(qbase_spec B φ h).1, (fmul_spec hi2).2, map_mul, esr_spec φ hi1, ei, embR_nat φ ((512#u32).val)]
      simp
    · rw [if_neg (fun h' => p0 ((ueq (lit := 0#usize) (n := 0) (by simp)).1 h'))] at h
      rw [if_neg p0]
      obtain ⟨i, hi, h⟩ := bind_eq_ok h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      have ei : i.val = p.val - 1 := by rw [(sub_ok hi).1]; simp
      have ei1 : i1.val = (p.val - 1) / 27 := by rw [div_ok (by simp) hi1, ei]; simp
      by_cases c10 : 10 ≤ (p.val - 1) / 27
      · rw [if_pos (by rw [UScalar.le_equiv, ei1]; simpa using c10)] at h
        rw [if_pos c10, ← ok_inj h, psi_zero]
      · rw [if_neg (by rw [UScalar.le_equiv, ei1]; simpa using c10)] at h
        rw [if_neg c10]
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
        obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
        have ei2 : i2.val = (p.val - 1) / 27 := by rw [div_ok (by simp) hi2, ei]; simp
        have ei3 : i3.val = (p.val - 1) % 27 := by rw [rem_ok (by simp) hi3, ei]; simp
        rw [tcell_spec B φ hT (by rw [ei2]; omega) h, ei2, ei3]

/-- Entry `p` of the balanced round source (lane `c`, row `r`, tower limb `k`). -/
theorem src_ent_spec (hT : Tower B) {al tr inact : Slice U32} {c r k p : Usize} {z : A4} (hp : p.val < 271)
    (h : R1CertBuild.src_ent al tr inact c r k p = ok z) :
    ψa B φ z = srcRoundR (Alimb B φ al) (gN tr) (flK φ inact) B.i B.u c.val r.val k.val p.val := by
  unfold R1CertBuild.src_ent at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨f, hf, h⟩ := bind_eq_ok h
  have ef : ψa B φ f = flK φ inact r.val := by
    rw [(qbase_spec B φ hf).1, idx_z' hi]
    rfl
  unfold srcRoundR
  by_cases c10 : c.val < 10
  · rw [if_pos (by rw [UScalar.lt_equiv]; simpa using c10)] at h
    rw [if_pos c10]
    obtain ⟨a, ha, h⟩ := bind_eq_ok h
    obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
    obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
    rw [psi_qsub B φ h, psi_qmul B φ hT ha2, ef, rr_spec B φ hT hp ha, rr_spec B φ hT hp ha1, u0']
  · rw [if_neg (by rw [UScalar.lt_equiv]; simpa using c10)] at h
    rw [if_neg c10]
    by_cases e10 : c.val = 10
    · rw [if_pos ((ueq (lit := 10#usize) (n := 10) (by simp)).2 e10)] at h
      rw [if_pos e10]
      obtain ⟨a, ha, h⟩ := bind_eq_ok h
      obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
      obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
      obtain ⟨a3, ha3, h⟩ := bind_eq_ok h
      obtain ⟨a4, ha4, h⟩ := bind_eq_ok h
      rw [psi_qmul B φ hT h, tbq_spec B φ ha, psi_qsub B φ ha4, psi_qmul B φ hT ha3, ef, rr_spec B φ hT hp ha1,
        rr_spec B φ hT hp ha2, u0', u10, tb_tbR B]
    · rw [if_neg (fun h' => e10 ((ueq (lit := 10#usize) (n := 10) (by simp)).1 h'))] at h
      rw [if_neg e10]
      obtain ⟨a, ha, h⟩ := bind_eq_ok h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
      obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
      obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
      obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
      obtain ⟨a3, ha3, h⟩ := bind_eq_ok h
      obtain ⟨a4, ha4, h⟩ := bind_eq_ok h
      have e2 : i2.val = gN tr r.val := by rw [(ok_inj hi2).symm, castUs, (index_ok hi1).2]; rfl
      have e4 : i4.val = gN tr 0 := by rw [(ok_inj hi4).symm, castUs, (index_ok hi3).2, u0']; rfl
      rw [psi_qmul B φ hT h, tbq_spec B φ ha, psi_qsub B φ ha4, psi_qmul B φ hT ha3, ef, trow_spec B φ hT ha1,
        trow_spec B φ hT ha2, e2, e4, tb_tbR B]

/-! ### The column loops -/

theorem push_spec {v w : alloc.vec.Vec U32} {x : U32} (h : alloc.vec.Vec.push v x = ok w) :
    w.val.length = v.val.length + 1 ∧ (∀ y, y < v.val.length → w.val[y]! = v.val[y]!) ∧
      w.val[v.val.length]! = x := by
  rw [push_ok h]
  exact ⟨by simp, fun y hy => get_append_left _ _ hy, get_append_len _ _⟩

theorem push4 {o0 o1 o2 o3 o4 : alloc.vec.Vec U32} {x0 x1 x2 x3 : U32}
    (h1 : alloc.vec.Vec.push o0 x0 = ok o1) (h2 : alloc.vec.Vec.push o1 x1 = ok o2)
    (h3 : alloc.vec.Vec.push o2 x2 = ok o3) (h4 : alloc.vec.Vec.push o3 x3 = ok o4) :
    o4.val.length = o0.val.length + 4 ∧ (∀ y, y < o0.val.length → o4.val[y]! = o0.val[y]!) ∧
      o4.val[o0.val.length]! = x0 ∧ o4.val[o0.val.length + 1]! = x1 ∧ o4.val[o0.val.length + 2]! = x2 ∧
      o4.val[o0.val.length + 3]! = x3 := by
  obtain ⟨L1, P1, E1⟩ := push_spec h1
  obtain ⟨L2, P2, E2⟩ := push_spec h2
  obtain ⟨L3, P3, E3⟩ := push_spec h3
  obtain ⟨L4, P4, E4⟩ := push_spec h4
  refine ⟨by omega, fun y hy => by rw [P4 y (by omega), P3 y (by omega), P2 y (by omega), P1 y hy], ?_, ?_, ?_, ?_⟩
  · rw [P4 _ (by omega), P3 _ (by omega), P2 _ (by omega), E1]
  · rw [P4 _ (by omega), P3 _ (by omega), show o0.val.length + 1 = o1.val.length by omega, E2]
  · rw [P4 _ (by omega), show o0.val.length + 2 = o2.val.length by omega, E3]
  · rw [show o0.val.length + 3 = o3.val.length by omega, E4]

variable (al tr inact kind srow slimb : Slice U32)

theorem round_col_spec (c r k : Usize) :
    ∀ (m : ℕ) (out : alloc.vec.Vec U32) (p : Usize) (res : alloc.vec.Vec U32), p.val + m = 271 →
      R1CertBuild.round_col_loop al tr inact c r k out p = ok res →
      res.val.length = out.val.length + 4 * m ∧ (∀ y, y < out.val.length → res.val[y]! = out.val[y]!) ∧
        ∀ s, p.val ≤ s → s < 271 → ∃ (pp : Usize) (v : A4), pp.val = s ∧
          R1CertBuild.src_ent al tr inact c r k pp = ok v ∧
          ∀ l, l < 4 → res.val[out.val.length + 4 * (s - p.val) + l]! = v.val[l]!
  | 0, out, p, res, hm, h => by
      rw [R1CertBuild.round_col_loop, if_neg (by rw [UScalar.lt_equiv]; simp; omega)] at h
      rw [← ok_inj h]
      exact ⟨by simp, fun y _ => rfl, fun s h1 h2 => by omega⟩
  | m + 1, out, p, res, hm, h => by
      rw [R1CertBuild.round_col_loop, if_pos (by rw [UScalar.lt_equiv]; simp; omega)] at h
      obtain ⟨v, hv, h⟩ := bind_eq_ok h
      obtain ⟨x0, hx0, h⟩ := bind_eq_ok h
      obtain ⟨o1, ho1, h⟩ := bind_eq_ok h
      obtain ⟨x1, hx1, h⟩ := bind_eq_ok h
      obtain ⟨o2, ho2, h⟩ := bind_eq_ok h
      obtain ⟨x2, hx2, h⟩ := bind_eq_ok h
      obtain ⟨o3, ho3, h⟩ := bind_eq_ok h
      obtain ⟨x3, hx3, h⟩ := bind_eq_ok h
      obtain ⟨o4, ho4, h⟩ := bind_eq_ok h
      obtain ⟨p1, hp1, h⟩ := bind_eq_ok h
      have hp1v : p1.val = p.val + 1 := by rw [add_ok hp1]; simp
      obtain ⟨L4, Q4, E0, E1, E2, E3⟩ := push4 ho1 ho2 ho3 ho4
      obtain ⟨L, P1, P2⟩ := round_col_spec c r k m o4 p1 res (by omega) h
      refine ⟨by rw [L, L4]; ring, fun y hy => by rw [P1 y (by omega), Q4 y hy], fun s h1 h2 => ?_⟩
      by_cases es : s = p.val
      · subst es
        refine ⟨p, v, rfl, hv, fun l hl => ?_⟩
        rw [Nat.sub_self, mul_zero, add_zero, P1 _ (by omega)]
        rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with e | e | e | e <;> subst e
        · rw [add_zero, E0, aidx_ok hx0]; simp
        · rw [E1, aidx_ok hx1]; simp
        · rw [E2, aidx_ok hx2]; simp
        · rw [E3, aidx_ok hx3]; simp
      · obtain ⟨pp, vv, hpp, hvv, hl⟩ := P2 s (by omega) h2
        refine ⟨pp, vv, hpp, hvv, fun l hl' => ?_⟩
        have := hl l hl'
        rw [L4, hp1v, show out.val.length + 4 + 4 * (s - (p.val + 1)) + l =
          out.val.length + 4 * (s - p.val) + l by omega] at this
        exact this

/-- Entry `p` of round column `t` comes from `src_ent` on source `t`'s descriptors. -/
def RoundAt (t p : ℕ) (v : A4) : Prop :=
  ∃ cc rr kk pp : Usize, cc.val = gNL kind t ∧ rr.val = gNL srow t ∧ kk.val = gNL slimb t ∧ pp.val = p ∧
    R1CertBuild.src_ent al tr inact cc rr kk pp = ok v

theorem fill_round_loop_spec (n : Usize) :
    ∀ (m : ℕ) (out : alloc.vec.Vec U32) (t : Usize) (res : alloc.vec.Vec U32), t.val + m = n.val →
      R1CertBuild.fill_round_loop al tr inact kind srow slimb n out t = ok res →
      res.val.length = out.val.length + m * 1084 ∧ (∀ y, y < out.val.length → res.val[y]! = out.val[y]!) ∧
        ∀ t', t.val ≤ t' → t' < n.val → ∀ p, p < 271 → ∃ v : A4, RoundAt al tr inact kind srow slimb t' p v ∧
          ∀ l, l < 4 → res.val[out.val.length + (t' - t.val) * 1084 + (4 * p + l)]! = v.val[l]!
  | 0, out, t, res, hm, h => by
      rw [R1CertBuild.fill_round_loop, if_neg (by rw [UScalar.lt_equiv]; omega)] at h
      rw [← ok_inj h]
      exact ⟨by simp, fun y _ => rfl, fun t' h1 h2 => by omega⟩
  | m + 1, out, t, res, hm, h => by
      rw [R1CertBuild.fill_round_loop, if_pos (by rw [UScalar.lt_equiv]; omega)] at h
      obtain ⟨i, hi, h⟩ := bind_eq_ok h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
      obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
      obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok h
      obtain ⟨t1, ht1, h⟩ := bind_eq_ok h
      have ht1v : t1.val = t.val + 1 := by rw [add_ok ht1]; simp
      unfold R1CertBuild.round_col at hout1
      obtain ⟨L1, Q1, Q2⟩ := round_col_spec al tr inact i1 i3 i5 271 out 0#usize out1 (by simp) hout1
      obtain ⟨L, P1, P2⟩ := fill_round_loop_spec n m out1 t1 res (by omega) h
      refine ⟨by rw [L, L1]; ring, fun y hy => by rw [P1 y (by omega), Q1 y hy], fun t' h1 h2 p hp => ?_⟩
      by_cases et : t' = t.val
      · subst et
        obtain ⟨pp, v, hpp, hv, hl⟩ := Q2 p (by simp) hp
        refine ⟨v, ⟨i1, i3, i5, pp, ?_, ?_, ?_, hpp, hv⟩, fun l hl4 => ?_⟩
        · rw [(ok_inj hi1).symm, castUs, (index_ok hi).2]; rfl
        · rw [(ok_inj hi3).symm, castUs, (index_ok hi2).2]; rfl
        · rw [(ok_inj hi5).symm, castUs, (index_ok hi4).2]; rfl
        · have e := hl l hl4
          simp only [u0', Nat.sub_zero] at e
          rw [Nat.sub_self, zero_mul, add_zero, P1 _ (by omega), ← Nat.add_assoc]
          exact e
      · obtain ⟨v, hv, hl⟩ := P2 t' (by omega) h2 p hp
        refine ⟨v, hv, fun l hl4 => ?_⟩
        have := hl l hl4
        rw [L1, ht1v, show out.val.length + 4 * 271 + (t' - (t.val + 1)) * 1084 + (4 * p + l) =
          out.val.length + (t' - t.val) * 1084 + (4 * p + l) by omega] at this
        exact this

theorem fill_round_spec {n : Usize} {res : alloc.vec.Vec U32}
    (h : R1CertBuild.fill_round al tr inact kind srow slimb n = ok res) :
    ∀ t, t < n.val → ∀ p, p < 271 → ∃ v : A4, RoundAt al tr inact kind srow slimb t p v ∧
      ∀ l, l < 4 → res.val[t * 1084 + (4 * p + l)]! = v.val[l]! := by
  obtain ⟨-, -, P⟩ := fill_round_loop_spec al tr inact kind srow slimb n n.val
    (alloc.vec.Vec.new U32) 0#usize res (by simp) h
  intro t ht p hp
  have := P t (by simp) ht p hp
  simpa using this

/-- Four limbs of a column entry, packed, are the array's `K₄` value. -/
theorem pack4_of (v : A4) (f : ℕ → U32) (hf : ∀ l, l < 4 → f l = v.val[l]!) :
    pack4 B (fun l : Fin 4 => ((φ ((f l.val).val : ZP) : F) : K)) = ψa B φ v := by
  have h0 := hf 0 (by norm_num)
  have h1 := hf 1 (by norm_num)
  have h2 := hf 2 (by norm_num)
  have h3 := hf 3 (by norm_num)
  show ((φ ((f 0).val : ZP) : F) : K) + B.i * ((φ ((f 1).val : ZP) : F) : K) +
    B.u * ((φ ((f 2).val : ZP) : F) : K) + B.i * B.u * ((φ ((f 3).val : ZP) : F) : K) = _
  rw [h0, h1, h2, h3]
  rfl

/-- **`fill_round_entries`**: entry `p` of column `t` of a `fill_round` output packs to the
CertRoundK model `srcRoundR` of source `t` (lane `kind t`, row `srow t`, limb `slimb t`). -/
theorem fill_round_entries (hT : Tower B) {n : Usize} {res : alloc.vec.Vec U32}
    (h : R1CertBuild.fill_round al tr inact kind srow slimb n = ok res) (t p : ℕ) (ht : t < n.val) (hp : p < 271) :
    pack4 B (fun l : Fin 4 => ((φ ((res.val[t * 1084 + (4 * p + l.val)]!).val : ZP) : F) : K)) =
      srcRoundR (Alimb B φ al) (gN tr) (flK φ inact) B.i B.u (gNL kind t) (gNL srow t) (gNL slimb t) p := by
  obtain ⟨v, ⟨cc, rr, kk, pp, hcc, hrr, hkk, hpp, hv⟩, hl⟩ := fill_round_spec al tr inact kind srow slimb h t ht p hp
  have e := pack4_of B φ v (fun l => res.val[t * 1084 + (4 * p + l)]!) hl
  rw [src_ent_spec B φ hT (by omega) hv, hcc, hrr, hkk, hpp] at e
  exact e

#print axioms fpow_spec
#print axioms binom_spec
#print axioms pcoef_spec
#print axioms pgv_spec
#print axioms boolw_spec
#print axioms rr0_spec
#print axioms bsum_spec
#print axioms prefr_spec
#print axioms rr_ent_spec
#print axioms rr_spec
#print axioms tcell_spec
#print axioms trow_spec
#print axioms src_ent_spec
#print axioms round_col_spec
#print axioms fill_round_loop_spec
#print axioms fill_round_spec
#print axioms fill_round_entries

end R1Z.CertBuild

end
