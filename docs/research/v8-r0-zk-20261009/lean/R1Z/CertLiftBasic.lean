import R1Z.CertBuildChain

/-! D59.2 builder 2: the extracted lift-column helpers as `K` values
(`R1CertBuild.aget/scarry/point_coord/eqw/qpow/hw/nat_loop/nat_q/evq/head_q`).
`ψa` is the `K₄` value of a limb array (CertBuildTower); `A = Alimb al`. -/

set_option autoImplicit false

namespace R1Z.CertBuild
open Aeneas Aeneas.Std Result R1Z.CertCheck R0P
open scoped BigOperators

variable {K : Type} [Field K] {F : Subfield K} (B : PackBasis F) (φ : ZP →+* ↥F)

theorem mul_loopG {S : Type} (f : S → K) {G : S → Usize → Result S} {n : ℕ} {T : ℕ → K}
    (hstop : ∀ a i, ¬ i.val < n → G a i = ok a)
    (hstep : ∀ a i r, i.val < n → G a i = ok r →
      ∃ a' i', i'.val = i.val + 1 ∧ G a' i' = ok r ∧ f a' = T i.val * f a) :
    ∀ k a i r, i.val + k = n → G a i = ok r → f r = (∏ j ∈ Finset.Ico i.val n, T j) * f a
  | 0, a, i, r, hk, h => by
      rw [hstop a i (by omega)] at h
      rw [← ok_inj h, Finset.Ico_eq_empty_of_le (by omega), Finset.prod_empty, one_mul]
  | k + 1, a, i, r, hk, h => by
      obtain ⟨a', i', hi', h', ha⟩ := hstep a i r (by omega) h
      rw [mul_loopG f hstop hstep k a' i' r (by omega) h', ha, hi',
        Finset.prod_eq_prod_Ico_succ_bot (show i.val < n by omega)]
      ring

theorem qone_spec {z : A4} (h : R1CertBuild.qone = ok z) : ψa B φ z = 1 := by
  unfold R1CertBuild.qone at h
  rw [← ok_inj h]
  obtain ⟨g0, g1, g2, g3⟩ := make_ga (1#u32) 0#u32 0#u32 0#u32
  simp [ψa, ψ4, g0, g1, g2, g3]

theorem qbase_spec {v : U32} {z : A4} (h : R1CertBuild.qbase v = ok z) :
    ψa B φ z = embR φ (v.val : ZP) ∧ ga z 0 = v.val ∧ ga z 1 = 0 ∧ ga z 2 = 0 ∧ ga z 3 = 0 := by
  unfold R1CertBuild.qbase at h
  rw [← ok_inj h]
  obtain ⟨g0, g1, g2, g3⟩ := make_ga v 0#u32 0#u32 0#u32
  refine ⟨?_, g0, by rw [g1]; simp, by rw [g2]; simp, by rw [g3]; simp⟩
  simp [ψa, ψ4, g0, g1, g2, g3]

theorem aget_spec {al : Slice U32} {j : Usize} {z : A4} (h : R1CertBuild.aget al j = ok z) :
    ψa B φ z = Alimb B φ al j.val := by
  unfold R1CertBuild.aget at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
  obtain ⟨i6, hi6, h⟩ := bind_eq_ok h
  obtain ⟨i7, hi7, h⟩ := bind_eq_ok h
  rw [← ok_inj h]
  obtain ⟨g0, g1, g2, g3⟩ := make_ga i1 i3 i5 i7
  have ei : i.val = 4 * j.val := by rw [mul_ok hi]; simp
  rw [ψa, g0, g1, g2, g3, Alimb, idx_z' hi1, idx_z' hi3, idx_z' hi5, idx_z' hi7, add_ok hi2,
    add_ok hi4, add_ok hi6, ei]
  simp

/-- `succCarry` on `ℕ`-indexed coordinates. -/
def scK (A : ℕ → K) (n : ℕ) : K := ∏ k ∈ Finset.range n, A (9 - k)

theorem scarry_spec (hT : Tower B) {al : Slice U32} {n : Usize} {z : A4}
    (h : R1CertBuild.scarry al n = ok z) : ψa B φ z = scK (Alimb B φ al) n.val := by
  unfold R1CertBuild.scarry at h
  obtain ⟨one, hone, h⟩ := bind_eq_ok h
  have e := mul_loopG (ψa B φ) (G := fun acc k => R1CertBuild.scarry_loop al n acc k) (n := n.val)
    (T := fun k => Alimb B φ al (9 - k))
    (fun a k hk => by rw [R1CertBuild.scarry_loop, if_neg (by rw [UScalar.lt_equiv]; exact hk)])
    (fun a k r hk h => by
      rw [R1CertBuild.scarry_loop, if_pos (by rw [UScalar.lt_equiv]; exact hk)] at h
      obtain ⟨i, hi, h⟩ := bind_eq_ok h
      obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
      obtain ⟨acc1, hacc, h⟩ := bind_eq_ok h
      obtain ⟨k1, hk1, h⟩ := bind_eq_ok h
      refine ⟨acc1, k1, add_ok hk1, h, ?_⟩
      rw [psi_qmul B φ hT hacc, aget_spec B φ ha1, (sub_ok hi).1]
      simp)
    n.val one 0#usize z (by simp) h
  rw [e, qone_spec B φ hone, mul_one, scK]
  simp

/-- Coordinate `c` of opening point `g` (`rustPoints`). -/
def pcK (A : ℕ → K) (g c : ℕ) : K :=
  if g = 0 then A c
  else if g = 1 then A c + scK A (9 - c) - (A c * scK A (9 - c) + A c * scK A (9 - c))
  else if c = 7 ∨ c = 6 then 1 - A c else A c

theorem ueq {x : Usize} {n : ℕ} {lit : Usize} (hl : lit.val = n) : x = lit ↔ x.val = n := by
  rw [UScalar.eq_equiv, hl]

theorem point_coord_spec (hT : Tower B) {al : Slice U32} {g c : Usize} {z : A4}
    (h : R1CertBuild.point_coord al g c = ok z) : ψa B φ z = pcK (Alimb B φ al) g.val c.val := by
  unfold R1CertBuild.point_coord at h
  unfold pcK
  by_cases g0 : g.val = 0
  · rw [if_pos ((ueq (by simp)).2 g0)] at h
    rw [if_pos g0, aget_spec B φ h]
  · rw [if_neg (fun h' => g0 ((ueq (by simp)).1 h'))] at h
    rw [if_neg g0]
    by_cases g1 : g.val = 1
    · rw [if_pos ((ueq (by simp)).2 g1)] at h
      rw [if_pos g1]
      obtain ⟨p, hp, h⟩ := bind_eq_ok h
      obtain ⟨i, hi, h⟩ := bind_eq_ok h
      obtain ⟨cr, hcr, h⟩ := bind_eq_ok h
      obtain ⟨a, ha, h⟩ := bind_eq_ok h
      obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
      obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
      rw [psi_qsub B φ h, psi_qadd B φ ha, psi_qadd B φ ha2, psi_qmul B φ hT ha1, aget_spec B φ hp,
        scarry_spec B φ hT hcr, (sub_ok hi).1]
      simp
    · rw [if_neg (fun h' => g1 ((ueq (by simp)).1 h'))] at h
      rw [if_neg g1]
      by_cases c7 : c.val = 7
      · rw [if_pos ((ueq (by simp)).2 c7)] at h
        rw [if_pos (Or.inl c7)]
        obtain ⟨a, ha, h⟩ := bind_eq_ok h
        obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
        rw [psi_qsub B φ h, qone_spec B φ ha, aget_spec B φ ha1]
      · rw [if_neg (fun h' => c7 ((ueq (by simp)).1 h'))] at h
        by_cases c6 : c.val = 6
        · rw [if_pos ((ueq (by simp)).2 c6)] at h
          rw [if_pos (Or.inr c6)]
          obtain ⟨a, ha, h⟩ := bind_eq_ok h
          obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
          rw [psi_qsub B φ h, qone_spec B φ ha, aget_spec B φ ha1]
        · rw [if_neg (fun h' => c6 ((ueq (by simp)).1 h'))] at h
          rw [if_neg (fun h' => h'.elim c7 c6), aget_spec B φ h]

/-- The eq weight of point `g` at row `r` (z4/probe.rs `eq`). -/
def eqK (A : ℕ → K) (g r : ℕ) : K :=
  ∏ i ∈ Finset.range 10, ((1 - pcK A g i) + (((r / 2 ^ (9 - i)) % 2 : ℕ) : K) * (pcK A g i + pcK A g i - 1))

theorem aidx_ok' {n : Usize} {x : Array Usize n} {i : Usize} {v : Usize}
    (h : Array.index_usize x i = ok v) : v = x.val[i.val]! := by
  unfold Array.index_usize at h
  rw [Array.getElem?_Usize_eq] at h
  cases hc : x.val[i.val]? with
  | none => rw [hc] at h; cases h
  | some y =>
    rw [hc] at h
    cases h
    rw [List.getElem!_eq_getElem?_getD, hc]
    rfl

theorem P2_get {i : Usize} {v : Usize} (hi : i.val < 10) (h : Array.index_usize R1CertBuild.P2 i = ok v) :
    v.val = 2 ^ (9 - i.val) := by
  rw [aidx_ok' h]
  unfold R1CertBuild.P2
  rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨
    i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9) with e | e | e | e | e | e | e | e | e | e <;>
    simp [e, Array.make]

theorem castU32 (x : Usize) (h : x.val < 2 ^ 32) : (UScalar.cast .U32 x).val = x.val := by
  rw [UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (by simpa using h)

/-- The natural value of a slice entry. -/
def gN (s : Slice U32) (k : ℕ) : ℕ := (s.val[k]!).val

theorem embR_nat (n : ℕ) : embR (K := K) φ (n : ZP) = (n : K) := map_natCast _ n

theorem eqw_spec (hT : Tower B) {al : Slice U32} {g r : Usize} {z : A4}
    (h : R1CertBuild.eqw al g r = ok z) : ψa B φ z = eqK (Alimb B φ al) g.val r.val := by
  unfold R1CertBuild.eqw at h
  obtain ⟨one, hone, h⟩ := bind_eq_ok h
  have h1 := qone_spec B φ hone
  have e := mul_loopG (ψa B φ) (G := fun acc1 i => R1CertBuild.eqw_loop one al g r acc1 i)
    (n := 10) (T := fun i => (1 - pcK (Alimb B φ al) g.val i) +
      (((r.val / 2 ^ (9 - i)) % 2 : ℕ) : K) * (pcK (Alimb B φ al) g.val i + pcK (Alimb B φ al) g.val i - 1))
    (fun a i hi => by rw [R1CertBuild.eqw_loop, if_neg (by rw [UScalar.lt_equiv]; simpa using hi)])
    (fun a i res hi h => by
      rw [R1CertBuild.eqw_loop, if_pos (by rw [UScalar.lt_equiv]; simpa using hi)] at h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
      obtain ⟨bit, hbit, h⟩ := bind_eq_ok h
      obtain ⟨p, hp, h⟩ := bind_eq_ok h
      obtain ⟨a0, ha0, h⟩ := bind_eq_ok h
      obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
      obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
      obtain ⟨a3, ha3, h⟩ := bind_eq_ok h
      obtain ⟨a4, ha4, h⟩ := bind_eq_ok h
      obtain ⟨f, hf, h⟩ := bind_eq_ok h
      obtain ⟨acc2, hacc, h⟩ := bind_eq_ok h
      obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
      refine ⟨acc2, i4, add_ok hi4, h, ?_⟩
      have hp2 := P2_get (by simpa using hi) hi1
      have hne : i1.val ≠ 0 := by rw [hp2]; positivity
      have e2 : i2.val = r.val / i1.val := div_ok hne hi2
      have two : (2#usize : Usize).val ≠ 0 := by simp
      have e3 : i3.val = i2.val % (2#usize : Usize).val := rem_ok two hi3
      have i3v : i3.val = r.val / 2 ^ (9 - i.val) % 2 := by rw [e3, e2, hp2]; simp
      have hb : bit.val = r.val / 2 ^ (9 - i.val) % 2 := by
        rw [(ok_inj hbit).symm, castU32 i3 (by rw [i3v]; omega), i3v]
      rw [psi_qmul B φ hT hacc, psi_qadd B φ hf, psi_qsub B φ ha0, psi_qmul B φ hT ha4,
        (qbase_spec B φ ha1).1, psi_qsub B φ ha3, psi_qadd B φ ha2, h1, point_coord_spec B φ hT hp, hb,
        embR_nat]
      ring)
    10 one 0#usize z (by simp) h
  rw [e, h1, mul_one, eqK]
  simp

theorem qpow_spec (hT : Tower B) {x : A4} {e : Usize} {z : A4} (h : R1CertBuild.qpow x e = ok z) :
    ψa B φ z = ψa B φ x ^ e.val := by
  unfold R1CertBuild.qpow at h
  obtain ⟨one, hone, h⟩ := bind_eq_ok h
  have E := horner_loopG (ψa B φ) (ψa B φ x) (G := fun acc t => R1CertBuild.qpow_loop x e acc t)
    (n := e.val) (T := fun _ => 0)
    (fun a t ht => by rw [R1CertBuild.qpow_loop, if_neg (by rw [UScalar.lt_equiv]; exact ht)])
    (fun a t res ht h => by
      rw [R1CertBuild.qpow_loop, if_pos (by rw [UScalar.lt_equiv]; exact ht)] at h
      obtain ⟨acc1, hacc, h⟩ := bind_eq_ok h
      obtain ⟨t1, ht1, h⟩ := bind_eq_ok h
      exact ⟨acc1, t1, add_ok ht1, h, by rw [psi_qmul B φ hT hacc, add_zero]⟩)
    e.val one 0#usize z (by simp) h
  rw [E, qone_spec B φ hone]
  simp

/-- `h_weight`. -/
def hwK (A : ℕ → K) (co : ℕ) : K := if co < 28 then A 8 ^ co else if co < 56 then A 9 ^ (co - 28) else 0

theorem hw_spec (hT : Tower B) {al : Slice U32} {co : Usize} {z : A4} (h : R1CertBuild.hw al co = ok z) :
    ψa B φ z = hwK (Alimb B φ al) co.val := by
  unfold R1CertBuild.hw at h
  unfold hwK
  by_cases c1 : co.val < 28
  · rw [if_pos (by rw [UScalar.lt_equiv]; simpa using c1)] at h
    rw [if_pos c1]
    obtain ⟨a, ha, h⟩ := bind_eq_ok h
    rw [qpow_spec B φ hT h, aget_spec B φ ha]
    simp
  · rw [if_neg (by rw [UScalar.lt_equiv]; simpa using c1)] at h
    rw [if_neg c1]
    by_cases c2 : co.val < 56
    · rw [if_pos (by rw [UScalar.lt_equiv]; simpa using c2)] at h
      rw [if_pos c2]
      obtain ⟨a, ha, h⟩ := bind_eq_ok h
      obtain ⟨i, hi, h⟩ := bind_eq_ok h
      rw [qpow_spec B φ hT h, aget_spec B φ ha, (sub_ok hi).1]
      simp
    · rw [if_neg (by rw [UScalar.lt_equiv]; simpa using c2)] at h
      rw [if_neg c2, ← ok_inj h, psi_zero]

/-- The natural-basis evaluation, bit by bit (`basis.rs` `natural`, 10 bits). -/
def natR (x : K) (m : ℕ) : ℕ → K
  | 0 => 1
  | k + 1 => (1 + ((m % 2 : ℕ) : K) * (x - 1)) * natR (x * x + x * x - 1) (m / 2) k

theorem nat_loop_spec (hT : Tower B) :
    ∀ (k : ℕ) (out f : A4) (m b : Usize) (z : A4), b.val + k = 10 →
      R1CertBuild.nat_loop_loop out f m b = ok z →
      ψa B φ z = ψa B φ out * natR (ψa B φ f) m.val k
  | 0, out, f, m, b, z, hk, h => by
      rw [R1CertBuild.nat_loop_loop, if_neg (by rw [UScalar.lt_equiv]; simp; omega)] at h
      rw [← ok_inj h, natR, mul_one]
  | k + 1, out, f, m, b, z, hk, h => by
      rw [R1CertBuild.nat_loop_loop, if_pos (by rw [UScalar.lt_equiv]; simp; omega)] at h
      obtain ⟨i, hi, h⟩ := bind_eq_ok h
      obtain ⟨bit, hbit, h⟩ := bind_eq_ok h
      obtain ⟨a, ha, h⟩ := bind_eq_ok h
      obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
      obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
      obtain ⟨a3, ha3, h⟩ := bind_eq_ok h
      obtain ⟨a4, ha4, h⟩ := bind_eq_ok h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok h
      obtain ⟨a5, ha5, h⟩ := bind_eq_ok h
      obtain ⟨a6, ha6, h⟩ := bind_eq_ok h
      obtain ⟨f1, hf1, h⟩ := bind_eq_ok h
      obtain ⟨m1, hm1, h⟩ := bind_eq_ok h
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok h
      have IH := nat_loop_spec hT k out1 f1 m1 b1 z (by rw [add_ok hb1]; simp; omega) h
      have two : (2#usize : Usize).val ≠ 0 := by simp
      have ei : i.val = m.val % 2 := by rw [rem_ok two hi]; simp
      have hb : bit.val = m.val % 2 := by
        rw [(ok_inj hbit).symm, castU32 i (by rw [ei]; omega), ei]
      have hm : m1.val = m.val / 2 := by rw [div_ok two hm1]; simp
      have ea := qone_spec B φ ha
      rw [IH, psi_qmul B φ hT hout1, psi_qadd B φ ha4, psi_qmul B φ hT ha3, (qbase_spec B φ ha1).1,
        psi_qsub B φ ha2, psi_qsub B φ hf1, psi_qadd B φ ha6, psi_qmul B φ hT ha5, ea, hb, hm, embR_nat,
        natR]
      ring

theorem nat_q_spec (hT : Tower B) {n : Usize} {x z : A4} (h : R1CertBuild.nat_q n x = ok z) :
    ψa B φ z = natR (ψa B φ x) n.val 10 := by
  unfold R1CertBuild.nat_q at h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  rw [nat_loop_spec B φ hT 10 a x n 0#usize z (by simp) h, qone_spec B φ ha, one_mul]

/-- `evalrow(co, (x, y))`. -/
def evK (x y : K) (co : ℕ) : K := if co % 2 = 0 then natR x (co / 2) 10 else natR x (co / 2) 10 * y

theorem evq_spec (hT : Tower B) {co : Usize} {x y z : A4} (h : R1CertBuild.evq co x y = ok z) :
    ψa B φ z = evK (ψa B φ x) (ψa B φ y) co.val := by
  unfold R1CertBuild.evq at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨v, hv, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  have two : (2#usize : Usize).val ≠ 0 := by simp
  have ei : i.val = co.val / 2 := by rw [div_ok two hi]; simp
  have ei1 : i1.val = co.val % 2 := by rw [rem_ok two hi1]; simp
  unfold evK
  by_cases e0 : co.val % 2 = 0
  · rw [if_pos ((ueq (lit := 0#usize) (n := 0) (by simp)).2 (by rw [ei1]; exact e0))] at h
    rw [if_pos e0, ← ok_inj h, nat_q_spec B φ hT hv, ei]
  · rw [if_neg (fun h' => e0 (by rw [← ei1]; exact (ueq (lit := 0#usize) (n := 0) (by simp)).1 h'))] at h
    rw [if_neg e0, psi_qmul B φ hT h, nat_q_spec B φ hT hv, ei]

/-- The six head values of row `r` (claims `g < 3`, extra `g = 3`, OOD `g = 4, 5`). -/
def headK (A Z : ℕ → K) (co r g : ℕ) : K :=
  if g < 3 then eqK A g r else if g = 3 then hwK A co else evK (Z (2 * (g - 4))) (Z (2 * (g - 4) + 1)) co

theorem head_q_spec (hT : Tower B) {al zz tr : Slice U32} {r g : Usize} {z : A4}
    (h : R1CertBuild.head_q al zz tr r g = ok z) :
    ψa B φ z = headK (Alimb B φ al) (Alimb B φ zz) (gN tr r.val) r.val g.val := by
  unfold R1CertBuild.head_q at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨co, hco, h⟩ := bind_eq_ok h
  have eco : co.val = gN tr r.val := by rw [(ok_inj hco).symm, castUs, (index_ok hi).2]; rfl
  unfold headK
  by_cases g3 : g.val < 3
  · rw [if_pos (by rw [UScalar.lt_equiv]; simpa using g3)] at h
    rw [if_pos g3, eqw_spec B φ hT h]
  · rw [if_neg (by rw [UScalar.lt_equiv]; simpa using g3)] at h
    rw [if_neg g3]
    by_cases g4 : g.val = 3
    · rw [if_pos ((ueq (by simp)).2 g4)] at h
      rw [if_pos g4, hw_spec B φ hT h, eco]
    · rw [if_neg (fun h' => g4 ((ueq (by simp)).1 h'))] at h
      rw [if_neg g4]
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
      obtain ⟨a, ha, h⟩ := bind_eq_ok h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
      obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
      obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
      rw [evq_spec B φ hT h, aget_spec B φ ha, aget_spec B φ ha1, add_ok hi4, mul_ok hi3, mul_ok hi2,
        (sub_ok hi1).1, eco]
      simp

#print axioms scarry_spec
#print axioms point_coord_spec
#print axioms eqw_spec
#print axioms hw_spec
#print axioms nat_q_spec
#print axioms evq_spec
#print axioms head_q_spec

end R1Z.CertBuild
