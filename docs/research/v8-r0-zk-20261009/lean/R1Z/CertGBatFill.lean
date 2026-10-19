import R1Z.CertRoundFill
import R1Z.CertRelFill
import R1Z.CertGBatK

/-! D72.2 (hGBent): the extracted G batched-column writer `fill_gbat` (c3/build builder 6)
fills `pb.gbat` with the CertGBatK model `gbatP`: cell `c` of column `t` is eight WideExact
limbs whose reading in the limb basis `wb` (`wb k = wbP i u w k`) is
`gbatP … (srow t) (slimb t) c`, the stored first-line points being the input limbs `x18`.
The unit-functional cells reuse the builder-4 specifications (`wt_spec`, `df1_spec`,
`nat_loop_spec`); every loop is the generic `acc_loopG` invariant or a structural induction
on the remaining iterations.  Aeneas side only. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertBuild
open Aeneas Aeneas.Std Result R1Z.CertCheck R0P R1Z.CertRel
open scoped BigOperators

variable {K : Type} [Field K] {F : Subfield K} (B : PackBasis F) (φ : ZP →+* ↥F) (w : K)

theorem u27 : (27#usize : Usize).val = 27 := by simp

theorem u0term_spec (hT : Tower B) (hW : w * w = B.u) {al zz tr inact ti op : Slice U32} {co c t : Usize}
    {z : A8} (h : R1CertBuild.u0term al zz tr inact ti op co c t = ok z) :
    ψ8 B φ w z = if co.val % 4 + (4 - t.val) % 4 = c.val then
      wtK B φ w al zz tr inact ti op (4 * (co.val / 4) + t.val) else 0 := by
  unfold R1CertBuild.u0term at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  have e3 : i3.val = co.val % 4 + (4 - t.val) % 4 := by
    rw [add_ok hi3, rem_ok (by simp) hi, rem_ok (by simp) hi2, (sub_ok hi1).1]; simp
  by_cases ec : co.val % 4 + (4 - t.val) % 4 = c.val
  · rw [if_pos (by rw [UScalar.eq_equiv, e3]; exact ec)] at h
    obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
    obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
    obtain ⟨i6, hi6, h⟩ := bind_eq_ok h
    have e6 : i6.val = 4 * (co.val / 4) + t.val := by
      rw [add_ok hi6, mul_ok hi5, div_ok (by simp) hi4]; simp
    rw [if_pos ec, wt_spec B φ w hT hW h, e6]
  · rw [if_neg (by rw [UScalar.eq_equiv, e3]; exact ec)] at h
    rw [if_neg ec, psi_wzero B φ w h]

theorem ucell_r0_spec (hT : Tower B) (hW : w * w = B.u) {al zz tr inact ti op : Slice U32} {co c : Usize}
    {z : A8} (h : R1CertBuild.ucell_r0 al zz tr inact ti op co c = ok z) :
    ψ8 B φ w z = ∑ t ∈ Finset.range 4, (if co.val % 4 + (4 - t) % 4 = c.val then
      wtK B φ w al zz tr inact ti op (4 * (co.val / 4) + t) else 0) := by
  unfold R1CertBuild.ucell_r0 at h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  have E := acc_loopG (ψ8 B φ w) (G := fun acc t => R1CertBuild.ucell_r0_loop al zz tr inact ti op co c acc t)
    (n := 4) (T := fun t => if co.val % 4 + (4 - t) % 4 = c.val then
      wtK B φ w al zz tr inact ti op (4 * (co.val / 4) + t) else 0)
    (fun x t ht => by rw [R1CertBuild.ucell_r0_loop, if_neg (by rw [UScalar.lt_equiv]; simpa using ht)])
    (fun x t res ht h => by
      rw [R1CertBuild.ucell_r0_loop, if_pos (by rw [UScalar.lt_equiv]; simpa using ht)] at h
      obtain ⟨v, hv, h⟩ := bind_eq_ok h
      obtain ⟨acc1, hacc1, h⟩ := bind_eq_ok h
      obtain ⟨t1, ht1, h⟩ := bind_eq_ok h
      exact ⟨acc1, t1, add_ok ht1, h, by rw [psi_wadd B φ w hacc1, u0term_spec B φ w hT hW hv]⟩)
    4 a 0#usize z (by simp) h
  rw [E, psi_wzero B φ w ha, zero_add]
  simp only [u0', Finset.range_eq_Ico]

theorem u1term_spec (hT : Tower B) (hW : w * w = B.u) {al zz tr inact ti op : Slice U32} {co c t : Usize}
    {z : A8} (h : R1CertBuild.u1term al zz tr inact ti op co c t = ok z) :
    ψ8 B φ w z = if co.val / 4 % 4 + (4 - t.val) % 4 = c.val - 7 then
      w1K B φ w al zz tr inact ti op (4 * (co.val / 16) + t.val) else 0 := by
  unfold R1CertBuild.u1term at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
  have e4 : i4.val = co.val / 4 % 4 + (4 - t.val) % 4 := by
    rw [add_ok hi4, rem_ok (by simp) hi1, div_ok (by simp) hi, rem_ok (by simp) hi3, (sub_ok hi2).1]; simp
  have e5 : i5.val = c.val - 7 := by rw [(sub_ok hi5).1]; simp
  by_cases ec : co.val / 4 % 4 + (4 - t.val) % 4 = c.val - 7
  · rw [if_pos (by rw [UScalar.eq_equiv, e4, e5]; exact ec)] at h
    obtain ⟨i6, hi6, h⟩ := bind_eq_ok h
    obtain ⟨i7, hi7, h⟩ := bind_eq_ok h
    obtain ⟨i8, hi8, h⟩ := bind_eq_ok h
    have e8 : i8.val = 4 * (co.val / 16) + t.val := by
      rw [add_ok hi8, mul_ok hi7, div_ok (by simp) hi6]; simp
    rw [if_pos ec, df1_spec B φ w hT hW h, e8]
  · rw [if_neg (by rw [UScalar.eq_equiv, e4, e5]; exact ec)] at h
    rw [if_neg ec, psi_wzero B φ w h]

theorem ucell_r1_spec (hT : Tower B) (hW : w * w = B.u) {al zz tr inact ti op : Slice U32} {co c : Usize}
    {z : A8} (h : R1CertBuild.ucell_r1 al zz tr inact ti op co c = ok z) :
    ψ8 B φ w z = ∑ t ∈ Finset.range 4, (if co.val / 4 % 4 + (4 - t) % 4 = c.val - 7 then
      w1K B φ w al zz tr inact ti op (4 * (co.val / 16) + t) else 0) := by
  unfold R1CertBuild.ucell_r1 at h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  have E := acc_loopG (ψ8 B φ w) (G := fun acc t => R1CertBuild.ucell_r1_loop al zz tr inact ti op co c acc t)
    (n := 4) (T := fun t => if co.val / 4 % 4 + (4 - t) % 4 = c.val - 7 then
      w1K B φ w al zz tr inact ti op (4 * (co.val / 16) + t) else 0)
    (fun x t ht => by rw [R1CertBuild.ucell_r1_loop, if_neg (by rw [UScalar.lt_equiv]; simpa using ht)])
    (fun x t res ht h => by
      rw [R1CertBuild.ucell_r1_loop, if_pos (by rw [UScalar.lt_equiv]; simpa using ht)] at h
      obtain ⟨v, hv, h⟩ := bind_eq_ok h
      obtain ⟨acc1, hacc1, h⟩ := bind_eq_ok h
      obtain ⟨t1, ht1, h⟩ := bind_eq_ok h
      exact ⟨acc1, t1, add_ok ht1, h, by rw [psi_wadd B φ w hacc1, u1term_spec B φ w hT hW hv]⟩)
    4 a 0#usize z (by simp) h
  rw [E, psi_wzero B φ w ha, zero_add]
  simp only [u0', Finset.range_eq_Ico]

/-- Cell `c` of the unit functional at natural coefficient `co`: the CertGBatK `ucellP`. -/
theorem ucell_spec (hT : Tower B) (hW : w * w = B.u) {al zz tr inact ti op x18 : Slice U32} {nf co c : Usize}
    {z : A8} (h : R1CertBuild.ucell al zz tr inact ti op x18 nf co c = ok z) :
    ψ8 B φ w z = ucellP (Alimb B φ al) (Alimb B φ zz) (gN tr) (gN ti) (flK φ inact) (Wl B φ w op 1)
      (Wl B φ w op 2) (Wl B φ w op 3) (embR φ 536870912) (fun m => embR φ (gs x18 m)) nf.val co.val c.val := by
  unfold R1CertBuild.ucell at h
  obtain ⟨q, hq, h⟩ := bind_eq_ok h
  obtain ⟨a0, ha0, h⟩ := bind_eq_ok h
  have eq4 := wq_quarter B φ w hq
  have e0 : ψ8 B φ w a0 = Wl B φ w op 2 := by rw [psi_wget B φ w ha0, u2']
  unfold ucellP
  by_cases c7 : c.val < 7
  · rw [if_pos (by rw [UScalar.lt_equiv]; simpa using c7)] at h
    obtain ⟨a, ha, h⟩ := bind_eq_ok h
    rw [if_pos c7, psi_wmul B φ w hT hW h, eq4, ucell_r0_spec B φ w hT hW ha]
  · rw [if_neg (by rw [UScalar.lt_equiv]; simpa using c7)] at h
    rw [if_neg c7]
    by_cases c14 : c.val < 14
    · rw [if_pos (by rw [UScalar.lt_equiv]; simpa using c14)] at h
      obtain ⟨i, hi, h⟩ := bind_eq_ok h
      obtain ⟨a, ha, h⟩ := bind_eq_ok h
      obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
      obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
      rw [if_pos c14, psi_wmul B φ w hT hW h, psi_wpow B φ w hT hW ha, e0, rem_ok (by simp) hi, u4',
        psi_wmul B φ w hT hW ha2, eq4, ucell_r1_spec B φ w hT hW ha1]
    · rw [if_neg (by rw [UScalar.lt_equiv]; simpa using c14)] at h
      rw [if_neg c14]
      obtain ⟨i, hi, h⟩ := bind_eq_ok h
      have ei : i.val = 14 + nf.val := by rw [add_ok hi]; simp
      by_cases cn : c.val < 14 + nf.val
      · rw [if_pos (by rw [UScalar.lt_equiv, ei]; exact cn)] at h
        rw [if_pos cn]
        obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
        obtain ⟨a, ha, h⟩ := bind_eq_ok h
        obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
        obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
        obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
        obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
        obtain ⟨a3, ha3, h⟩ := bind_eq_ok h
        obtain ⟨a4, ha4, h⟩ := bind_eq_ok h
        have e2 : i2.val = c.val - 14 := by rw [(sub_ok hi2).1]; simp
        have e4 : i4.val = co.val / 4 := by rw [div_ok (by simp) hi4]; simp
        rw [psi_wmul B φ w hT hW h, psi_wpow B φ w hT hW ha, e0, rem_ok (by simp) hi1, u4', psi_wq B φ w ha4,
          nat_loop_spec B φ hT 8 a1 a2 i4 2#usize a3 (by simp) ha3, qone_spec B φ ha1, one_mul,
          (qbase_spec B φ ha2).1, idx_z' hi3, e2, e4, natR_P]
      · rw [if_neg (by rw [UScalar.lt_equiv, ei]; exact cn)] at h
        rw [if_neg cn]
        obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
        have e1 : i1.val = c.val - (14 + nf.val) := by rw [(sub_ok hi1).1, ei]
        have e2 : i2.val = co.val / 16 := by rw [div_ok (by simp) hi2]; simp
        by_cases ef : c.val - (14 + nf.val) = co.val / 16
        · rw [if_pos (by rw [UScalar.eq_equiv, e1, e2]; exact ef)] at h
          rw [if_pos ef]
          obtain ⟨a, ha, h⟩ := bind_eq_ok h
          obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
          obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
          obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
          obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
          obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
          have e4 : i4.val = co.val / 4 % 4 := by rw [rem_ok (by simp) hi4, div_ok (by simp) hi3]; simp
          have e5 : i5.val = co.val % 4 := by rw [rem_ok (by simp) hi5]; simp
          rw [psi_wmul B φ w hT hW h, psi_wpow B φ w hT hW ha1, psi_wpow B φ w hT hW ha2, psi_wget B φ w ha, e0,
            u3', e4, e5]
        · rw [if_neg (by rw [UScalar.eq_equiv, e1, e2]; exact ef)] at h
          rw [if_neg ef, psi_wzero B φ w h]

/-- Cell `c` of the G batched column at row `r`, tower limb `k`: the CertGBatK `gbatP`. -/
theorem gbat_cell_spec (hT : Tower B) (hW : w * w = B.u) {al zz tr inact ti op x18 : Slice U32}
    {nf r k c : Usize} {z : A8} (h : R1CertBuild.gbat_cell al zz tr inact ti op x18 nf r k c = ok z) :
    ψ8 B φ w z = gbatP (Alimb B φ al) (Alimb B φ zz) (gN tr) (gN ti) (flK φ inact) (Wl B φ w op 0)
      (Wl B φ w op 1) (Wl B φ w op 2) (Wl B φ w op 3) (embR φ 536870912) B.i B.u (fun m => embR φ (gs x18 m))
      nf.val r.val k.val c.val := by
  unfold R1CertBuild.gbat_cell at h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
  obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
  obtain ⟨a3, ha3, h⟩ := bind_eq_ok h
  obtain ⟨g, hg, h⟩ := bind_eq_ok h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨u0, hu0, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  obtain ⟨u1, hu1, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  obtain ⟨a4, ha4, h⟩ := bind_eq_ok h
  obtain ⟨a5, ha5, h⟩ := bind_eq_ok h
  obtain ⟨a6, ha6, h⟩ := bind_eq_ok h
  have e1 : i1.val = gN tr r.val := by rw [(ok_inj hi1).symm, castUs, (index_ok hi).2]; rfl
  have e3 : i3.val = gN tr 0 := by rw [(ok_inj hi3).symm, castUs, (index_ok hi2).2, u0']; rfl
  rw [psi_wmul B φ w hT hW h, psi_wmul B φ w hT hW hg, psi_wpow B φ w hT hW ha1, psi_wget B φ w ha, u0', u27,
    psi_wq B φ w ha3, tbq_spec B φ ha2, psi_wsub B φ w ha6, psi_wmul B φ w hT hW ha5, psi_wbase B φ w ha4,
    idx_z' hi4, ucell_spec B φ w hT hW hu0, ucell_spec B φ w hT hW hu1, e1, e3, gbatP]
  rfl

/-! ### The column loops -/

theorem push8 {o0 o1 o2 o3 o4 o5 o6 o7 o8 : alloc.vec.Vec U32} {x0 x1 x2 x3 x4 x5 x6 x7 : U32}
    (h1 : alloc.vec.Vec.push o0 x0 = ok o1) (h2 : alloc.vec.Vec.push o1 x1 = ok o2)
    (h3 : alloc.vec.Vec.push o2 x2 = ok o3) (h4 : alloc.vec.Vec.push o3 x3 = ok o4)
    (h5 : alloc.vec.Vec.push o4 x4 = ok o5) (h6 : alloc.vec.Vec.push o5 x5 = ok o6)
    (h7 : alloc.vec.Vec.push o6 x6 = ok o7) (h8 : alloc.vec.Vec.push o7 x7 = ok o8) :
    o8.val = o0.val ++ [x0, x1, x2, x3, x4, x5, x6, x7] := by
  rw [push_ok h8, push_ok h7, push_ok h6, push_ok h5, push_ok h4, push_ok h3, push_ok h2, push_ok h1]
  simp

theorem getAppL (l m : List U32) (i : ℕ) (hi : i < l.length) : (l ++ m)[i]! = l[i]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getAppR (l m : List U32) (i : ℕ) (hi : i < m.length) : (l ++ m)[l.length + i]! = m[i]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left]

variable (al zz tr inact ti op x18 srow slimb : Slice U32)

theorem gbat_col_spec (nf r k : Usize) :
    ∀ (m : ℕ) (out : alloc.vec.Vec U32) (c : Usize) (res : alloc.vec.Vec U32), c.val + m = 78 + nf.val →
      R1CertBuild.gbat_col_loop al zz tr inact ti op x18 nf r k out c = ok res →
      res.val.length = out.val.length + 8 * m ∧ (∀ y, y < out.val.length → res.val[y]! = out.val[y]!) ∧
        ∀ s, c.val ≤ s → s < 78 + nf.val → ∃ (cc : Usize) (v : A8), cc.val = s ∧
          R1CertBuild.gbat_cell al zz tr inact ti op x18 nf r k cc = ok v ∧
          ∀ l, l < 8 → res.val[out.val.length + 8 * (s - c.val) + l]! = v.val[l]!
  | 0, out, c, res, hm, h => by
      rw [R1CertBuild.gbat_col_loop] at h
      obtain ⟨i, hi, h⟩ := bind_eq_ok h
      have ei : i.val = 78 + nf.val := by rw [add_ok hi]; simp
      rw [if_neg (by rw [UScalar.lt_equiv, ei]; omega)] at h
      rw [← ok_inj h]
      exact ⟨by simp, fun y _ => rfl, fun s h1 h2 => by omega⟩
  | m + 1, out, c, res, hm, h => by
      rw [R1CertBuild.gbat_col_loop] at h
      obtain ⟨i, hi, h⟩ := bind_eq_ok h
      have ei : i.val = 78 + nf.val := by rw [add_ok hi]; simp
      rw [if_pos (by rw [UScalar.lt_equiv, ei]; omega)] at h
      obtain ⟨v, hv, h⟩ := bind_eq_ok h
      obtain ⟨x0, hx0, h⟩ := bind_eq_ok h
      obtain ⟨o1, ho1, h⟩ := bind_eq_ok h
      obtain ⟨x1, hx1, h⟩ := bind_eq_ok h
      obtain ⟨o2, ho2, h⟩ := bind_eq_ok h
      obtain ⟨x2, hx2, h⟩ := bind_eq_ok h
      obtain ⟨o3, ho3, h⟩ := bind_eq_ok h
      obtain ⟨x3, hx3, h⟩ := bind_eq_ok h
      obtain ⟨o4, ho4, h⟩ := bind_eq_ok h
      obtain ⟨x4, hx4, h⟩ := bind_eq_ok h
      obtain ⟨o5, ho5, h⟩ := bind_eq_ok h
      obtain ⟨x5, hx5, h⟩ := bind_eq_ok h
      obtain ⟨o6, ho6, h⟩ := bind_eq_ok h
      obtain ⟨x6, hx6, h⟩ := bind_eq_ok h
      obtain ⟨o7, ho7, h⟩ := bind_eq_ok h
      obtain ⟨x7, hx7, h⟩ := bind_eq_ok h
      obtain ⟨o8, ho8, h⟩ := bind_eq_ok h
      obtain ⟨c1, hc1, h⟩ := bind_eq_ok h
      have hc1v : c1.val = c.val + 1 := by rw [add_ok hc1]; simp
      have eo := push8 ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8
      have hlen : o8.val.length = out.val.length + 8 := by rw [eo]; simp
      obtain ⟨L, P1, P2⟩ := gbat_col_spec nf r k m o8 c1 res (by omega) h
      refine ⟨by rw [L, hlen]; ring, fun y hy => by rw [P1 y (by omega), eo, getAppL _ _ _ hy],
        fun s h1 h2 => ?_⟩
      by_cases es : s = c.val
      · subst es
        refine ⟨c, v, rfl, hv, fun l hl => ?_⟩
        rw [Nat.sub_self, mul_zero, add_zero, P1 _ (by omega), eo, getAppR _ _ _ (by simp; omega)]
        obtain rfl := aidxN hx0
        obtain rfl := aidxN hx1
        obtain rfl := aidxN hx2
        obtain rfl := aidxN hx3
        obtain rfl := aidxN hx4
        obtain rfl := aidxN hx5
        obtain rfl := aidxN hx6
        obtain rfl := aidxN hx7
        rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5 ∨ l = 6 ∨ l = 7) with
          e | e | e | e | e | e | e | e <;> subst e <;> simp
      · obtain ⟨cc, vv, hcc, hvv, hl⟩ := P2 s (by omega) h2
        refine ⟨cc, vv, hcc, hvv, fun l hl' => ?_⟩
        have := hl l hl'
        rw [hlen, hc1v, show out.val.length + 8 + 8 * (s - (c.val + 1)) + l =
          out.val.length + 8 * (s - c.val) + l by omega] at this
        exact this

/-- Cell `c` of G batched column `t` comes from `gbat_cell` on source `t`'s row and limb. -/
def GBatAt (nf : Usize) (t c : ℕ) (v : A8) : Prop :=
  ∃ rr kk cc : Usize, rr.val = gNL srow t ∧ kk.val = gNL slimb t ∧ cc.val = c ∧
    R1CertBuild.gbat_cell al zz tr inact ti op x18 nf rr kk cc = ok v

theorem fill_gbat_loop_spec (n nf : Usize) :
    ∀ (m : ℕ) (out : alloc.vec.Vec U32) (t : Usize) (res : alloc.vec.Vec U32), t.val + m = n.val →
      R1CertBuild.fill_gbat_loop al zz tr inact ti op x18 srow slimb n nf out t = ok res →
      res.val.length = out.val.length + m * (8 * (78 + nf.val)) ∧
        (∀ y, y < out.val.length → res.val[y]! = out.val[y]!) ∧
        ∀ t', t.val ≤ t' → t' < n.val → ∀ c, c < 78 + nf.val → ∃ v : A8,
          GBatAt al zz tr inact ti op x18 srow slimb nf t' c v ∧
          ∀ l, l < 8 → res.val[out.val.length + (t' - t.val) * (8 * (78 + nf.val)) + (8 * c + l)]! = v.val[l]!
  | 0, out, t, res, hm, h => by
      rw [R1CertBuild.fill_gbat_loop, if_neg (by rw [UScalar.lt_equiv]; omega)] at h
      rw [← ok_inj h]
      exact ⟨by simp, fun y _ => rfl, fun t' h1 h2 => by omega⟩
  | m + 1, out, t, res, hm, h => by
      rw [R1CertBuild.fill_gbat_loop, if_pos (by rw [UScalar.lt_equiv]; omega)] at h
      obtain ⟨i, hi, h⟩ := bind_eq_ok h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok h
      obtain ⟨t1, ht1, h⟩ := bind_eq_ok h
      have ht1v : t1.val = t.val + 1 := by rw [add_ok ht1]; simp
      unfold R1CertBuild.gbat_col at hout1
      obtain ⟨L1, Q1, Q2⟩ := gbat_col_spec al zz tr inact ti op x18 nf i1 i3 (78 + nf.val) out 0#usize out1
        (by simp) hout1
      obtain ⟨L, P1, P2⟩ := fill_gbat_loop_spec n nf m out1 t1 res (by omega) h
      refine ⟨by rw [L, L1]; ring, fun y hy => by rw [P1 y (by omega), Q1 y hy], fun t' h1 h2 c hc => ?_⟩
      by_cases et : t' = t.val
      · subst et
        obtain ⟨cc, v, hcc, hv, hl⟩ := Q2 c (by simp) hc
        refine ⟨v, ⟨i1, i3, cc, ?_, ?_, hcc, hv⟩, fun l hl8 => ?_⟩
        · rw [(ok_inj hi1).symm, castUs, (index_ok hi).2]; rfl
        · rw [(ok_inj hi3).symm, castUs, (index_ok hi2).2]; rfl
        · have e := hl l hl8
          simp only [u0', Nat.sub_zero] at e
          rw [Nat.sub_self, zero_mul, add_zero, P1 _ (by omega), ← Nat.add_assoc]
          exact e
      · obtain ⟨v, hv, hl⟩ := P2 t' (by omega) h2 c hc
        refine ⟨v, hv, fun l hl8 => ?_⟩
        have := hl l hl8
        rw [L1, ht1v, show out.val.length + 8 * (78 + nf.val) + (t' - (t.val + 1)) * (8 * (78 + nf.val)) +
            (8 * c + l) = out.val.length + (t' - t.val) * (8 * (78 + nf.val)) + (8 * c + l) by
          rw [show t' - t.val = (t' - (t.val + 1)) + 1 by omega]; ring] at this
        exact this

theorem fill_gbat_spec {n nf : Usize} {res : alloc.vec.Vec U32}
    (h : R1CertBuild.fill_gbat al zz tr inact ti op x18 srow slimb n nf = ok res) :
    ∀ t, t < n.val → ∀ c, c < 78 + nf.val → ∃ v : A8, GBatAt al zz tr inact ti op x18 srow slimb nf t c v ∧
      ∀ l, l < 8 → res.val[t * (8 * (78 + nf.val)) + (8 * c + l)]! = v.val[l]! := by
  obtain ⟨-, -, P⟩ := fill_gbat_loop_spec al zz tr inact ti op x18 srow slimb n nf n.val
    (alloc.vec.Vec.new U32) 0#usize res (by simp) h
  intro t ht c hc
  have := P t (by simp) ht c hc
  simpa using this

/-- **`fill_gbat_entries`**: cell `c` of column `t` of a `fill_gbat` output, read in the WideExact
limb basis `wb`, is the CertGBatK model `gbatP` of source `t` (row `srow t`, limb `slimb t`), with
the stored first-line points `x18`. -/
theorem fill_gbat_entries (hT : Tower B) (hW : w * w = B.u) (wb : Module.Basis (Fin 8) F K)
    (hwb : ∀ k : Fin 8, wb k = wbP B.i B.u w k.val) {n nf : Usize} {res : alloc.vec.Vec U32}
    (h : R1CertBuild.fill_gbat al zz tr inact ti op x18 srow slimb n nf = ok res)
    (t c : ℕ) (ht : t < n.val) (hc : c < 78 + nf.val) :
    ∑ l : Fin 8, φ ((res.val[t * ((78 + nf.val) * 8) + (8 * c + l.val)]!).val : ZP) • wb l =
      gbatP (Alimb B φ al) (Alimb B φ zz) (gN tr) (gN ti) (flK φ inact) (Wl B φ w op 0) (Wl B φ w op 1)
        (Wl B φ w op 2) (Wl B φ w op 3) (embR φ 536870912) B.i B.u (fun m => embR φ (gs x18 m)) nf.val
        (gNL srow t) (gNL slimb t) c := by
  obtain ⟨v, ⟨rr, kk, cc, hrr, hkk, hcc, hv⟩, hl⟩ := fill_gbat_spec al zz tr inact ti op x18 srow slimb h t ht c hc
  have e := gbat_cell_spec B φ w hT hW hv
  rw [hrr, hkk, hcc, psi8_sum B φ w] at e
  rw [← e, ← Fin.sum_univ_eq_sum_range (fun k => embR φ (g8 v k) * wbP B.i B.u w k) 8,
    show (78 + nf.val) * 8 = 8 * (78 + nf.val) by ring]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [hwb, hl l.val l.2]
  rfl

#print axioms u0term_spec
#print axioms ucell_r0_spec
#print axioms u1term_spec
#print axioms ucell_r1_spec
#print axioms ucell_spec
#print axioms gbat_cell_spec
#print axioms gbat_col_spec
#print axioms fill_gbat_loop_spec
#print axioms fill_gbat_spec
#print axioms fill_gbat_entries

end R1Z.CertBuild

end
