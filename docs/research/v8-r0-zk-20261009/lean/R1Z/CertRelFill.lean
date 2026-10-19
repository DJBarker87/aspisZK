import R1Z.CertRelCoef
import R1Z.CertBuildFill

/-! D64 hRel (3b): the extracted `fill_rel` lays out the relation matrix row-major with
width `bw = 8 (78 + nf)`: entry `(x, c)` is `rel_entry x c`, limb `x mod 8` of
`coef(x / 8, c / 8) · unit(c mod 8)`.  `fill_rel_entries` states this as the CertRelK
bridge `RelEntry` (the WideExact reading of the limbs is `coefP · wbP`), the only
statement the pure side (CertRelData) consumes.  Aeneas side only. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertBuild
open Aeneas Aeneas.Std Result R1Z.CertCheck R0P R1Z.CertRel
open scoped BigOperators

variable {K : Type} [Field K] {F : Subfield K} (B : PackBasis F) (φ : ZP →+* ↥F) (w : K)
variable (al zz tr inact ti op fpos rk ru li x16 : Slice U32) (nf : Usize)

/-- The relation coefficient model of the builder inputs. -/
abbrev coefK (rho i : ℕ) : K :=
  coefP nf.val (Wl B φ w op 2) (Wl B φ w op 3) (embR φ 536870912) (w2K B φ w al zz tr inact ti op) (gN fpos)
    (lfK B φ w op li rho) (nlK φ x16 rho) (gN rk rho) (gN ru rho) i

theorem wtb_wbP (m : ℕ) : wtb B w m = wbP B.i B.u w m := rfl

theorem psi8_sum (z : A8) : ψ8 B φ w z = ∑ k ∈ Finset.range 8, embR φ (g8 z k) * wbP B.i B.u w k := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [show wbP B.i B.u w 0 = 1 from rfl, show wbP B.i B.u w 1 = B.i from rfl,
    show wbP B.i B.u w 2 = B.u from rfl, show wbP B.i B.u w 3 = B.i * B.u from rfl,
    show wbP B.i B.u w 4 = 1 * w from rfl, show wbP B.i B.u w 5 = B.i * w from rfl,
    show wbP B.i B.u w 6 = B.u * w from rfl, show wbP B.i B.u w 7 = B.i * B.u * w from rfl, ψ8, ψ4, ψ4]
  ring

/-- Entry `(x, c)` from `rel_entry`. -/
def RelAt (x c : ℕ) (v : U32) : Prop :=
  ∃ xx cc : Usize, xx.val = x ∧ cc.val = c ∧
    R1CertBuild.rel_entry al zz tr inact ti op fpos rk ru li x16 nf xx cc = ok v

theorem rel_entry_spec (hT : Tower B) (hW : w * w = B.u) {xx cc : Usize} {v : U32}
    (h : R1CertBuild.rel_entry al zz tr inact ti op fpos rk ru li x16 nf xx cc = ok v) :
    ∃ z : A8, (v.val : ZP) = g8 z (xx.val % 8) ∧
      ψ8 B φ w z = coefK B φ w al zz tr inact ti op fpos rk ru li x16 nf (xx.val / 8) (cc.val / 8) *
        wtb B w (cc.val % 8) := by
  unfold R1CertBuild.rel_entry at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
  obtain ⟨z, hz, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  have ei : i.val = xx.val / 8 := by rw [div_ok (by simp) hi]; simp
  have ei1 : i1.val = cc.val / 8 := by rw [div_ok (by simp) hi1]; simp
  have ei2 : i2.val = cc.val % 8 := by rw [rem_ok (by simp) hi2]; simp
  have ei3 : i3.val = xx.val % 8 := by rw [rem_ok (by simp) hi3]; simp
  refine ⟨z, by rw [a8 h _ ei3], ?_⟩
  rw [psi_wmul B φ w hT hW hz, coef_spec B φ w hT hW ha, psi_wunit B φ w (by rw [ei2]; omega) ha1, ei, ei1, ei2]

theorem rel_row_spec (x : Usize) :
    ∀ (m : ℕ) (out : alloc.vec.Vec U32) (c : Usize) (res : alloc.vec.Vec U32), c.val + m = 8 * (78 + nf.val) →
      R1CertBuild.rel_row_loop al zz tr inact ti op fpos rk ru li x16 nf x out c = ok res →
      res.val.length = out.val.length + m ∧ (∀ y, y < out.val.length → res.val[y]! = out.val[y]!) ∧
        ∀ s, c.val ≤ s → s < 8 * (78 + nf.val) → ∃ cc : Usize, cc.val = s ∧
          R1CertBuild.rel_entry al zz tr inact ti op fpos rk ru li x16 nf x cc = ok (res.val[out.val.length + (s - c.val)]!)
  | 0, out, c, res, hm, h => by
      rw [R1CertBuild.rel_row_loop] at h
      obtain ⟨i, hi, h⟩ := bind_eq_ok h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      have e1 : i1.val = 8 * (78 + nf.val) := by rw [mul_ok hi1, add_ok hi]; simp
      rw [if_neg (by rw [UScalar.lt_equiv, e1]; omega)] at h
      rw [← ok_inj h]
      exact ⟨by simp, fun y _ => rfl, fun s h1 h2 => by omega⟩
  | m + 1, out, c, res, hm, h => by
      rw [R1CertBuild.rel_row_loop] at h
      obtain ⟨i, hi, h⟩ := bind_eq_ok h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      have e1 : i1.val = 8 * (78 + nf.val) := by rw [mul_ok hi1, add_ok hi]; simp
      rw [if_pos (by rw [UScalar.lt_equiv, e1]; omega)] at h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok h
      obtain ⟨c1, hc1, h⟩ := bind_eq_ok h
      have hc1v : c1.val = c.val + 1 := by rw [add_ok hc1]; simp
      have eo := push_ok hout1
      have hlen : out1.val.length = out.val.length + 1 := by rw [eo]; simp
      obtain ⟨L, P1, P2⟩ := rel_row_spec x m out1 c1 res (by omega) h
      refine ⟨by rw [L, hlen]; omega, fun y hy => by rw [P1 y (by omega), eo, get_append_left _ _ hy],
        fun s h1 h2 => ?_⟩
      by_cases es : s = c.val
      · subst es
        rw [Nat.sub_self, add_zero, P1 _ (by omega), eo, get_append_len]
        exact ⟨c, rfl, hi2⟩
      · obtain ⟨cc, hcc, hv⟩ := P2 s (by omega) h2
        rw [hlen, hc1v, show out.val.length + 1 + (s - (c.val + 1)) = out.val.length + (s - c.val) by omega]
          at hv
        exact ⟨cc, hcc, hv⟩

theorem fill_rel_loop_spec (q : Usize) :
    ∀ (m : ℕ) (out : alloc.vec.Vec U32) (x : Usize) (res : alloc.vec.Vec U32), x.val + m = q.val →
      R1CertBuild.fill_rel_loop al zz tr inact ti op fpos rk ru li x16 nf q out x = ok res →
      res.val.length = out.val.length + m * (8 * (78 + nf.val)) ∧
        (∀ y, y < out.val.length → res.val[y]! = out.val[y]!) ∧
        ∀ x', x.val ≤ x' → x' < q.val → ∀ c, c < 8 * (78 + nf.val) →
          RelAt al zz tr inact ti op fpos rk ru li x16 nf x' c
            (res.val[out.val.length + (x' - x.val) * (8 * (78 + nf.val)) + c]!)
  | 0, out, x, res, hm, h => by
      rw [R1CertBuild.fill_rel_loop, if_neg (by rw [UScalar.lt_equiv]; omega)] at h
      rw [← ok_inj h]
      exact ⟨by simp, fun y _ => rfl, fun x' h1 h2 => by omega⟩
  | m + 1, out, x, res, hm, h => by
      rw [R1CertBuild.fill_rel_loop, if_pos (by rw [UScalar.lt_equiv]; omega)] at h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok h
      obtain ⟨x1, hx1, h⟩ := bind_eq_ok h
      have hx1v : x1.val = x.val + 1 := by rw [add_ok hx1]; simp
      unfold R1CertBuild.rel_row at hout1
      obtain ⟨L1, Q1, Q2⟩ := rel_row_spec al zz tr inact ti op fpos rk ru li x16 nf x (8 * (78 + nf.val)) out
        0#usize out1 (by simp) hout1
      obtain ⟨L, P1, P2⟩ := fill_rel_loop_spec q m out1 x1 res (by omega) h
      refine ⟨by rw [L, L1]; ring, fun y hy => by rw [P1 y (by omega), Q1 y hy], fun x' h1 h2 c hc => ?_⟩
      by_cases ex : x' = x.val
      · subst ex
        obtain ⟨cc, hcc, hv⟩ := Q2 c (by simp) hc
        rw [P1 _ (by rw [L1]; simp; omega)]
        simp only [Nat.sub_self, zero_mul, add_zero]
        simp only [Nat.sub_zero, show (0#usize : Usize).val = 0 by simp] at hv
        exact ⟨x, cc, rfl, hcc, hv⟩
      · have := P2 x' (by omega) h2 c hc
        rw [L1, hx1v, show out.val.length + 8 * (78 + nf.val) + (x' - (x.val + 1)) * (8 * (78 + nf.val)) + c =
          out.val.length + (x' - x.val) * (8 * (78 + nf.val)) + c by
            rw [show x' - x.val = (x' - (x.val + 1)) + 1 by omega]; ring] at this
        exact this

/-- **`fill_rel`**: the CertRelK bridge `RelEntry` for the produced matrix. -/
theorem fill_rel_entries (hT : Tower B) (hW : w * w = B.u) {q : Usize} {res : alloc.vec.Vec U32}
    (h : R1CertBuild.fill_rel al zz tr inact ti op fpos rk ru li x16 nf q = ok res) :
    RelEntry (embR φ) B.i B.u w (fun n => ((res.val[n]!).val : ZP)) (8 * (78 + nf.val)) q.val
      (coefK B φ w al zz tr inact ti op fpos rk ru li x16 nf) := by
  obtain ⟨-, -, P⟩ := fill_rel_loop_spec al zz tr inact ti op fpos rk ru li x16 nf q q.val
    (alloc.vec.Vec.new U32) 0#usize res (by simp) h
  intro x c hx hc
  obtain ⟨xx, cc, hxx, hcc, hv⟩ := P x (by simp) hx c hc
  have hidx : (alloc.vec.Vec.new U32).val.length + (x - (0#usize : Usize).val) * (8 * (78 + nf.val)) + c =
      x * (8 * (78 + nf.val)) + c := by simp
  rw [hidx] at hv
  obtain ⟨z, hz1, hz2⟩ := rel_entry_spec B φ w al zz tr inact ti op fpos rk ru li x16 nf hT hW hv
  refine ⟨g8 z, ?_, ?_⟩
  · show ((res.val[x * (8 * (78 + nf.val)) + c]!).val : ZP) = g8 z (x % 8)
    rw [hz1, hxx]
  · rw [← psi8_sum, hz2, hxx, hcc, wtb_wbP]

#print axioms psi8_sum
#print axioms rel_entry_spec
#print axioms rel_row_spec
#print axioms fill_rel_loop_spec
#print axioms fill_rel_entries

end R1Z.CertBuild

end
