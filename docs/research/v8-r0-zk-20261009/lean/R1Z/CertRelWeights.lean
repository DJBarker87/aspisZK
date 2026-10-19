import R1Z.CertRelW
import R1Z.CertRelK

/-! D64 hRel (2a): the extracted weights and dual folds (builder 4 `ellq`, `wt`, `df1`,
`df2`) as the CertRelK models `ellP`, `wtP`, `w1P`, `w2P` of the builder inputs (alpha
limbs, OOD limbs, transport `tr`, inverse transport `ti`, inactive flags, openings).
Aeneas side only: the identification with `weightsR1`, `w1`, `w2` is CertRelWId. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertBuild
open Aeneas Aeneas.Std Result R1Z.CertCheck R0P R1Z.CertRel
open scoped BigOperators

variable {K : Type} [Field K] {F : Subfield K} (B : PackBasis F) (φ : ZP →+* ↥F) (w : K)

/-! ### The builder values -/

theorem natR_P : ∀ (k : ℕ) (x : K) (m : ℕ), natR x m k = natP x m k
  | 0, x, m => rfl
  | k + 1, x, m => by rw [natR, natP, natR_P k]

theorem headK_P (A Z : ℕ → K) (co r g : ℕ) : headK A Z co r g = headP A Z co r g := by
  simp only [headK, headP, eqK, eqP, pcK, pcP, scK, scP, hwK, hwP, evK, evP, natR_P]

/-- The flags of `inact` in `K`. -/
def flK (inact : Slice U32) (r : ℕ) : K := embR φ (gs inact r)

/-- `ell_k(e_j)` at row `r` from the builder inputs. -/
abbrev ellK (al zz tr inact : Slice U32) (r k : ℕ) : K :=
  ellP (Alimb B φ al) (Alimb B φ zz) (gN tr) (flK φ inact) r k

/-- The batched weight of message index `j` from the builder inputs. -/
abbrev wtK (al zz tr inact ti op : Slice U32) (j : ℕ) : K :=
  wtP (Alimb B φ al) (Alimb B φ zz) (gN tr) (gN ti) (flK φ inact) (Wl B φ w op 1) j

abbrev w1K (al zz tr inact ti op : Slice U32) (d : ℕ) : K :=
  w1P (Alimb B φ al) (Alimb B φ zz) (gN tr) (gN ti) (flK φ inact) (Wl B φ w op 1) (Wl B φ w op 2)
    (embR φ 536870912) d

abbrev w2K (al zz tr inact ti op : Slice U32) (e : ℕ) : K :=
  w2P (Alimb B φ al) (Alimb B φ zz) (gN tr) (gN ti) (flK φ inact) (Wl B φ w op 1) (Wl B φ w op 2)
    (Wl B φ w op 3) (embR φ 536870912) e

theorem ellq_spec (hT : Tower B) {al zz tr inact : Slice U32} {r k : Usize} {z : A4}
    (h : R1CertBuild.ellq al zz tr inact r k = ok z) : ψa B φ z = ellK B φ al zz tr inact r.val k.val := by
  unfold R1CertBuild.ellq at h
  unfold ellK ellP
  by_cases k0 : k.val = 0
  · rw [if_pos ((ueq (lit := 0#usize) (n := 0) (by simp)).2 k0)] at h
    rw [if_pos k0]
    obtain ⟨i, hi, h⟩ := bind_eq_ok h
    rw [(qbase_spec B φ h).1, idx_z' hi, flK]
  · rw [if_neg (fun h' => k0 ((ueq (lit := 0#usize) (n := 0) (by simp)).1 h'))] at h
    rw [if_neg k0]
    obtain ⟨i, hi, h⟩ := bind_eq_ok h
    rw [head_q_spec B φ hT h, (sub_ok hi).1, u1', headK_P]

theorem wt_spec (hT : Tower B) (hW : w * w = B.u) {al zz tr inact ti op : Slice U32} {j : Usize} {z : A8}
    (h : R1CertBuild.wt al zz tr inact ti op j = ok z) :
    ψ8 B φ w z = wtK B φ w al zz tr inact ti op j.val := by
  unfold R1CertBuild.wt at h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  unfold R1CertBuild.wt_loop at h
  have er : i1.val = gN ti j.val := by rw [(ok_inj hi1).symm, castUs, (index_ok hi).2]; rfl
  have E := acc_loopG (ψ8 B φ w) (G := fun acc k => R1CertBuild.wt_loop_loop al zz tr inact op i1 acc k)
    (n := 7) (T := fun k => Wl B φ w op 1 ^ k * ellK B φ al zz tr inact i1.val k)
    (fun a t ht => by rw [R1CertBuild.wt_loop_loop, if_neg (by rw [UScalar.lt_equiv]; simpa using ht)])
    (fun a t res ht h => by
      rw [R1CertBuild.wt_loop_loop, if_pos (by rw [UScalar.lt_equiv]; simpa using ht)] at h
      obtain ⟨b0, hb0, h⟩ := bind_eq_ok h
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok h
      obtain ⟨b2, hb2, h⟩ := bind_eq_ok h
      obtain ⟨b3, hb3, h⟩ := bind_eq_ok h
      obtain ⟨b4, hb4, h⟩ := bind_eq_ok h
      obtain ⟨acc1, hacc1, h⟩ := bind_eq_ok h
      obtain ⟨t1, ht1, h⟩ := bind_eq_ok h
      refine ⟨acc1, t1, add_ok ht1, h, ?_⟩
      rw [psi_wadd B φ w hacc1, psi_wmul B φ w hT hW hb4, psi_wpow B φ w hT hW hb1, psi_wget B φ w hb0,
        psi_wq B φ w hb3, ellq_spec B φ hT hb2, u1'])
    7 a 0#usize z (by simp) h
  rw [E, psi_wzero B φ w ha, zero_add, wtK, wtP]
  simp only [u0', er, Finset.range_eq_Ico]

theorem wq_quarter {z : A8} (h : R1CertBuild.wbase 536870912#u32 = ok z) : ψ8 B φ w z = embR φ 536870912 := by
  rw [psi_wbase B φ w h]
  simp

theorem df1_spec (hT : Tower B) (hW : w * w = B.u) {al zz tr inact ti op : Slice U32} {d : Usize} {z : A8}
    (h : R1CertBuild.df1 al zz tr inact ti op d = ok z) :
    ψ8 B φ w z = w1K B φ w al zz tr inact ti op d.val := by
  unfold R1CertBuild.df1 at h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
  obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
  unfold R1CertBuild.df1_loop at ha2
  have E := acc_loopG (ψ8 B φ w) (G := fun acc t => R1CertBuild.df1_loop_loop al zz tr inact ti op d acc t)
    (n := 4) (T := fun t => wtK B φ w al zz tr inact ti op (4 * d.val + t) * Wl B φ w op 2 ^ ((4 - t) % 4))
    (fun a t ht => by rw [R1CertBuild.df1_loop_loop, if_neg (by rw [UScalar.lt_equiv]; simpa using ht)])
    (fun a t res ht h => by
      rw [R1CertBuild.df1_loop_loop, if_pos (by rw [UScalar.lt_equiv]; simpa using ht)] at h
      obtain ⟨i, hi, h⟩ := bind_eq_ok h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      obtain ⟨b, hb, h⟩ := bind_eq_ok h
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
      obtain ⟨b2, hb2, h⟩ := bind_eq_ok h
      obtain ⟨b3, hb3, h⟩ := bind_eq_ok h
      obtain ⟨acc1, hacc1, h⟩ := bind_eq_ok h
      obtain ⟨t1, ht1, h⟩ := bind_eq_ok h
      refine ⟨acc1, t1, add_ok ht1, h, ?_⟩
      have e1 : i1.val = 4 * d.val + t.val := by rw [add_ok hi1, mul_ok hi]; simp
      have e3 : i3.val = (4 - t.val) % 4 := by rw [rem_ok (by simp) hi3, (sub_ok hi2).1]; simp
      rw [psi_wadd B φ w hacc1, psi_wmul B φ w hT hW hb3, psi_wpow B φ w hT hW hb2, psi_wget B φ w hb1,
        wt_spec B φ w hT hW hb, e1, e3, u2'])
    4 a1 0#usize a2 (by simp) ha2
  rw [psi_wmul B φ w hT hW h, wq_quarter B φ w ha, E, psi_wzero B φ w ha1, zero_add, w1K, w1P]
  simp only [u0', Finset.range_eq_Ico]

theorem df2_spec (hT : Tower B) (hW : w * w = B.u) {al zz tr inact ti op : Slice U32} {e : Usize} {z : A8}
    (h : R1CertBuild.df2 al zz tr inact ti op e = ok z) :
    ψ8 B φ w z = w2K B φ w al zz tr inact ti op e.val := by
  unfold R1CertBuild.df2 at h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  obtain ⟨a1, ha1, h⟩ := bind_eq_ok h
  obtain ⟨a2, ha2, h⟩ := bind_eq_ok h
  unfold R1CertBuild.df2_loop at ha2
  have E := acc_loopG (ψ8 B φ w) (G := fun acc t => R1CertBuild.df2_loop_loop al zz tr inact ti op e acc t)
    (n := 4) (T := fun t => w1K B φ w al zz tr inact ti op (4 * e.val + t) * Wl B φ w op 3 ^ ((4 - t) % 4))
    (fun a t ht => by rw [R1CertBuild.df2_loop_loop, if_neg (by rw [UScalar.lt_equiv]; simpa using ht)])
    (fun a t res ht h => by
      rw [R1CertBuild.df2_loop_loop, if_pos (by rw [UScalar.lt_equiv]; simpa using ht)] at h
      obtain ⟨i, hi, h⟩ := bind_eq_ok h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      obtain ⟨b, hb, h⟩ := bind_eq_ok h
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
      obtain ⟨b2, hb2, h⟩ := bind_eq_ok h
      obtain ⟨b3, hb3, h⟩ := bind_eq_ok h
      obtain ⟨acc1, hacc1, h⟩ := bind_eq_ok h
      obtain ⟨t1, ht1, h⟩ := bind_eq_ok h
      refine ⟨acc1, t1, add_ok ht1, h, ?_⟩
      have e1 : i1.val = 4 * e.val + t.val := by rw [add_ok hi1, mul_ok hi]; simp
      have e3 : i3.val = (4 - t.val) % 4 := by rw [rem_ok (by simp) hi3, (sub_ok hi2).1]; simp
      rw [psi_wadd B φ w hacc1, psi_wmul B φ w hT hW hb3, psi_wpow B φ w hT hW hb2, psi_wget B φ w hb1,
        df1_spec B φ w hT hW hb, e1, e3, u3'])
    4 a1 0#usize a2 (by simp) ha2
  rw [psi_wmul B φ w hT hW h, wq_quarter B φ w ha, E, psi_wzero B φ w ha1, zero_add, w2K, w2P]
  simp only [u0', Finset.range_eq_Ico]

#print axioms natR_P
#print axioms headK_P
#print axioms ellq_spec
#print axioms wt_spec
#print axioms df1_spec
#print axioms df2_spec

end R1Z.CertBuild

end
