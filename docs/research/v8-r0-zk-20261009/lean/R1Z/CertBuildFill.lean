import R1Z.CertBuildChain

/-! D57.3: the extracted `fill_tq` lays out the chain-target matrix row-major:
entry `i·1084 + t` is `[t = i] + [t/4 = 244]·c_i[t mod 4]`, where `c_i` is the
coordinate-244 correction `corr i` (`fill_tq_spec`). -/

set_option autoImplicit false

namespace R1Z.CertBuild
open Aeneas Aeneas.Std Result R1Z.CertCheck R0P
open scoped BigOperators

variable {K : Type} [Field K] {F : Subfield K} (B : PackBasis F) (φ : ZP →+* ↥F)

/-- Row `i`, column `t` of the chain targets given the correction `c`. -/
def ent (i : ℕ) (c : A4) (t : ℕ) : ZP :=
  (if t = i then 1 else 0) + (if t / 4 = 244 then 1 else 0) * ga c (t % 4)

theorem push_ok {v : alloc.vec.Vec U32} {x : U32} {w : alloc.vec.Vec U32}
    (h : alloc.vec.Vec.push v x = ok w) : w.val = v.val ++ [x] := by
  have h' : alloc.vec.Vec.push v x = ok w := h
  unfold alloc.vec.Vec.push at h'
  dsimp only at h'
  split at h'
  · cases h'; simp
  · cases h'

theorem get_append_left (l : List U32) (x : U32) {m : ℕ} (hm : m < l.length) :
    (l ++ [x])[m]! = l[m]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD, List.getElem?_append_left hm]

theorem get_append_len (l : List U32) (x : U32) : (l ++ [x])[l.length]! = x := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_concat_length]
  rfl

theorem fromBool32Z (p : Prop) [Decidable p] :
    ((UScalar.cast_fromBool .U32 (decide p)).val : ZP) = if p then 1 else 0 := by
  rw [fromBool32]
  by_cases hp : p <;> simp [hp]

theorem fill_row_loop_spec (i : Usize) (c : A4) :
    ∀ (m : ℕ) (out : alloc.vec.Vec U32) (t : Usize) (r : alloc.vec.Vec U32), t.val + m = 1084 →
      R1CertBuild.fill_row_loop i c out t = ok r →
      r.val.length = out.val.length + m ∧ (∀ x, x < out.val.length → r.val[x]! = out.val[x]!) ∧
        ∀ s, t.val ≤ s → s < 1084 → ((r.val[out.val.length + (s - t.val)]!).val : ZP) = ent i.val c s
  | 0, out, t, r, hm, h => by
      rw [R1CertBuild.fill_row_loop, if_neg (by rw [UScalar.lt_equiv]; simp; omega)] at h
      rw [← ok_inj h]
      exact ⟨by simp, fun x _ => rfl, fun s h1 h2 => by omega⟩
  | m + 1, out, t, r, hm, h => by
      rw [R1CertBuild.fill_row_loop, if_pos (by rw [UScalar.lt_equiv]; simp; omega)] at h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      obtain ⟨on, hon, h⟩ := bind_eq_ok h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
      obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
      obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
      obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
      obtain ⟨i6, hi6, h⟩ := bind_eq_ok h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok h
      obtain ⟨t1, ht1, h⟩ := bind_eq_ok h
      have ht1v : t1.val = t.val + 1 := add_ok ht1
      have eo := push_ok hout1
      obtain ⟨L, P1, P2⟩ := fill_row_loop_spec i c m out1 t1 r (by omega) h
      have hlen : out1.val.length = out.val.length + 1 := by rw [eo]; simp
      have hval : ((i6.val : ℕ) : ZP) = ent i.val c t.val := by
        have a1 : (t = i) ↔ t.val = i.val := UScalar.eq_equiv t i
        have a2 : (i1 = 244#usize) ↔ t.val / 4 = 244 := by
          rw [UScalar.eq_equiv, div_ok (by simp) hi1]; simp
        rw [(fadd_spec hi6).2, (fmul_spec hi5).2, (ok_inj hi2).symm, (ok_inj hon).symm, fromBool32Z,
          fromBool32Z, aidx_ok hi4, rem_ok (by simp) hi3]
        simp only [a1, a2, ent, ga]
        simp
      refine ⟨by rw [L, hlen]; omega, fun x hx => ?_, fun s h1 h2 => ?_⟩
      · rw [P1 x (by omega), eo, get_append_left _ _ hx]
      · by_cases es : s = t.val
        · subst es
          rw [Nat.sub_self, add_zero, P1 _ (by omega), eo, get_append_len, hval]
        · have := P2 s (by omega) h2
          rw [hlen, ht1v, show out.val.length + 1 + (s - (t.val + 1)) = out.val.length + (s - t.val) by omega]
            at this
          exact this

/-- The chain-target correction of unit `i`. -/
def corrK (al hinv : Slice U32) (i : ℕ) : K :=
  prevR (Vu B (i / 4) (i % 4)) (Alimb B φ al) 10 * Hlimb B φ hinv * embR φ 1073741824

theorem fill_tq_loop_spec (hT : Tower B) (al hinv : Slice U32) :
    ∀ (m : ℕ) (out : alloc.vec.Vec U32) (i : Usize) (r : alloc.vec.Vec U32), i.val + m = 1084 →
      out.val.length = i.val * 1084 → R1CertBuild.fill_tq_loop al hinv out i = ok r →
      r.val.length = 1084 * 1084 ∧ (∀ x, x < out.val.length → r.val[x]! = out.val[x]!) ∧
        ∀ i', i.val ≤ i' → i' < 1084 → ∃ c : A4, ψa B φ c = corrK B φ al hinv i' ∧
          ∀ t, t < 1084 → ((r.val[i' * 1084 + t]!).val : ZP) = ent i' c t
  | 0, out, i, r, hm, hl, h => by
      rw [R1CertBuild.fill_tq_loop, if_neg (by rw [UScalar.lt_equiv]; simp; omega)] at h
      rw [← ok_inj h]
      exact ⟨by rw [hl]; omega, fun x _ => rfl, fun i' h1 h2 => by omega⟩
  | m + 1, out, i, r, hm, hl, h => by
      rw [R1CertBuild.fill_tq_loop, if_pos (by rw [UScalar.lt_equiv]; simp; omega)] at h
      obtain ⟨c, hc, h⟩ := bind_eq_ok h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok h
      obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
      have hi1v : i1.val = i.val + 1 := add_ok hi1
      obtain ⟨L1, Q1, Q2⟩ := fill_row_loop_spec i c 1084 out 0#usize out1 (by simp) hout1
      obtain ⟨L, P1, P2⟩ := fill_tq_loop_spec hT al hinv m out1 i1 r (by omega)
        (by rw [L1, hl, hi1v]; ring) h
      refine ⟨L, fun x hx => by rw [P1 x (by omega), Q1 x hx], fun i' h1 h2 => ?_⟩
      by_cases ei : i' = i.val
      · subst ei
        refine ⟨c, by rw [corr_spec B φ hT hc]; rfl, fun t ht => ?_⟩
        have := Q2 t (by simp) ht
        rw [P1 _ (by rw [L1, hl]; simp; omega)]
        rw [hl] at this
        simpa using this
      · exact P2 i' (by omega) h2

/-- **`fill_tq`**: row `i`'s entries are `ent i c_i` with `ψ c_i = corrK i`. -/
theorem fill_tq_spec (hT : Tower B) {al hinv : Slice U32} {r : alloc.vec.Vec U32}
    (h : R1CertBuild.fill_tq al hinv = ok r) :
    ∀ i, i < 1084 → ∃ c : A4, ψa B φ c = corrK B φ al hinv i ∧
      ∀ t, t < 1084 → ((r.val[i * 1084 + t]!).val : ZP) = ent i c t := by
  obtain ⟨-, -, P⟩ := fill_tq_loop_spec B φ hT al hinv 1084 (alloc.vec.Vec.new U32) 0#usize r (by simp)
    (by simp) h
  exact fun i hi => P i (by simp) hi

#print axioms fill_row_loop_spec
#print axioms fill_tq_loop_spec
#print axioms fill_tq_spec

end R1Z.CertBuild
