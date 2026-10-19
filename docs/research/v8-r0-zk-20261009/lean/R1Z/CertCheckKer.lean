import R1Z.CertCheckDot

/-! D49.4 C3: the extracted kernel-entry tests (`kimg_ok`, `piv_ok`, `ents_ok`).

`kco m st j idx io c co s i` is Lean `kcoord` read off the flat source-column
matrix `m` (column `t` at `t·st`): `m[j·st+i] + ∑_{p<s} m[idx[io+p]·st+i]·c[co+p]`.
`ents_ok = ok true` gives, for every entry, in-range indices (the sources are
`0 … lane.len-1`), pivots in the entry's lane, zero `z1`- and `z2`-coordinates
and `g`-coordinates equal to the supplied image `out`. -/

set_option autoImplicit false

namespace R1Z.CertCheck
open Aeneas Aeneas.Std Result R1CertCheck
open scoped BigOperators

/-- Kernel-entry coordinate `i` (Lean `kcoord`) on a flat column matrix. -/
def kco (m : Slice U32) (st j : ℕ) (idx : Slice U32) (io : ℕ) (c : Slice U32) (co s i : ℕ) : ZP :=
  gs m (j * st + i) + ∑ p ∈ Finset.range s, gs m (gi idx (io + p) * st + i) * gs c (co + p)

theorem and_dec {b : Bool} {p : Prop} [Decidable p] (h : (b && decide p) = true) : b = true ∧ p := by
  simpa [Bool.and_eq_true, decide_eq_true_eq] using h

theorem and_true' {b c : Bool} (h : (b && c) = true) : b = true ∧ c = true := by
  simpa [Bool.and_eq_true] using h

theorem kimg_loop_stop (m : Slice U32) (st nrows j : Usize) (idx : Slice U32) (io : Usize)
    (c : Slice U32) (co s : Usize) (tgt : Slice U32) (to1 ts : Usize) :
    ∀ (b : Bool) (i : Usize), ¬ i.val < nrows.val →
      kimg_ok_loop m st nrows j idx io c co s tgt to1 ts b i = ok b := by
  intro b i hi
  rw [kimg_ok_loop, if_neg (by rw [UScalar.lt_equiv]; exact hi)]

theorem kimg_loop_step (m : Slice U32) (st nrows j : Usize) (idx : Slice U32) (io : Usize)
    (c : Slice U32) (co s : Usize) (tgt : Slice U32) (to1 ts : Usize) :
    ∀ (b : Bool) (i : Usize) (r : Bool), i.val < nrows.val →
      kimg_ok_loop m st nrows j idx io c co s tgt to1 ts b i = ok r →
      ∃ b' i', i'.val = i.val + 1 ∧ kimg_ok_loop m st nrows j idx io c co s tgt to1 ts b' i' = ok r ∧
        (b' = true → b = true ∧
          kco m st.val j.val idx io.val c co.val s.val i.val = gs tgt (to1.val + i.val * ts.val)) := by
  intro b i r hi h
  rw [kimg_ok_loop, if_pos (by rw [UScalar.lt_equiv]; exact hi)] at h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
  obtain ⟨i6, hi6, h⟩ := bind_eq_ok h
  obtain ⟨v, hv, h⟩ := bind_eq_ok h
  obtain ⟨i7, hi7, h⟩ := bind_eq_ok h
  obtain ⟨i8, hi8, h⟩ := bind_eq_ok h
  obtain ⟨i9, hi9, h⟩ := bind_eq_ok h
  obtain ⟨i10, hi10, h⟩ := bind_eq_ok h
  obtain ⟨i11, hi11, h⟩ := bind_eq_ok h
  refine ⟨_, i11, add_ok hi11, h, fun hb => ?_⟩
  obtain ⟨hb1, heq⟩ := and_dec hb
  refine ⟨hb1, ?_⟩
  have e4 : i4 = UScalar.cast .U64 i3 := (ok_inj hi4).symm
  have e10 : i10 = UScalar.cast .U64 i9 := (ok_inj hi10).symm
  have hvv : (v.val : ZP) = (i10.val : ZP) := by rw [heq]
  rw [(modP_lt hv).2, add_ok hi6, Nat.cast_add, (kdot_spec hi5).2, e4, cast64, (index_ok hi3).2,
    add_ok hi2, mul_ok hi1, e10, cast64, (index_ok hi9).2, add_ok hi8, mul_ok hi7] at hvv
  exact hvv

/-- `kimg_ok`: every coordinate row of the entry equals the target. -/
theorem kimg_spec {m idx c tgt : Slice U32} {st nrows j io co s to1 ts : Usize}
    (h : kimg_ok m st nrows j idx io c co s tgt to1 ts = ok true) :
    ∀ i, i < nrows.val → kco m st.val j.val idx io.val c co.val s.val i = gs tgt (to1.val + i * ts.val) :=
  flag_loop0 (F := fun b i => kimg_ok_loop m st nrows j idx io c co s tgt to1 ts b i)
    (kimg_loop_stop m st nrows j idx io c co s tgt to1 ts)
    (kimg_loop_step m st nrows j idx io c co s tgt to1 ts) h

theorem piv_loop_stop (idx : Slice U32) (io s : Usize) (lane : Slice U32) (lj : U32) :
    ∀ (b : Bool) (p : Usize), ¬ p.val < s.val → piv_ok_loop idx io s lane lj b p = ok b := by
  intro b p hp
  rw [piv_ok_loop, if_neg (by rw [UScalar.lt_equiv]; exact hp)]

theorem piv_loop_step (idx : Slice U32) (io s : Usize) (lane : Slice U32) (lj : U32) :
    ∀ (b : Bool) (p : Usize) (r : Bool), p.val < s.val →
      piv_ok_loop idx io s lane lj b p = ok r →
      ∃ b' p', p'.val = p.val + 1 ∧ piv_ok_loop idx io s lane lj b' p' = ok r ∧
        (b' = true → b = true ∧ (gi idx (io.val + p.val) < lane.val.length ∧
          gi lane (gi idx (io.val + p.val)) = lj.val)) := by
  intro b p r hp h
  rw [piv_ok_loop, if_pos (by rw [UScalar.lt_equiv]; exact hp)] at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨t, ht, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨p1, hp1, h⟩ := bind_eq_ok h
  refine ⟨_, p1, add_ok hp1, h, fun hb => ?_⟩
  obtain ⟨hb1, heq⟩ := and_dec hb
  have et : t = UScalar.cast .Usize i1 := (ok_inj ht).symm
  have etv : t.val = gi idx (io.val + p.val) := by
    rw [et, castUs, (index_ok hi1).2, add_ok hi]; rfl
  refine ⟨hb1, ?_, ?_⟩
  · rw [← etv]; exact (index_ok hi2).1
  · rw [← etv, ← heq, (index_ok hi2).2]; rfl

theorem piv_spec {idx lane : Slice U32} {io s : Usize} {lj : U32}
    (h : piv_ok idx io s lane lj = ok true) :
    ∀ p, p < s.val → gi idx (io.val + p) < lane.val.length ∧ gi lane (gi idx (io.val + p)) = lj.val :=
  flag_loop0 (F := fun b p => piv_ok_loop idx io s lane lj b p)
    (piv_loop_stop idx io s lane lj) (piv_loop_step idx io s lane lj) h

/-- What `ents_ok` certifies about entry `e`. -/
def EntOK (ej es epo eco idx coef lane wl : Slice U32) (z1 : Slice U32) (s1 : ℕ)
    (z2 : Slice U32) (s2 n2 : ℕ) (g : Slice U32) (sg ng : ℕ) (out : Slice U32) (zero : Slice U32)
    (e : ℕ) : Prop :=
  gi ej e < lane.val.length ∧
  (∀ p, p < gi es e → gi idx (gi epo e + p) < lane.val.length ∧
      gi lane (gi idx (gi epo e + p)) = gi lane (gi ej e)) ∧
  (∀ i, i < gi wl (gi lane (gi ej e)) →
      kco z1 s1 (gi ej e) idx (gi epo e) coef (gi eco e) (gi es e) i = gs zero 0) ∧
  (∀ i, i < n2 → kco z2 s2 (gi ej e) idx (gi epo e) coef (gi eco e) (gi es e) i = gs zero 0) ∧
  (∀ i, i < ng → kco g sg (gi ej e) idx (gi epo e) coef (gi eco e) (gi es e) i = gs out (e * ng + i))

theorem ents_loop_stop (ej es epo eco idx coef : Slice U32) (m : Usize) (lane wl : Slice U32)
    (z1 : Slice U32) (s1 : Usize) (z2 : Slice U32) (s2 n2 : Usize) (g : Slice U32)
    (sg ng : Usize) (out zero : Slice U32) :
    ∀ (b : Bool) (e : Usize), ¬ e.val < m.val →
      ents_ok_loop ej es epo eco idx coef m lane wl z1 s1 z2 s2 n2 g sg ng out zero b e = ok b := by
  intro b e he
  rw [ents_ok_loop, if_neg (by rw [UScalar.lt_equiv]; exact he)]

theorem ents_loop_step (ej es epo eco idx coef : Slice U32) (m : Usize) (lane wl : Slice U32)
    (z1 : Slice U32) (s1 : Usize) (z2 : Slice U32) (s2 n2 : Usize) (g : Slice U32)
    (sg ng : Usize) (out zero : Slice U32) :
    ∀ (b : Bool) (e : Usize) (r : Bool), e.val < m.val →
      ents_ok_loop ej es epo eco idx coef m lane wl z1 s1 z2 s2 n2 g sg ng out zero b e = ok r →
      ∃ b' e', e'.val = e.val + 1 ∧
        ents_ok_loop ej es epo eco idx coef m lane wl z1 s1 z2 s2 n2 g sg ng out zero b' e' = ok r ∧
        (b' = true → b = true ∧ EntOK ej es epo eco idx coef lane wl z1 s1.val z2 s2.val n2.val
          g sg.val ng.val out zero e.val) := by
  intro b e r he h
  rw [ents_ok_loop, if_pos (by rw [UScalar.lt_equiv]; exact he)] at h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨j, hj, h⟩ := bind_eq_ok h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok h
  obtain ⟨s, hs, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨io, hio, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  obtain ⟨co, hco, h⟩ := bind_eq_ok h
  obtain ⟨lj, hlj, h⟩ := bind_eq_ok h
  obtain ⟨i4, hi4, h⟩ := bind_eq_ok h
  obtain ⟨i5, hi5, h⟩ := bind_eq_ok h
  obtain ⟨w1, hw1, h⟩ := bind_eq_ok h
  obtain ⟨b0, hb0, h⟩ := bind_eq_ok h
  obtain ⟨b1, hb1, h⟩ := bind_eq_ok h
  obtain ⟨b2, hb2, h⟩ := bind_eq_ok h
  obtain ⟨i6, hi6, h⟩ := bind_eq_ok h
  obtain ⟨b3, hb3, h⟩ := bind_eq_ok h
  obtain ⟨e1, he1, h⟩ := bind_eq_ok h
  refine ⟨_, e1, add_ok he1, h, fun hb => ?_⟩
  obtain ⟨hb', hb3t⟩ := and_true' hb
  obtain ⟨hb', hb2t⟩ := and_true' hb'
  obtain ⟨hb', hb1t⟩ := and_true' hb'
  obtain ⟨hbt, hb0t⟩ := and_true' hb'
  have ejv : j.val = gi ej e.val := by
    rw [(ok_inj hj).symm, castUs, (index_ok hi).2]; rfl
  have esv : s.val = gi es e.val := by
    rw [(ok_inj hs).symm, castUs, (index_ok hi1).2]; rfl
  have eio : io.val = gi epo e.val := by
    rw [(ok_inj hio).symm, castUs, (index_ok hi2).2]; rfl
  have eco' : co.val = gi eco e.val := by
    rw [(ok_inj hco).symm, castUs, (index_ok hi3).2]; rfl
  have elj : lj.val = gi lane (gi ej e.val) := by
    rw [(index_ok hlj).2, ejv]; rfl
  have ew1 : w1.val = gi wl (gi lane (gi ej e.val)) := by
    rw [(ok_inj hw1).symm, castUs, (index_ok hi5).2, (ok_inj hi4).symm, castUs, (index_ok hlj).2, ejv]
    rfl
  refine ⟨hbt, ejv ▸ (index_ok hlj).1, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have := piv_spec (hb0t ▸ hb0) p (by rw [esv]; exact hp)
    rw [eio, elj] at this
    exact this
  · intro i hi'
    have := kimg_spec (hb1t ▸ hb1) i (by rw [ew1]; exact hi')
    rw [ejv, eio, eco', esv] at this
    simpa using this
  · intro i hi'
    have := kimg_spec (hb2t ▸ hb2) i hi'
    rw [ejv, eio, eco', esv] at this
    simpa using this
  · intro i hi'
    have := kimg_spec (hb3t ▸ hb3) i hi'
    rw [ejv, eio, eco', esv, mul_ok hi6] at this
    simpa using this

/-- `ents_ok`: every entry satisfies `EntOK`. -/
theorem ents_spec {ej es epo eco idx coef lane wl z1 z2 g out zero : Slice U32}
    {m s1 s2 n2 sg ng : Usize}
    (h : ents_ok ej es epo eco idx coef m lane wl z1 s1 z2 s2 n2 g sg ng out zero = ok true) :
    ∀ e, e < m.val → EntOK ej es epo eco idx coef lane wl z1 s1.val z2 s2.val n2.val
      g sg.val ng.val out zero e :=
  flag_loop0 (F := fun b e => ents_ok_loop ej es epo eco idx coef m lane wl z1 s1 z2 s2 n2 g sg ng out zero b e)
    (ents_loop_stop ej es epo eco idx coef m lane wl z1 s1 z2 s2 n2 g sg ng out zero)
    (ents_loop_step ej es epo eco idx coef m lane wl z1 s1 z2 s2 n2 g sg ng out zero) h

#print axioms kimg_spec
#print axioms piv_spec
#print axioms ents_spec

end R1Z.CertCheck
