import R1Z.CertCheckMat
import R1Z.CertCheckHalf

/-! D49.4 C3: the extracted `check` returning `true` gives `CheckOK pb c`, the
conjunction of every test's M31 statement on the flat public data `pb` and
certificate `c` (`check_spec`).  `CheckOK` is the input of the transfer to the
`CertSound` Props (`CertCheckProps`). -/

set_option autoImplicit false

namespace R1Z.CertCheck
open Aeneas Aeneas.Std Result R1CertCheck
open scoped BigOperators

/-- A vector field as a slice. -/
abbrev sl (v : alloc.vec.Vec U32) : Slice U32 := alloc.vec.Vec.deref v

/-- The checker's one-limb zero target. -/
def zeroS : Slice U32 := Array.to_slice (Array.make 1#usize [0#u32])

theorem zeroS_gs : gs zeroS 0 = 0 := by
  simp [gs, zeroS, Array.to_slice, Array.make]

/-- QPrime: kernel entries over the referenced sources and `Y·ρ = T`. -/
def QPrimeOK (pb : Pub) (c : Cert) : Prop :=
  (∀ e, e < c.m.val → EntOK (sl c.ej) (sl c.es) (sl c.epo) (sl c.eco) (sl c.pidx) (sl c.coef)
    (sl pb.lane) (sl pb.wl) (sl pb.own) pb.os.val (sl pb.round) pb.rw.val 0 (sl pb.round) pb.rw.val
    pb.rw.val (sl c.rho) zeroS e) ∧
  (∀ i, i < pb.rw.val → ∀ j, j < pb.rw.val →
    ∑ p ∈ Finset.range c.m.val, gs (sl c.y) (0 + i * c.m.val + p) * gs (sl c.rho) (0 + j + p * pb.rw.val)
      = gs (sl pb.tq) (0 + i * pb.rw.val + j))

/-- BCondG: lengths, `U·Rel = E`, `tag` inverse to `lst`, `E` echelon on
`lst[0..r)`, the V_G entries, the `n_f` matrix and `Y_G·β = N`. -/
def BCondOK (pb : Pub) (c : Cert) : Prop :=
  (sl c.lst).val.length = pb.bw.val ∧ (sl c.tag).val.length = pb.bw.val ∧
  c.r.val + c.k.val = pb.bw.val ∧
  (∀ a, a < c.r.val → ∀ j, j < pb.bw.val →
    ∑ x ∈ Finset.range pb.q.val, gs (sl c.u) (0 + a * pb.q.val + x) * gs (sl pb.rel) (0 + j + x * pb.bw.val)
      = gs (sl c.e) (0 + a * pb.bw.val + j)) ∧
  (∀ x, x < pb.bw.val → gi (sl c.lst) x < (sl c.tag).val.length ∧ gi (sl c.tag) (gi (sl c.lst) x) = x) ∧
  (∀ x, x < pb.bw.val → gi (sl c.tag) x < (sl c.lst).val.length ∧ gi (sl c.lst) (gi (sl c.tag) x) = x) ∧
  (∀ a, a < c.r.val → ∀ b, b < c.r.val →
    gs (sl c.e) (a * pb.bw.val + gi (sl c.lst) b) = if a = b then 1 else 0) ∧
  (∀ e, e < c.mg.val → EntOK (sl c.gej) (sl c.ges) (sl c.gepo) (sl c.geco) (sl c.gpidx) (sl c.gcoef)
    (sl pb.glane) (sl pb.gwl) (sl pb.gown) pb.gw.val (sl pb.ground) pb.rw.val pb.rw.val (sl pb.gbat)
    pb.bw.val pb.bw.val (sl c.beta) zeroS e) ∧
  (∀ f, f < c.k.val → ∀ t, t < pb.bw.val →
    gs (sl c.nm) (f * pb.bw.val + t) = nval (sl c.e) pb.bw.val (sl c.tag) c.r.val (gi (sl c.lst) (c.r.val + f)) t) ∧
  (∀ f, f < c.k.val → ∀ t, t < pb.bw.val →
    ∑ p ∈ Finset.range c.mg.val, gs (sl c.yg) (0 + f * c.mg.val + p) * gs (sl c.beta) (0 + t + p * pb.bw.val)
      = gs (sl c.nm) (0 + f * pb.bw.val + t))

/-- Everything `check` tests. -/
def CheckOK (pb : Pub) (c : Cert) : Prop :=
  HalfEq (sl pb.a9) (sl c.hinv) ∧ pb.nq.val ≤ 22 ∧
  (∀ l, l < pb.nl.val → LiftOK (sl pb.lo) (sl c.lu) (sl c.lid) (sl pb.lw) (sl pb.loff) l) ∧
  QPrimeOK pb c ∧ BCondOK pb c

theorem castU {x : U32} {y : Usize} (h : lift (UScalar.cast .Usize x) = ok y) : y.val = x.val := by
  rw [(ok_inj h).symm, castUs]

theorem qprime_spec {pb : Pub} {c : Cert} (h : check_qprime pb c = ok true) : QPrimeOK pb c := by
  unfold check_qprime at h
  obtain ⟨rw, hrw, h⟩ := bind_eq_ok h
  obtain ⟨m, hm, h⟩ := bind_eq_ok h
  obtain ⟨os, hos, h⟩ := bind_eq_ok h
  obtain ⟨s12, hs12, h⟩ := bind_eq_ok h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  obtain ⟨b, hb, h⟩ := bind_eq_ok h
  obtain ⟨hat, hbt⟩ := and_true' (ok_inj h)
  have es12 : s12 = zeroS := (ok_inj hs12).symm
  have E := ents_spec (hat ▸ ha)
  have Pp := prod_spec (hbt ▸ hb)
  rw [castU hrw, castU hm, castU hos, es12, u0] at E
  rw [castU hrw, castU hm, u0] at Pp
  exact ⟨E, Pp⟩

theorem len_val (v : alloc.vec.Vec U32) : (alloc.vec.Vec.len v).val = (sl v).val.length := by
  simp [alloc.vec.Vec.len, sl, alloc.vec.Vec.deref]

theorem bcond_spec {pb : Pub} {c : Cert} (h : check_bcond pb c = ok true) : BCondOK pb c := by
  unfold check_bcond at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok h
  obtain ⟨r, hr, h⟩ := bind_eq_ok h
  obtain ⟨k, hk, h⟩ := bind_eq_ok h
  obtain ⟨q, hq, h⟩ := bind_eq_ok h
  obtain ⟨mg, hmg, h⟩ := bind_eq_ok h
  obtain ⟨rw, hrw, h⟩ := bind_eq_ok h
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok h
  obtain ⟨e1, he1, h⟩ := bind_eq_ok h
  obtain ⟨e2, he2, h⟩ := bind_eq_ok h
  obtain ⟨e3, he3, h⟩ := bind_eq_ok h
  obtain ⟨e4, he4, h⟩ := bind_eq_ok h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok h
  obtain ⟨s21, hs21, h⟩ := bind_eq_ok h
  obtain ⟨g1, hg1, h⟩ := bind_eq_ok h
  obtain ⟨g2, hg2, h⟩ := bind_eq_ok h
  obtain ⟨g3, hg3, h⟩ := bind_eq_ok h
  have hb := ok_inj h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hl1, hl2⟩, hl3⟩, he1t⟩, he2t⟩, he3t⟩, he4t⟩, hg1t⟩, hg2t⟩, hg3t⟩ := hb
  have es21 : s21 = zeroS := (ok_inj hs21).symm
  have L1 := congrArg UScalar.val hl1
  have L2 := congrArg UScalar.val hl2
  have L3 := congrArg UScalar.val hl3
  rw [len_val, castU hn] at L1 L2
  rw [add_ok hi2, castU hr, castU hk, castU hn] at L3
  have P1 := prod_spec (he1t ▸ he1)
  have P2 := perm_left_spec (he2t ▸ he2)
  have P3 := perm_right_spec (he3t ▸ he3)
  have P4 := ech_spec (he4t ▸ he4)
  have G1 := ents_spec (hg1t ▸ hg1)
  have G2 := nvec_spec (hg2t ▸ hg2)
  have G3 := prod_spec (hg3t ▸ hg3)
  rw [castU hr, castU hn, castU hq, u0] at P1
  rw [castU hn] at P2 P3
  rw [castU hr, castU hn] at P4
  rw [castU hmg, castU hi3, castU hrw, castU hn, es21] at G1
  rw [castU hk, castU hn, castU hr] at G2
  rw [castU hk, castU hn, castU hmg, u0] at G3
  exact ⟨L1, L2, L3, P1, P2, P3, P4, G1, G2, G3⟩

/-- **The extracted checker's success gives every test's M31 statement.** -/
theorem check_spec {pb : Pub} {c : Cert} (h : check pb c = ok true) : CheckOK pb c := by
  unfold check at h
  obtain ⟨hh, hhh, h⟩ := bind_eq_ok h
  obtain ⟨i, hi, h⟩ := bind_eq_ok h
  obtain ⟨li, hli, h⟩ := bind_eq_ok h
  obtain ⟨qp, hqp, h⟩ := bind_eq_ok h
  obtain ⟨bc, hbc, h⟩ := bind_eq_ok h
  have hb := ok_inj h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨hht, hnq⟩, hlit⟩, hqpt⟩, hbct⟩ := hb
  have Ls := lifts_spec (hlit ▸ hli)
  rw [castU hi] at Ls
  exact ⟨half_spec (hht ▸ hhh), by rw [UScalar.le_equiv] at hnq; simpa using hnq, Ls,
    qprime_spec (hqpt ▸ hqp), bcond_spec (hbct ▸ hbc)⟩

#print axioms zeroS_gs
#print axioms qprime_spec
#print axioms bcond_spec
#print axioms check_spec

end R1Z.CertCheck
