import R1Z.CertSound
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! D49.4 C3: the checker's data without Aeneas types.

`CData` is the flat public data and certificate as functions `ℕ → ZP` (values)
and `ℕ → ℕ` (indices); `DataOK d` is the conjunction of the checker's tests on it
(the extracted `check` gives `DataOK (toData pb c)`, module `CertCheckData`).
Here `DataOK` is turned into the `CertSound` Props over `ZP = ZMod (2^31-1)`
(`data_qprime`, `data_bcond`, `data_lift`), for any row layout `st` of the
lane-blocked own matrix.  The module imports Mathlib and `CertSound` only, so
the final composition with `p_r1_of_checks` never loads Aeneas. -/

set_option autoImplicit false

namespace R1Z.CertData

open scoped BigOperators
open R1Z.CertSound

abbrev ZP := ZMod 2147483647

structure CData where
  rw : ℕ
  bw : ℕ
  nq : ℕ
  m : ℕ
  mg : ℕ
  r : ℕ
  k : ℕ
  q : ℕ
  nl : ℕ
  os : ℕ
  gw : ℕ
  N : ℕ
  NG : ℕ
  lstLen : ℕ
  tagLen : ℕ
  a9 : ℕ → ZP
  hinv : ℕ → ZP
  lane : ℕ → ℕ
  wl : ℕ → ℕ
  own : ℕ → ZP
  round : ℕ → ZP
  tq : ℕ → ZP
  ej : ℕ → ℕ
  es : ℕ → ℕ
  epo : ℕ → ℕ
  eco : ℕ → ℕ
  pidx : ℕ → ℕ
  coef : ℕ → ZP
  rho : ℕ → ZP
  y : ℕ → ZP
  rel : ℕ → ZP
  u : ℕ → ZP
  e : ℕ → ZP
  lst : ℕ → ℕ
  tag : ℕ → ℕ
  glane : ℕ → ℕ
  gwl : ℕ → ℕ
  gown : ℕ → ZP
  ground : ℕ → ZP
  gbat : ℕ → ZP
  gej : ℕ → ℕ
  ges : ℕ → ℕ
  gepo : ℕ → ℕ
  geco : ℕ → ℕ
  gpidx : ℕ → ℕ
  gcoef : ℕ → ZP
  beta : ℕ → ZP
  yg : ℕ → ZP
  nm : ℕ → ZP
  lw : ℕ → ℕ
  loff : ℕ → ℕ
  lo : ℕ → ZP
  lu : ℕ → ZP
  lid : ℕ → ZP

/-- Kernel-entry coordinate `i` on a flat column matrix (column `t` at `t·st`). -/
def kcoF (m : ℕ → ZP) (st j : ℕ) (idx : ℕ → ℕ) (io : ℕ) (c : ℕ → ZP) (co s i : ℕ) : ZP :=
  m (j * st + i) + ∑ p ∈ Finset.range s, m (idx (io + p) * st + i) * c (co + p)

/-- One kernel entry's tests. -/
def EntOKF (ej es epo eco idx : ℕ → ℕ) (coef : ℕ → ZP) (lane wl : ℕ → ℕ) (N : ℕ)
    (z1 : ℕ → ZP) (s1 : ℕ) (z2 : ℕ → ZP) (s2 n2 : ℕ) (g : ℕ → ZP) (sg ng : ℕ) (out : ℕ → ZP)
    (e : ℕ) : Prop :=
  ej e < N ∧
  (∀ p, p < es e → idx (epo e + p) < N ∧ lane (idx (epo e + p)) = lane (ej e)) ∧
  (∀ i, i < wl (lane (ej e)) → kcoF z1 s1 (ej e) idx (epo e) coef (eco e) (es e) i = 0) ∧
  (∀ i, i < n2 → kcoF z2 s2 (ej e) idx (epo e) coef (eco e) (es e) i = 0) ∧
  (∀ i, i < ng → kcoF g sg (ej e) idx (epo e) coef (eco e) (es e) i = out (e * ng + i))

/-- The HalfOK limb equations. -/
def HalfEqF (a h : ℕ → ZP) : Prop :=
  ((a 0 - 1073741824) * h 0 - a 1 * h 1 + 2 * (a 2 * h 2 - a 3 * h 3) - (a 2 * h 3 + a 3 * h 2) = 1) ∧
  ((a 0 - 1073741824) * h 1 + a 1 * h 0 + (a 2 * h 2 - a 3 * h 3) + 2 * (a 2 * h 3 + a 3 * h 2) = 0) ∧
  ((a 0 - 1073741824) * h 2 - a 1 * h 3 + a 2 * h 0 - a 3 * h 1 = 0) ∧
  ((a 0 - 1073741824) * h 3 + a 1 * h 2 + a 2 * h 1 + a 3 * h 0 = 0)

/-- One lift block's tests. -/
def LiftOKF (o u id : ℕ → ZP) (lw loff : ℕ → ℕ) (l : ℕ) : Prop :=
  (∀ i, i < lw l → ∀ j, j < lw l →
    ∑ p ∈ Finset.range (lw l), o (loff l + i * lw l + p) * u (loff l + j + p * lw l)
      = id (loff l + i * lw l + j)) ∧
  (∀ i, i < lw l → ∀ j, j < lw l → id (loff l + i * lw l + j) = if i = j then 1 else 0)

/-- The n_f value at column `t`. -/
def nvalF (e : ℕ → ZP) (n : ℕ) (tag : ℕ → ℕ) (r ff t : ℕ) : ZP :=
  (if t = ff then 1 else 0) - (if tag t < r then e (tag t * n + ff) else 0)

/-- Everything the checker tests, on the flat data. -/
def DataOK (d : CData) : Prop :=
  HalfEqF d.a9 d.hinv ∧ d.nq ≤ 22 ∧
  (∀ l, l < d.nl → LiftOKF d.lo d.lu d.lid d.lw d.loff l) ∧
  ((∀ e, e < d.m → EntOKF d.ej d.es d.epo d.eco d.pidx d.coef d.lane d.wl d.N d.own d.os
      d.round d.rw 0 d.round d.rw d.rw d.rho e) ∧
    (∀ i, i < d.rw → ∀ j, j < d.rw →
      ∑ p ∈ Finset.range d.m, d.y (0 + i * d.m + p) * d.rho (0 + j + p * d.rw) = d.tq (0 + i * d.rw + j))) ∧
  (d.lstLen = d.bw ∧ d.tagLen = d.bw ∧ d.r + d.k = d.bw ∧
    (∀ a, a < d.r → ∀ j, j < d.bw →
      ∑ x ∈ Finset.range d.q, d.u (0 + a * d.q + x) * d.rel (0 + j + x * d.bw) = d.e (0 + a * d.bw + j)) ∧
    (∀ x, x < d.bw → d.lst x < d.tagLen ∧ d.tag (d.lst x) = x) ∧
    (∀ x, x < d.bw → d.tag x < d.lstLen ∧ d.lst (d.tag x) = x) ∧
    (∀ a, a < d.r → ∀ b, b < d.r → d.e (a * d.bw + d.lst b) = if a = b then 1 else 0) ∧
    (∀ e, e < d.mg → EntOKF d.gej d.ges d.gepo d.geco d.gpidx d.gcoef d.glane d.gwl d.NG d.gown d.gw
      d.ground d.rw d.rw d.gbat d.bw d.bw d.beta e) ∧
    (∀ f, f < d.k → ∀ t, t < d.bw → d.nm (f * d.bw + t) = nvalF d.e d.bw d.tag d.r (d.lst (d.r + f)) t) ∧
    (∀ f, f < d.k → ∀ t, t < d.bw →
      ∑ p ∈ Finset.range d.mg, d.yg (0 + f * d.mg + p) * d.beta (0 + t + p * d.bw) = d.nm (0 + f * d.bw + t)))

/-! ### Matrices -/

/-- The lane-blocked own matrix: source `t`'s column holds `own[t·os ..]` on the
rows `st(lane t) … st(lane t) + wl(lane t) - 1` and zero elsewhere. -/
def blockM (own : ℕ → ZP) (os : ℕ) (lane wl : ℕ → ℕ) (st : ℕ → ℕ) (i t : ℕ) : ZP :=
  if st (lane t) ≤ i ∧ i < st (lane t) + wl (lane t) then own (t * os + (i - st (lane t))) else 0

/-- A flat column matrix: column `t` at `t·s`. -/
def colM (m : ℕ → ZP) (s : ℕ) (i t : ℕ) : ZP := m (t * s + i)

/-- A row-major matrix with `cols` columns. -/
def rowM (m : ℕ → ZP) (cols : ℕ) (i j : ℕ) : ZP := m (i * cols + j)

section Field

variable {F : Type*} [Field F] (φ : ZP →+* F)

/-- The kernel entries of a family, as `KerEntry`s over `F` (bounds from the tests). -/
def entF (ej es epo eco idx : ℕ → ℕ) (coef : ℕ → ZP) (N : ℕ) (e : ℕ) (hj : ej e < N)
    (hp : ∀ p, p < es e → idx (epo e + p) < N) : KerEntry N F where
  s := es e
  j := ⟨ej e, hj⟩
  piv := fun p => ⟨idx (epo e + p), hp p p.2⟩
  c := fun p => φ (coef (eco e + p))

/-- `kcoord` of a mapped matrix on a family entry. -/
theorem kcoord_map (A : ℕ → ℕ → ZP) {a N : ℕ} (ej es epo eco idx : ℕ → ℕ) (coef : ℕ → ZP)
    (e : ℕ) (hj : ej e < N) (hp : ∀ p, p < es e → idx (epo e + p) < N) (i : Fin a) :
    kcoord (fun (i : Fin a) (t : Fin N) => φ (A i t)) (entF φ ej es epo eco idx coef N e hj hp) i =
      φ (A i (ej e) + ∑ p ∈ Finset.range (es e), A i (idx (epo e + p)) * coef (eco e + p)) := by
  unfold kcoord entF
  simp only
  rw [map_add, map_sum]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun p => φ (A i (idx (epo e + p)) * coef (eco e + p)))]
  exact Finset.sum_congr rfl fun p _ => by rw [map_mul]

theorem kco_colM (m : ℕ → ZP) (s : ℕ) (ej es epo eco idx : ℕ → ℕ) (coef : ℕ → ZP) (e i : ℕ) :
    colM m s i (ej e) + ∑ p ∈ Finset.range (es e), colM m s i (idx (epo e + p)) * coef (eco e + p) =
      kcoF m s (ej e) idx (epo e) coef (eco e) (es e) i := rfl

theorem kco_blockM (own : ℕ → ZP) (os : ℕ) (lane wl st : ℕ → ℕ) (ej es epo eco idx : ℕ → ℕ)
    (coef : ℕ → ZP) (e i : ℕ)
    (hl : ∀ p, p < es e → lane (idx (epo e + p)) = lane (ej e))
    (hk : ∀ i, i < wl (lane (ej e)) → kcoF own os (ej e) idx (epo e) coef (eco e) (es e) i = 0) :
    blockM own os lane wl st i (ej e) +
      ∑ p ∈ Finset.range (es e), blockM own os lane wl st i (idx (epo e + p)) * coef (eco e + p) = 0 := by
  have hlane : ∀ p ∈ Finset.range (es e), blockM own os lane wl st i (idx (epo e + p)) =
      blockM own os (fun _ => lane (ej e)) wl st i (idx (epo e + p)) := by
    intro p hp'
    unfold blockM
    rw [hl p (Finset.mem_range.1 hp')]
  rw [Finset.sum_congr rfl fun p hp' => by rw [hlane p hp']]
  by_cases hi : st (lane (ej e)) ≤ i ∧ i < st (lane (ej e)) + wl (lane (ej e))
  · have := hk (i - st (lane (ej e))) (by omega)
    unfold kcoF at this
    unfold blockM
    simp only [if_pos hi]
    exact this
  · unfold blockM
    simp only [if_neg hi, zero_mul, Finset.sum_const_zero, add_zero]

/-! ### QPrime -/

theorem data_qprime (d : CData) (hd : DataOK d) (st : ℕ → ℕ) {A R : ℕ} (hR : d.rw = R) :
    ∃ ents : Fin d.m → KerEntry d.N F,
      PreOK (fun (i : Fin A) (t : Fin d.N) => φ (blockM d.own d.os d.lane d.wl st i t))
        (fun (i : Fin R) (t : Fin d.N) => φ (colM d.round d.rw i t)) ents
        (fun (i : Fin R) (e : Fin d.m) => φ (rowM d.y d.m i e))
        (fun (i : Fin R) (t : Fin R) => φ (rowM d.tq d.rw i t)) := by
  obtain ⟨-, -, -, ⟨hE, hP⟩, -⟩ := hd
  refine ⟨fun e => entF φ d.ej d.es d.epo d.eco d.pidx d.coef d.N e (hE e e.2).1
    (fun p hp => ((hE e e.2).2.1 p hp).1), fun e i => ?_, fun i t => ?_⟩
  · rw [kcoord_map φ (blockM d.own d.os d.lane d.wl st), kco_blockM _ _ _ _ _ _ _ _ _ _ _ _ _
      (fun p hp => ((hE e e.2).2.1 p hp).2) (hE e e.2).2.2.1, map_zero]
  · have hc : ∀ e : Fin d.m, kcoord (fun (i : Fin R) (t : Fin d.N) => φ (colM d.round d.rw i t))
        (entF φ d.ej d.es d.epo d.eco d.pidx d.coef d.N e (hE e e.2).1
          (fun p hp => ((hE e e.2).2.1 p hp).1)) t = φ (d.rho (e * d.rw + t)) := by
      intro e
      rw [kcoord_map φ (colM d.round d.rw), kco_colM]
      exact congrArg φ ((hE e e.2).2.2.2.2 t (hR ▸ t.2))
    simp only [hc, rowM]
    have := hP i (hR ▸ i.2) t (hR ▸ t.2)
    simp only [zero_add] at this
    rw [← this, map_sum, ← Fin.sum_univ_eq_sum_range (fun p => φ (d.y (i * d.m + p) * d.rho (t + p * d.rw))) d.m]
    exact Finset.sum_congr rfl fun p _ => by rw [map_mul, add_comm (p.val * d.rw)]

end Field

#print axioms kcoord_map
#print axioms kco_blockM
#print axioms data_qprime

end R1Z.CertData
