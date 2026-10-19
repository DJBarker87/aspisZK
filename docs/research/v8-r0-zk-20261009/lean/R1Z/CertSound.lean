import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! D38.5 (zf1/DESIGN-P-CERT.txt §2.3 (C1), §5): generic soundness of the
P_R1 certificate checker.  Payload-free linear algebra over an arbitrary
field `F`; vectors are `Fin n → F`, matrices `Fin a → Fin b → F`
(row index first), and every check is a decidable Prop whose `decide` is the
Boolean checker.

* `pre_sound`, `pre_sound₂`, `span_sound`: a two-level preimage certificate
  (kernel entries over a pivot list, then a combination matrix) gives
  membership of each target in `(G ⊓ ker z).map g` (resp. with two zero maps).
  Used for QPrime_R1 (z = own, g = round) and V_G (z₁ = own, z₂ = round,
  g = bat, G = Gonly).
* `ech_sound`, `bcond_sound`: `E = U·Rel` in reduced echelon form on a
  pivot/free partition gives `ker Rel ≤ span {n_f}`; with preimages of the
  `n_f` this is `B0 ≤ V` (BCondG_R1).  No inverse of `U` is needed.
* `rinv_sound`: a right inverse `O·U = 1` of the selected observation
  columns gives `range ι ≤ V.map obs` (C1Lift, H1Lift).
* `half_sound`, `card_sound`: HalfOK, QueryCard.
* `kcoord_offblock`: the lane-local kernel check implies the full one when the
  coordinate matrix is block-diagonal (the Rust checker only tests the block).

The correspondence of the coordinate matrices with the R1 maps (the D34.3
row-formula items RF-own, RF-round, RF-bat, RF-src, RF-chain, RF-rel, RF-obs)
enters only as hypotheses `hz`, `hg`, `hG`, `hS`, `hrel` of these theorems. -/

set_option autoImplicit false

namespace R1Z.CertSound

open scoped BigOperators

/-- A kernel entry: source `j` plus a combination of `s` pivot sources. -/
structure KerEntry (N : ℕ) (F : Type*) where
  s : ℕ
  j : Fin N
  piv : Fin s → Fin N
  c : Fin s → F

variable {F : Type*} [Field F]

/-- Column `t` of a matrix. -/
def col {a N : ℕ} (A : Fin a → Fin N → F) (t : Fin N) : Fin a → F := fun i => A i t

/-- Coordinates of a kernel entry, as the Rust checker computes them:
`A[i][j] + dot(A[i][piv], c)`. -/
def kcoord {a N : ℕ} (A : Fin a → Fin N → F) (e : KerEntry N F) (i : Fin a) : F :=
  A i e.j + ∑ p, A i (e.piv p) * e.c p

section Pre

variable {M Y Y₂ Z : Type*} [AddCommGroup M] [Module F M] [AddCommGroup Y] [Module F Y]
  [AddCommGroup Y₂] [Module F Y₂] [AddCommGroup Z] [Module F Z]

/-- The tape of a kernel entry. -/
def kvec {N : ℕ} (src : Fin N → M) (e : KerEntry N F) : M :=
  src e.j + ∑ p, e.c p • src (e.piv p)

theorem kcoord_eq {a N : ℕ} (A : Fin a → Fin N → F) (e : KerEntry N F) :
    kcoord A e = col A e.j + ∑ p, e.c p • col A (e.piv p) := by
  funext i
  simp only [kcoord, col, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

/-- Row-formula transport: a map whose values on the sources have
coordinates `A` sends a kernel entry's tape to its coordinates. -/
theorem map_kvec {a N : ℕ} {W : Type*} [AddCommGroup W] [Module F W] (f : M →ₗ[F] W)
    (ι : (Fin a → F) →ₗ[F] W) (src : Fin N → M) (A : Fin a → Fin N → F)
    (hA : ∀ t, f (src t) = ι (col A t)) (e : KerEntry N F) :
    f (kvec src e) = ι (kcoord A e) := by
  rw [kcoord_eq, map_add, map_sum, kvec, map_add, map_sum, hA]
  congr 1
  exact Finset.sum_congr rfl fun p _ => by rw [map_smul, map_smul, hA]

theorem kvec_mem {N : ℕ} (G : Submodule F M) (src : Fin N → M) (hG : ∀ t, src t ∈ G)
    (e : KerEntry N F) : kvec src e ∈ G :=
  G.add_mem (hG _) (sum_mem fun p _ => G.smul_mem _ (hG _))

/-- The preimage certificate: kernel entries with zero `Zc`-coordinates and a
combination matrix sending their `Gc`-coordinates to the targets. -/
def PreOK {a b N m n : ℕ} (Zc : Fin a → Fin N → F) (Gc : Fin b → Fin N → F)
    (ents : Fin m → KerEntry N F) (Yc : Fin n → Fin m → F) (T : Fin n → Fin b → F) : Prop :=
  (∀ e i, kcoord Zc (ents e) i = 0) ∧ (∀ i t, ∑ e, Yc i e * kcoord Gc (ents e) t = T i t)

/-- The same with two zero maps (V_G: own and round). -/
def PreOK₂ {a₁ a₂ b N m n : ℕ} (Z₁ : Fin a₁ → Fin N → F) (Z₂ : Fin a₂ → Fin N → F)
    (Gc : Fin b → Fin N → F) (ents : Fin m → KerEntry N F) (Yc : Fin n → Fin m → F)
    (T : Fin n → Fin b → F) : Prop :=
  (∀ e i, kcoord Z₁ (ents e) i = 0) ∧ (∀ e i, kcoord Z₂ (ents e) i = 0) ∧
    (∀ i t, ∑ e, Yc i e * kcoord Gc (ents e) t = T i t)

theorem target_eq {b N m n : ℕ} (Gc : Fin b → Fin N → F) (ents : Fin m → KerEntry N F)
    (Yc : Fin n → Fin m → F) (T : Fin n → Fin b → F)
    (h : ∀ i t, ∑ e, Yc i e * kcoord Gc (ents e) t = T i t) (i : Fin n) :
    T i = ∑ e, Yc i e • kcoord Gc (ents e) := by
  funext t
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact (h i t).symm

theorem zero_of_kcoord {a N : ℕ} (A : Fin a → Fin N → F) (e : KerEntry N F)
    (h : ∀ i, kcoord A e i = 0) : kcoord A e = 0 := funext h

/-- Preimage soundness, one zero map. -/
theorem pre_sound {a b N m n : ℕ} (G : Submodule F M) (z : M →ₗ[F] Y) (g : M →ₗ[F] Z)
    (ιz : (Fin a → F) →ₗ[F] Y) (ιg : (Fin b → F) →ₗ[F] Z)
    (src : Fin N → M) (hG : ∀ t, src t ∈ G)
    (Zc : Fin a → Fin N → F) (Gc : Fin b → Fin N → F)
    (hz : ∀ t, z (src t) = ιz (col Zc t)) (hg : ∀ t, g (src t) = ιg (col Gc t))
    (ents : Fin m → KerEntry N F) (Yc : Fin n → Fin m → F) (T : Fin n → Fin b → F)
    (h : PreOK Zc Gc ents Yc T) (i : Fin n) :
    ιg (T i) ∈ (G ⊓ LinearMap.ker z).map g := by
  refine Submodule.mem_map.2 ⟨∑ e, Yc i e • kvec src (ents e), ?_, ?_⟩
  · refine Submodule.mem_inf.2 ⟨sum_mem fun e _ => G.smul_mem _ (kvec_mem G src hG _), ?_⟩
    rw [LinearMap.mem_ker, map_sum]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [map_smul, map_kvec z ιz src Zc hz, zero_of_kcoord Zc _ (h.1 e), map_zero, smul_zero]
  · rw [map_sum, target_eq Gc ents Yc T h.2 i, map_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [map_smul, map_smul, map_kvec g ιg src Gc hg]

/-- Preimage soundness, two zero maps: membership in `(G ⊓ ker z₂ ⊓ ker z₁).map g`
(the parenthesisation of `V_G`). -/
theorem pre_sound₂ {a₁ a₂ b N m n : ℕ} (G : Submodule F M) (z₁ : M →ₗ[F] Y)
    (z₂ : M →ₗ[F] Y₂) (g : M →ₗ[F] Z)
    (ι₁ : (Fin a₁ → F) →ₗ[F] Y) (ι₂ : (Fin a₂ → F) →ₗ[F] Y₂) (ιg : (Fin b → F) →ₗ[F] Z)
    (src : Fin N → M) (hG : ∀ t, src t ∈ G)
    (Z₁ : Fin a₁ → Fin N → F) (Z₂ : Fin a₂ → Fin N → F) (Gc : Fin b → Fin N → F)
    (h₁ : ∀ t, z₁ (src t) = ι₁ (col Z₁ t)) (h₂ : ∀ t, z₂ (src t) = ι₂ (col Z₂ t))
    (hg : ∀ t, g (src t) = ιg (col Gc t))
    (ents : Fin m → KerEntry N F) (Yc : Fin n → Fin m → F) (T : Fin n → Fin b → F)
    (h : PreOK₂ Z₁ Z₂ Gc ents Yc T) (i : Fin n) :
    ιg (T i) ∈ (G ⊓ LinearMap.ker z₂ ⊓ LinearMap.ker z₁).map g := by
  obtain ⟨hk₁, hk₂, hy⟩ := h
  refine Submodule.mem_map.2 ⟨∑ e, Yc i e • kvec src (ents e), ?_, ?_⟩
  · refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2
      ⟨sum_mem fun e _ => G.smul_mem _ (kvec_mem G src hG _), ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker, map_sum]
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [map_smul, map_kvec z₂ ι₂ src Z₂ h₂, zero_of_kcoord Z₂ _ (hk₂ e), map_zero, smul_zero]
    · rw [LinearMap.mem_ker, map_sum]
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [map_smul, map_kvec z₁ ι₁ src Z₁ h₁, zero_of_kcoord Z₁ _ (hk₁ e), map_zero, smul_zero]
  · rw [map_sum, target_eq Gc ents Yc T hy i, map_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [map_smul, map_smul, map_kvec g ιg src Gc hg]

/-- A submodule spanned by (or inside the span of) the certified targets is
inside the certified image (QPrime_R1 with RF-chain as `hS`). -/
theorem span_sound {a b N m n : ℕ} (G : Submodule F M) (z : M →ₗ[F] Y) (g : M →ₗ[F] Z)
    (ιz : (Fin a → F) →ₗ[F] Y) (ιg : (Fin b → F) →ₗ[F] Z)
    (src : Fin N → M) (hG : ∀ t, src t ∈ G)
    (Zc : Fin a → Fin N → F) (Gc : Fin b → Fin N → F)
    (hz : ∀ t, z (src t) = ιz (col Zc t)) (hg : ∀ t, g (src t) = ιg (col Gc t))
    (ents : Fin m → KerEntry N F) (Yc : Fin n → Fin m → F) (T : Fin n → Fin b → F)
    (S : Submodule F Z) (hS : S ≤ Submodule.span F (Set.range fun i => ιg (T i)))
    (h : PreOK Zc Gc ents Yc T) :
    S ≤ (G ⊓ LinearMap.ker z).map g := by
  refine hS.trans (Submodule.span_le.2 ?_)
  rintro _ ⟨i, rfl⟩
  exact pre_sound G z g ιz ιg src hG Zc Gc hz hg ents Yc T h i

/-- The Rust checker tests a kernel entry only on its lane's block; for a
block-diagonal coordinate matrix the other coordinates vanish. -/
theorem kcoord_offblock {a N L : ℕ} (A : Fin a → Fin N → F) (blk : Fin a → Fin L)
    (lane : Fin N → Fin L) (hA : ∀ i t, blk i ≠ lane t → A i t = 0) (e : KerEntry N F)
    (hj : ∀ p, lane (e.piv p) = lane e.j) (i : Fin a) (hi : blk i ≠ lane e.j) :
    kcoord A e i = 0 := by
  rw [kcoord, hA i e.j hi, zero_add]
  exact Finset.sum_eq_zero fun p _ => by rw [hA i (e.piv p) (by rw [hj p]; exact hi), zero_mul]

end Pre

/-! ## Echelon certificate (BCondG_R1) -/

section Ech

variable {q n r k : ℕ}

/-- `E = U · Rel`, computed by the checker. -/
def Emat (U : Fin r → Fin q → F) (Rel : Fin q → Fin n → F) (a : Fin r) (c : Fin n) : F :=
  ∑ x, U a x * Rel x c

/-- The kernel generator of a free column. -/
def nvec (E : Fin r → Fin n → F) (piv : Fin r → Fin n) (fr : Fin k → Fin n) (f : Fin k)
    (c : Fin n) : F :=
  (if c = fr f then 1 else 0) - ∑ a, E a (fr f) * (if c = piv a then 1 else 0)

/-- Reduced echelon form on `piv`, and `piv`/`fr` a partition of the columns. -/
def EchOK (E : Fin r → Fin n → F) (piv : Fin r → Fin n) (fr : Fin k → Fin n) : Prop :=
  (∀ a b, E a (piv b) = if a = b then 1 else 0) ∧
    (∀ f g, fr f = fr g → f = g) ∧ (∀ a f, piv a ≠ fr f) ∧
    (∀ c, (∃ a, piv a = c) ∨ (∃ f, fr f = c))

theorem piv_inj {E : Fin r → Fin n → F} {piv : Fin r → Fin n}
    (hE : ∀ a b, E a (piv b) = if a = b then 1 else 0) : Function.Injective piv := by
  intro a b h
  have h1 := hE a b
  rw [← h, hE a a, if_pos rfl] at h1
  by_contra hab
  rw [if_neg hab] at h1
  exact one_ne_zero h1

theorem sum_split (piv : Fin r → Fin n) (fr : Fin k → Fin n) (hpi : Function.Injective piv)
    (hfr : Function.Injective fr) (hd : ∀ a f, piv a ≠ fr f)
    (hc : ∀ c, (∃ a, piv a = c) ∨ (∃ f, fr f = c)) (φ : Fin n → F) :
    ∑ c, φ c = ∑ a, φ (piv a) + ∑ f, φ (fr f) := by
  have hU : (Finset.univ : Finset (Fin n)) = Finset.univ.image piv ∪ Finset.univ.image fr := by
    ext c
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_image, true_and, true_iff]
    exact hc c
  have hD : Disjoint (Finset.univ.image piv) (Finset.univ.image fr) := by
    rw [Finset.disjoint_left]
    intro c ha hb
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨f, hf⟩ := hb
    exact hd a f hf.symm
  have i1 : Set.InjOn piv (Finset.univ : Finset (Fin r)) := by
    intro x _ y _ h
    exact hpi h
  have i2 : Set.InjOn fr (Finset.univ : Finset (Fin k)) := by
    intro x _ y _ h
    exact hfr h
  rw [hU, Finset.sum_union hD, Finset.sum_image i1, Finset.sum_image i2]

/-- Echelon soundness: every vector killed by `Rel` is the combination of the
`n_f` with its free coordinates. -/
theorem ech_sound (U : Fin r → Fin q → F) (Rel : Fin q → Fin n → F) (piv : Fin r → Fin n)
    (fr : Fin k → Fin n) (h : EchOK (Emat U Rel) piv fr) (v : Fin n → F)
    (hv : ∀ x, ∑ c, Rel x c * v c = 0) :
    v = ∑ f, v (fr f) • nvec (Emat U Rel) piv fr f := by
  obtain ⟨hE, hfr, hd, hc⟩ := h
  have hpi := piv_inj hE
  have hfr' : Function.Injective fr := by
    intro a b hab
    exact hfr a b hab
  have hEv : ∀ a, ∑ c, Emat U Rel a c * v c = 0 := by
    intro a
    have e1 : ∀ c, Emat U Rel a c * v c = ∑ x, U a x * (Rel x c * v c) := by
      intro c
      rw [Emat, Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => mul_assoc _ _ _
    rw [Finset.sum_congr rfl fun c _ => e1 c, Finset.sum_comm]
    exact Finset.sum_eq_zero fun x _ => by rw [← Finset.mul_sum, hv x, mul_zero]
  funext c
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, nvec]
  rcases hc c with ⟨a0, rfl⟩ | ⟨f0, rfl⟩
  · have hsplit : ∑ c, Emat U Rel a0 c * v c =
        ∑ a, Emat U Rel a0 (piv a) * v (piv a) + ∑ f, Emat U Rel a0 (fr f) * v (fr f) :=
      sum_split piv fr hpi hfr' hd hc _
    rw [hEv a0] at hsplit
    simp only [hE, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true] at hsplit
    have hfr0 : ∀ f, (if piv a0 = fr f then (1 : F) else 0) = 0 := fun f => if_neg (hd a0 f)
    have hpp : ∀ f, ∑ a, Emat U Rel a (fr f) * (if piv a0 = piv a then (1 : F) else 0) =
        Emat U Rel a0 (fr f) := by
      intro f
      simp only [hpi.eq_iff, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
        if_true]
    simp only [hfr0, hpp, zero_sub, mul_neg, Finset.sum_neg_distrib]
    have hcomm : ∑ f, v (fr f) * Emat U Rel a0 (fr f) = ∑ f, Emat U Rel a0 (fr f) * v (fr f) :=
      Finset.sum_congr rfl fun f _ => mul_comm _ _
    rw [hcomm]
    linear_combination -hsplit
  · have hz : ∀ a, (if fr f0 = piv a then (1 : F) else 0) = 0 :=
      fun a => if_neg fun h => hd a f0 h.symm
    simp only [hz, mul_zero, Finset.sum_const_zero, sub_zero, hfr'.eq_iff, mul_ite, mul_one,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- BCondG_R1 shape: with `B0 ≤ ιb(ker Rel)` (RF-rel) and every `ιb n_f ∈ V`,
`B0 ≤ V`. -/
theorem bcond_sound {Z : Type*} [AddCommGroup Z] [Module F Z] (U : Fin r → Fin q → F)
    (Rel : Fin q → Fin n → F) (piv : Fin r → Fin n) (fr : Fin k → Fin n)
    (ιb : (Fin n → F) →ₗ[F] Z) (B0 V : Submodule F Z)
    (hrel : ∀ x ∈ B0, ∃ v : Fin n → F, (∀ y, ∑ c, Rel y c * v c = 0) ∧ ιb v = x)
    (h : EchOK (Emat U Rel) piv fr) (hn : ∀ f, ιb (nvec (Emat U Rel) piv fr f) ∈ V) :
    B0 ≤ V := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := hrel x hx
  rw [ech_sound U Rel piv fr h v hv, map_sum]
  exact sum_mem fun f _ => by rw [map_smul]; exact V.smul_mem _ (hn f)

end Ech

/-! ## Right-inverse certificate (C1Lift, H1Lift) -/

section Rinv

variable {M Y : Type*} [AddCommGroup M] [Module F M] [AddCommGroup Y] [Module F Y]

/-- `O · U = 1`. -/
def RinvOK {w : ℕ} (O U : Fin w → Fin w → F) : Prop :=
  ∀ i j, ∑ x, O i x * U x j = if i = j then 1 else 0

theorem rinv_sound {w : ℕ} (V : Submodule F M) (obs : M →ₗ[F] Y) (ι : (Fin w → F) →ₗ[F] Y)
    (src : Fin w → M) (hV : ∀ t, src t ∈ V) (O : Fin w → Fin w → F)
    (hO : ∀ t, obs (src t) = ι (col O t)) (U : Fin w → Fin w → F) (h : RinvOK O U) :
    LinearMap.range ι ≤ V.map obs := by
  have h' : ∀ i j, ∑ x, O i x * U x j = if i = j then 1 else 0 := h
  rintro _ ⟨t, rfl⟩
  refine Submodule.mem_map.2
    ⟨∑ x, (∑ j, U x j * t j) • src x, sum_mem fun x _ => V.smul_mem _ (hV x), ?_⟩
  have ht : t = ∑ x, (∑ j, U x j * t j) • col O x := by
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, col]
    calc t i = ∑ j, (if i = j then (1 : F) else 0) * t j := by
            simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      _ = ∑ j, (∑ x, O i x * U x j) * t j := by simp only [h']
      _ = ∑ x, (∑ j, U x j * t j) * O i x := by
          simp only [Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => by ring
  rw [map_sum]
  calc ∑ x, obs ((∑ j, U x j * t j) • src x) = ∑ x, ι ((∑ j, U x j * t j) • col O x) :=
        Finset.sum_congr rfl fun x _ => by rw [map_smul, map_smul, hO]
    _ = ι (∑ x, (∑ j, U x j * t j) • col O x) := (map_sum ι _ _).symm
    _ = ι t := by rw [← ht]

/-- The lift shape: with `W.map obs ≤ range ι` (RF-obs), `W.map obs ≤ V.map obs`. -/
theorem lift_sound {w : ℕ} (W V : Submodule F M) (obs : M →ₗ[F] Y) (ι : (Fin w → F) →ₗ[F] Y)
    (hW : W.map obs ≤ LinearMap.range ι)
    (src : Fin w → M) (hV : ∀ t, src t ∈ V) (O : Fin w → Fin w → F)
    (hO : ∀ t, obs (src t) = ι (col O t)) (U : Fin w → Fin w → F) (h : RinvOK O U) :
    W.map obs ≤ V.map obs :=
  hW.trans (rinv_sound V obs ι src hV O hO U h)

end Rinv

/-! ## Field and length facts -/

theorem half_sound {K : Type*} [Field K] (x h y : K) (hy : (x - h) * y = 1) : x ≠ h := by
  intro hx
  rw [hx, sub_self, zero_mul] at hy
  exact zero_ne_one hy

theorem card_sound {α : Type*} [DecidableEq α] (l : List α) (hl : l.length ≤ 22) :
    l.toFinset.card ≤ 22 :=
  (List.toFinset_card_le (l := l)).trans hl

/-! ## The Boolean checkers -/

section Bool

variable [DecidableEq F]

instance decPreOK {a b N m n : ℕ} (Zc : Fin a → Fin N → F) (Gc : Fin b → Fin N → F)
    (ents : Fin m → KerEntry N F) (Yc : Fin n → Fin m → F) (T : Fin n → Fin b → F) :
    Decidable (PreOK Zc Gc ents Yc T) := by
  unfold PreOK; infer_instance

instance decPreOK₂ {a₁ a₂ b N m n : ℕ} (Z₁ : Fin a₁ → Fin N → F) (Z₂ : Fin a₂ → Fin N → F)
    (Gc : Fin b → Fin N → F) (ents : Fin m → KerEntry N F) (Yc : Fin n → Fin m → F)
    (T : Fin n → Fin b → F) : Decidable (PreOK₂ Z₁ Z₂ Gc ents Yc T) := by
  unfold PreOK₂; infer_instance

instance decEchOK {n r k : ℕ} (E : Fin r → Fin n → F) (piv : Fin r → Fin n)
    (fr : Fin k → Fin n) : Decidable (EchOK E piv fr) := by
  unfold EchOK; infer_instance

instance decRinvOK {w : ℕ} (O U : Fin w → Fin w → F) : Decidable (RinvOK O U) := by
  unfold RinvOK; infer_instance

/-- The Boolean checkers are `decide` of the certificate Props, so a `true`
result gives the Prop. -/
theorem preCheck_sound {a b N m n : ℕ} {Zc : Fin a → Fin N → F} {Gc : Fin b → Fin N → F}
    {ents : Fin m → KerEntry N F} {Yc : Fin n → Fin m → F} {T : Fin n → Fin b → F}
    (h : decide (PreOK Zc Gc ents Yc T) = true) : PreOK Zc Gc ents Yc T :=
  of_decide_eq_true h

theorem preCheck₂_sound {a₁ a₂ b N m n : ℕ} {Z₁ : Fin a₁ → Fin N → F}
    {Z₂ : Fin a₂ → Fin N → F} {Gc : Fin b → Fin N → F} {ents : Fin m → KerEntry N F}
    {Yc : Fin n → Fin m → F} {T : Fin n → Fin b → F}
    (h : decide (PreOK₂ Z₁ Z₂ Gc ents Yc T) = true) : PreOK₂ Z₁ Z₂ Gc ents Yc T :=
  of_decide_eq_true h

theorem echCheck_sound {n r k : ℕ} {E : Fin r → Fin n → F} {piv : Fin r → Fin n}
    {fr : Fin k → Fin n} (h : decide (EchOK E piv fr) = true) : EchOK E piv fr :=
  of_decide_eq_true h

theorem rinvCheck_sound {w : ℕ} {O U : Fin w → Fin w → F}
    (h : decide (RinvOK O U) = true) : RinvOK O U :=
  of_decide_eq_true h

end Bool

#print axioms kcoord_eq
#print axioms map_kvec
#print axioms kvec_mem
#print axioms target_eq
#print axioms pre_sound
#print axioms pre_sound₂
#print axioms span_sound
#print axioms kcoord_offblock
#print axioms piv_inj
#print axioms sum_split
#print axioms ech_sound
#print axioms bcond_sound
#print axioms rinv_sound
#print axioms lift_sound
#print axioms half_sound
#print axioms card_sound
#print axioms preCheck_sound
#print axioms preCheck₂_sound
#print axioms echCheck_sound
#print axioms rinvCheck_sound

end R1Z.CertSound
