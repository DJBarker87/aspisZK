import R1Z.CertOwnIdent

/-! D62 builder 3: the per-lane entry identifications that `CertOwnBlock`
consumes, from the extracted `fill_own` run (`own_hC`, `own_hE`). -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertBuild
open Aeneas Aeneas.Std Result R1Z.CertCheck R0P R0P.SemSource R1Z.RfChain R1Z.RfOwn R1Z.RfObs R1Z.RfSrc
open R0Z.K4 R0Z.HonestView AspisCircleTensorBinding R1Z.PredicateR1
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K} (B : PackBasis F) (φ : ZP →+* ↥F)

theorem own_val_c1 (al zz tr sx sy inact : Slice U32) {kk rr ll ii wb we : Usize} {v : U32}
    (hk : kk.val < 10) (hi : ii.val < wb.val)
    (h : R1CertBuild.own_val al zz tr sx sy inact kk rr ll ii wb we = ok v) :
    R1CertBuild.own_c1 al zz tr sx sy inact rr ii = ok v := by
  unfold R1CertBuild.own_val at h
  rw [if_pos (by rw [UScalar.lt_equiv]; simpa using hk), if_pos (by rw [UScalar.lt_equiv]; exact hi)] at h
  exact h

theorem own_val_h1 (al zz tr sx sy inact : Slice U32) {kk rr ll ii wb we : Usize} {v : U32}
    (hk : 10 ≤ kk.val) (hi : ii.val < we.val)
    (h : R1CertBuild.own_val al zz tr sx sy inact kk rr ll ii wb we = ok v) :
    R1CertBuild.h1_entry al zz tr sx sy inact rr ll ii = ok v := by
  unfold R1CertBuild.own_val at h
  rw [if_neg (by rw [UScalar.lt_equiv]; simp; omega), if_pos (by rw [UScalar.lt_equiv]; exact hi)] at h
  exact h

variable {Bat : Type} [BatchedLayer K Bat]

/-- The mask-lane entry identification of own column `t`. -/
theorem own_hC (hT : Tower B) (hB : PackField B) (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K)
    (l : List (Fin 262144)) (hq : ch.queries = l.toFinset)
    (al zz tr sx sy inact kind srow slimb : Slice U32)
    (ha : ∀ (j : ℕ) (h : j < 10), Alimb B φ al j = alpha ch ⟨j, h⟩)
    (hzx : ∀ j : Fin 2, Alimb B φ zz (2 * j.val) = (ch.circle j).1.1)
    (hzy : ∀ j : Fin 2, Alimb B φ zz (2 * j.val + 1) = (ch.circle j).1.2)
    (htr : ∀ r : Fin 1024, gN tr r.val = (π r).val)
    (hin : ∀ r : Fin 1024, gs inact r.val = if r ∈ copyInactiveRows then 1 else 0)
    (hsx : ∀ (m : ℕ) (hm : m < 4 * l.length), embR φ (gs sx m) =
      storedX (AspisV5ComponentCConcreteFoldLinearity.childIndex (l.get ⟨m / 4, by omega⟩) ⟨m % 4, by omega⟩))
    (hsy : ∀ (m : ℕ) (hm : m < 4 * l.length), embR φ (gs sy m) =
      storedY (AspisV5ComponentCConcreteFoldLinearity.childIndex (l.get ⟨m / 4, by omega⟩) ⟨m % 4, by omega⟩))
    {n os nq : Usize} {res : alloc.vec.Vec U32} (hnq : nq.val = l.length) (hos : 24 + 16 * l.length ≤ os.val)
    (hfill : R1CertBuild.fill_own al zz tr sx sy inact kind srow slimb n os nq = ok res)
    (t : ℕ) (ht : t < n.val) (hk : gNL kind t < 10) (r : Fin 1024) (hr : r ≠ 0) (hrow : gNL srow t = r.val)
    (c : Fin 29) (i : Fin (24 + 4 * l.length)) :
    flatC1 B hB l (obs (Bat := Bat) π B ch c (balWord 0 r 1)) i =
      φ (gs (alloc.vec.Vec.deref res) (t * os.val + i.val)) := by
  obtain ⟨kk, rr, ll, ii, wb, we, hkk, hrr, hll, hii, hwb, hwe, hval⟩ :=
    fill_own_spec al zz tr sx sy inact kind srow slimb hfill t ht i.val (by have := i.2; omega)
  have hc := own_val_c1 al zz tr sx sy inact (by rw [hkk]; exact hk) (by rw [hii, hwb, hnq]; exact i.2) hval
  exact own_c1_ident (Bat := Bat) B φ hT hB π ch c l hq al zz tr sx sy inact ha hzx hzy htr hin hsx hsy
    r hr rr ii (by rw [hrr, hrow]) i hii hc

/-- The G/D entry identification of own column `t`. -/
theorem own_hE (hT : Tower B) (hB : PackField B) (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K)
    (l : List (Fin 262144)) (hq : ch.queries = l.toFinset)
    (al zz tr sx sy inact kind srow slimb : Slice U32)
    (ha : ∀ (j : ℕ) (h : j < 10), Alimb B φ al j = alpha ch ⟨j, h⟩)
    (hzx : ∀ j : Fin 2, Alimb B φ zz (2 * j.val) = (ch.circle j).1.1)
    (hzy : ∀ j : Fin 2, Alimb B φ zz (2 * j.val + 1) = (ch.circle j).1.2)
    (htr : ∀ r : Fin 1024, gN tr r.val = (π r).val)
    (hin : ∀ r : Fin 1024, gs inact r.val = if r ∈ copyInactiveRows then 1 else 0)
    (hsx : ∀ (m : ℕ) (hm : m < 4 * l.length), embR φ (gs sx m) =
      storedX (AspisV5ComponentCConcreteFoldLinearity.childIndex (l.get ⟨m / 4, by omega⟩) ⟨m % 4, by omega⟩))
    (hsy : ∀ (m : ℕ) (hm : m < 4 * l.length), embR φ (gs sy m) =
      storedY (AspisV5ComponentCConcreteFoldLinearity.childIndex (l.get ⟨m / 4, by omega⟩) ⟨m % 4, by omega⟩))
    {n os nq : Usize} {res : alloc.vec.Vec U32} (hnq : nq.val = l.length) (hos : 24 + 16 * l.length ≤ os.val)
    (hfill : R1CertBuild.fill_own al zz tr sx sy inact kind srow slimb n os nq = ok res)
    (t : ℕ) (ht : t < n.val) (hk : 10 ≤ gNL kind t) (r : Fin 1024) (hr : r ≠ 0) (hrow : gNL srow t = r.val)
    (k : Fin 4) (hlimb : gNL slimb t = k.val) (c : Fin 29) (i : Fin (24 + 16 * l.length)) :
    flatH1 B hB l (obs (Bat := Bat) π B ch c (balWord 0 r (Mask.towerBasis B k))) i =
      φ (gs (alloc.vec.Vec.deref res) (t * os.val + i.val)) := by
  obtain ⟨kk, rr, ll, ii, wb, we, hkk, hrr, hll, hii, hwb, hwe, hval⟩ :=
    fill_own_spec al zz tr sx sy inact kind srow slimb hfill t ht i.val (by have := i.2; omega)
  have hc := own_val_h1 al zz tr sx sy inact (by rw [hkk]; exact hk) (by rw [hii, hwe, hnq]; exact i.2) hval
  exact own_h1_ident (Bat := Bat) B φ hT hB π ch c l hq al zz tr sx sy inact ha hzx hzy htr hin hsx hsy
    r hr k rr ll ii (by rw [hrr, hrow]) (by rw [hll, hlimb]) i hii hc

#print axioms own_hC
#print axioms own_hE

end R1Z.CertBuild
