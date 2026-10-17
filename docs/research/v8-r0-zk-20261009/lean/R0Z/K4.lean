import R0P.CoreExt
import R0P.MaskValue
import R0Z.PureRounds

/-! J1 (T2b-2b design §1.1, §1.2, §5): the packing subfields `K₂ = F(i)` and
`K₄ = F(i, u)`, the prefix spans `Λ_j`, the quadratic-subfield lemma, and
`Good₃ → Λ_j = K₄` for `j ≥ 4`.

Payload-generic part: everything up to `lambda4_eq_K4` uses only a finite field
`K`, a subfield `F`, a packing basis and the closure premise `PackField`.  The
only protocol objects are `eqPrefix` (the multilinear prefix weight of
PureRounds) and, in `Good3`, the R0 challenge record (`alpha`, `sem`, `Good`).
No concrete row set is enumerated; `Λ_j` is a span over the symbolic range of
`eqPrefix`, and every row used below is built as `rowOf` of an updated bit
vector. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.K4
open R0P R0P.SemDegree R0Z.HonestView

section Field
variable {K : Type} [Field K] [Fintype K] {F : Subfield K}

/-! ### The closure premise and the two subfields -/

/-- The packing basis spans a field: `i² ∈ F` and `u² ∈ F + F·i`.  For the
QM31 tower `i² = −1`, `u² = 2 + i`; a refinement fact of the concrete basis. -/
def PackField (B : PackBasis F) : Prop :=
  B.i * B.i ∈ F ∧ ∃ a b : K, a ∈ F ∧ b ∈ F ∧ B.u * B.u = a + B.i * b

/-- Scalar action of the base subfield is multiplication. -/
theorem fsmul_eq (c : F) (x : K) : c • x = (c : K) * x := rfl

/-- In a finite field every subring is closed under inversion. -/
theorem inv_mem_of_subring (S : Subring K) {x : K} (hx : x ∈ S) : x⁻¹ ∈ S := by
  by_cases h0 : x = 0
  · rw [h0, inv_zero]
    exact S.zero_mem
  · have hc : 1 < Fintype.card K := Fintype.one_lt_card
    have hm : x * x ^ (Fintype.card K - 2) = 1 := by
      calc x * x ^ (Fintype.card K - 2) = x ^ (Fintype.card K - 2 + 1) := (pow_succ' x _).symm
        _ = x ^ (Fintype.card K - 1) := by congr 1; omega
        _ = 1 := FiniteField.pow_card_sub_one_eq_one x h0
    rw [inv_eq_of_mul_eq_one_right hm]
    exact pow_mem hx _

/-- A subring of a finite field, as a subfield. -/
def subfieldOfSubring (S : Subring K) : Subfield K :=
  { S with inv_mem' := fun _ hx => inv_mem_of_subring S hx }

/-- `F + F·i` as a subring. -/
def K2Subring (B : PackBasis F) (hB : PackField B) : Subring K where
  carrier := {x | ∃ a ∈ F, ∃ b ∈ F, x = a + B.i * b}
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
    exact ⟨a * c + (B.i * B.i) * (b * d),
      F.add_mem (F.mul_mem ha hc) (F.mul_mem hB.1 (F.mul_mem hb hd)),
      a * d + b * c, F.add_mem (F.mul_mem ha hd) (F.mul_mem hb hc), by ring⟩
  one_mem' := ⟨1, F.one_mem, 0, F.zero_mem, by ring⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
    exact ⟨a + c, F.add_mem ha hc, b + d, F.add_mem hb hd, by ring⟩
  zero_mem' := ⟨0, F.zero_mem, 0, F.zero_mem, by ring⟩
  neg_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨-a, F.neg_mem ha, -b, F.neg_mem hb, by ring⟩

/-- `K₂ = F(i)`. -/
def K2 (B : PackBasis F) (hB : PackField B) : Subfield K :=
  subfieldOfSubring (K2Subring B hB)

theorem mem_K2 (B : PackBasis F) (hB : PackField B) {x : K} :
    x ∈ K2 B hB ↔ ∃ a ∈ F, ∃ b ∈ F, x = a + B.i * b := Iff.rfl

theorem F_le_K2 (B : PackBasis F) (hB : PackField B) {x : K} (hx : x ∈ F) :
    x ∈ K2 B hB :=
  (mem_K2 B hB).2 ⟨x, hx, 0, F.zero_mem, by ring⟩

theorem i_mem_K2 (B : PackBasis F) (hB : PackField B) : B.i ∈ K2 B hB :=
  (mem_K2 B hB).2 ⟨0, F.zero_mem, 1, F.one_mem, by ring⟩

theorem uu_mem_K2 (B : PackBasis F) (hB : PackField B) : B.u * B.u ∈ K2 B hB := by
  obtain ⟨a, b, ha, hb, h⟩ := hB.2
  exact (mem_K2 B hB).2 ⟨a, ha, b, hb, h⟩

/-- `K₂ + u·K₂` as a subring. -/
def K4Subring (B : PackBasis F) (hB : PackField B) : Subring K where
  carrier := {x | ∃ A ∈ K2 B hB, ∃ C ∈ K2 B hB, x = A + B.u * C}
  mul_mem' := by
    rintro _ _ ⟨A, hA, C, hC, rfl⟩ ⟨A', hA', C', hC', rfl⟩
    exact ⟨A * A' + (B.u * B.u) * (C * C'),
      (K2 B hB).add_mem ((K2 B hB).mul_mem hA hA')
        ((K2 B hB).mul_mem (uu_mem_K2 B hB) ((K2 B hB).mul_mem hC hC')),
      A * C' + C * A',
      (K2 B hB).add_mem ((K2 B hB).mul_mem hA hC') ((K2 B hB).mul_mem hC hA'), by ring⟩
  one_mem' := ⟨1, (K2 B hB).one_mem, 0, (K2 B hB).zero_mem, by ring⟩
  add_mem' := by
    rintro _ _ ⟨A, hA, C, hC, rfl⟩ ⟨A', hA', C', hC', rfl⟩
    exact ⟨A + A', (K2 B hB).add_mem hA hA', C + C', (K2 B hB).add_mem hC hC', by ring⟩
  zero_mem' := ⟨0, (K2 B hB).zero_mem, 0, (K2 B hB).zero_mem, by ring⟩
  neg_mem' := by
    rintro _ ⟨A, hA, C, hC, rfl⟩
    exact ⟨-A, (K2 B hB).neg_mem hA, -C, (K2 B hB).neg_mem hC, by ring⟩

/-- `K₄ = F(i, u)`. -/
def K4 (B : PackBasis F) (hB : PackField B) : Subfield K :=
  subfieldOfSubring (K4Subring B hB)

theorem mem_K4_iff_K2 (B : PackBasis F) (hB : PackField B) {x : K} :
    x ∈ K4 B hB ↔ ∃ A ∈ K2 B hB, ∃ C ∈ K2 B hB, x = A + B.u * C := Iff.rfl

/-- The carrier characterisation through `pack4` used by every word lemma. -/
theorem mem_K4_iff_pack4 (B : PackBasis F) (hB : PackField B) {x : K} :
    x ∈ K4 B hB ↔ ∃ v : Fin 4 → K, (∀ j, v j ∈ F) ∧ x = pack4 B v := by
  rw [mem_K4_iff_K2]
  constructor
  · rintro ⟨A, hA, C, hC, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_K2 B hB).1 hA
    obtain ⟨c, hc, d, hd, rfl⟩ := (mem_K2 B hB).1 hC
    let v : Fin 4 → K := fun j =>
      if j.val = 0 then a else if j.val = 1 then b else if j.val = 2 then c else d
    refine ⟨v, ?_, ?_⟩
    · intro j
      simp only [v]
      split_ifs
      · exact ha
      · exact hb
      · exact hc
      · exact hd
    · have h0 : v 0 = a := rfl
      have h1 : v 1 = b := rfl
      have h2 : v 2 = c := rfl
      have h3 : v 3 = d := rfl
      unfold pack4
      rw [h0, h1, h2, h3]
      ring
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v 0 + B.i * v 1, (mem_K2 B hB).2 ⟨v 0, hv 0, v 1, hv 1, rfl⟩,
      v 2 + B.i * v 3, (mem_K2 B hB).2 ⟨v 2, hv 2, v 3, hv 3, rfl⟩, ?_⟩
    unfold pack4
    ring

theorem K2_le_K4 (B : PackBasis F) (hB : PackField B) : K2 B hB ≤ K4 B hB :=
  fun x hx => (mem_K4_iff_K2 B hB).2 ⟨x, hx, 0, (K2 B hB).zero_mem, by ring⟩

theorem F_le_K4 (B : PackBasis F) (hB : PackField B) {x : K} (hx : x ∈ F) :
    x ∈ K4 B hB :=
  K2_le_K4 B hB (F_le_K2 B hB hx)

theorem u_mem_K4 (B : PackBasis F) (hB : PackField B) : B.u ∈ K4 B hB :=
  (mem_K4_iff_K2 B hB).2 ⟨0, (K2 B hB).zero_mem, 1, (K2 B hB).one_mem, by ring⟩

theorem i_mem_K4 (B : PackBasis F) (hB : PackField B) : B.i ∈ K4 B hB :=
  K2_le_K4 B hB (i_mem_K2 B hB)

theorem pack4_mem_K4 (B : PackBasis F) (hB : PackField B) (v : Fin 4 → K)
    (hv : ∀ j, v j ∈ F) : pack4 B v ∈ K4 B hB :=
  (mem_K4_iff_pack4 B hB).2 ⟨v, hv, rfl⟩

theorem towerBasis_mem_K4 (B : PackBasis F) (hB : PackField B) (j : Fin 4) :
    R0P.Mask.towerBasis B j ∈ K4 B hB := by
  unfold R0P.Mask.towerBasis
  split_ifs
  · exact (K4 B hB).one_mem
  · exact i_mem_K4 B hB
  · exact u_mem_K4 B hB
  · exact (K4 B hB).mul_mem (i_mem_K4 B hB) (u_mem_K4 B hB)

theorem natCast_mem_K4 (B : PackBasis F) (hB : PackField B) (n : ℕ) :
    (n : K) ∈ K4 B hB :=
  natCast_mem (K4 B hB) n

theorem half_mem_K4 (B : PackBasis F) (hB : PackField B) : (1 / 2 : K) ∈ K4 B hB := by
  have h2 : (2 : K) ∈ K4 B hB := by
    have h := natCast_mem_K4 B hB 2
    simpa using h
  exact (K4 B hB).div_mem (K4 B hB).one_mem h2

/-! ### F-dimensions -/

/-- `K₄` as an `F`-subspace of `K` (same carrier). -/
def K4F (B : PackBasis F) (hB : PackField B) : Submodule F K where
  carrier := (K4 B hB : Set K)
  add_mem' := fun ha hb => (K4 B hB).add_mem ha hb
  zero_mem' := (K4 B hB).zero_mem
  smul_mem' := fun c x hx => by
    rw [fsmul_eq]
    exact (K4 B hB).mul_mem (F_le_K4 B hB c.2) hx

theorem mem_K4F (B : PackBasis F) (hB : PackField B) {x : K} :
    x ∈ K4F B hB ↔ x ∈ K4 B hB := Iff.rfl

/-- `K₂` as an `F`-subspace of `K`. -/
def K2F (B : PackBasis F) (hB : PackField B) : Submodule F K where
  carrier := (K2 B hB : Set K)
  add_mem' := fun ha hb => (K2 B hB).add_mem ha hb
  zero_mem' := (K2 B hB).zero_mem
  smul_mem' := fun c x hx => by
    rw [fsmul_eq]
    exact (K2 B hB).mul_mem (F_le_K2 B hB c.2) hx

theorem mem_K2F (B : PackBasis F) (hB : PackField B) {x : K} :
    x ∈ K2F B hB ↔ x ∈ K2 B hB := Iff.rfl

theorem towerBasis_zero (B : PackBasis F) : R0P.Mask.towerBasis B 0 = 1 := rfl
theorem towerBasis_one (B : PackBasis F) : R0P.Mask.towerBasis B 1 = B.i := rfl
theorem towerBasis_two (B : PackBasis F) : R0P.Mask.towerBasis B 2 = B.u := rfl
theorem towerBasis_three (B : PackBasis F) : R0P.Mask.towerBasis B 3 = B.i * B.u := rfl

/-- `{1, i, u, iu}` is `F`-independent (from `PackBasis.indep`). -/
theorem towerBasis_linearIndependent (B : PackBasis F) :
    LinearIndependent F (R0P.Mask.towerBasis B) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h : (g 0 : K) + B.i * g 1 + B.u * g 2 + B.i * B.u * g 3 = 0 := by
    rw [← hg, Fin.sum_univ_four]
    simp only [fsmul_eq, towerBasis_zero, towerBasis_one, towerBasis_two, towerBasis_three]
    ring
  obtain ⟨h0, h1, h2, h3⟩ := B.indep _ _ _ _ (g 0).2 (g 1).2 (g 2).2 (g 3).2 h
  intro j
  fin_cases j
  · exact Subtype.ext h0
  · exact Subtype.ext h1
  · exact Subtype.ext h2
  · exact Subtype.ext h3

theorem K4F_eq_span (B : PackBasis F) (hB : PackField B) :
    K4F B hB = Submodule.span F (Set.range (R0P.Mask.towerBasis B)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := (mem_K4_iff_pack4 B hB).1 hx
    have e : pack4 B v =
        v 0 * R0P.Mask.towerBasis B 0 + v 1 * R0P.Mask.towerBasis B 1 +
        v 2 * R0P.Mask.towerBasis B 2 + v 3 * R0P.Mask.towerBasis B 3 := by
      rw [towerBasis_zero, towerBasis_one, towerBasis_two, towerBasis_three]
      unfold pack4
      ring
    rw [e]
    have hm (j : Fin 4) : v j * R0P.Mask.towerBasis B j ∈
        Submodule.span F (Set.range (R0P.Mask.towerBasis B)) :=
      Submodule.smul_mem _ (⟨v j, hv j⟩ : F) (Submodule.subset_span ⟨j, rfl⟩)
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (hm 0) (hm 1)) (hm 2))
      (hm 3)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact towerBasis_mem_K4 B hB j

theorem finrank_K4F (B : PackBasis F) (hB : PackField B) :
    Module.finrank F (K4F B hB) = 4 := by
  rw [K4F_eq_span B hB, finrank_span_eq_card (towerBasis_linearIndependent B),
    Fintype.card_fin]

/-- The `K₂` basis `{1, i}`. -/
def k2Basis (B : PackBasis F) : Fin 2 → K := fun j => if j.val = 0 then 1 else B.i

theorem k2Basis_linearIndependent (B : PackBasis F) :
    LinearIndependent F (k2Basis B) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h' : (g 0 : K) + B.i * g 1 = 0 := by
    rw [← hg, Fin.sum_univ_two]
    simp only [fsmul_eq]
    have e0 : k2Basis B 0 = 1 := rfl
    have e1 : k2Basis B 1 = B.i := rfl
    rw [e0, e1]
    ring
  have h : (g 0 : K) + B.i * g 1 + B.u * 0 + B.i * B.u * 0 = 0 := by
    rw [mul_zero, mul_zero, add_zero, add_zero]
    exact h'
  obtain ⟨h0, h1, -, -⟩ := B.indep _ _ _ _ (g 0).2 (g 1).2 F.zero_mem F.zero_mem h
  intro j
  fin_cases j
  · exact Subtype.ext h0
  · exact Subtype.ext h1

theorem K2F_eq_span (B : PackBasis F) (hB : PackField B) :
    K2F B hB = Submodule.span F (Set.range (k2Basis B)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_K2 B hB).1 hx
    have e : a + B.i * b = a * k2Basis B 0 + b * k2Basis B 1 := by
      have e0 : k2Basis B 0 = 1 := rfl
      have e1 : k2Basis B 1 = B.i := rfl
      rw [e0, e1]
      ring
    rw [e]
    have h0 : a * k2Basis B 0 ∈ Submodule.span F (Set.range (k2Basis B)) :=
      Submodule.smul_mem _ (⟨a, ha⟩ : F) (Submodule.subset_span ⟨0, rfl⟩)
    have h1 : b * k2Basis B 1 ∈ Submodule.span F (Set.range (k2Basis B)) :=
      Submodule.smul_mem _ (⟨b, hb⟩ : F) (Submodule.subset_span ⟨1, rfl⟩)
    exact Submodule.add_mem _ h0 h1
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    unfold k2Basis
    split_ifs
    · exact (K2 B hB).one_mem
    · exact i_mem_K2 B hB

theorem finrank_K2F (B : PackBasis F) (hB : PackField B) :
    Module.finrank F (K2F B hB) = 2 := by
  rw [K2F_eq_span B hB, finrank_span_eq_card (k2Basis_linearIndependent B),
    Fintype.card_fin]

theorem K2F_le_K4F (B : PackBasis F) (hB : PackField B) : K2F B hB ≤ K4F B hB :=
  fun _ hx => K2_le_K4 B hB hx

/-! ### The quadratic-subfield lemma -/

/-- Frobenius over `F` (power `|F|`) squares to the identity on every root of
a quadratic over `F`. -/
theorem frob_sq_of_quadratic [Fintype F] {y a b : K} (ha : a ∈ F) (hb : b ∈ F)
    (hy : y * y = a + b * y) :
    (y ^ Fintype.card F) ^ Fintype.card F = y := by
  let φ := FiniteField.frobeniusAlgHom F K
  have hφ (w : K) : φ w = w ^ Fintype.card F := rfl
  have hfix {c : K} (hc : c ∈ F) : φ c = c := φ.commutes ⟨c, hc⟩
  rw [← hφ, ← hφ]
  set z := φ y with hzdef
  have hz : z * z = a + b * z := by
    have h := congrArg φ hy
    rw [map_mul, map_add, map_mul, hfix ha, hfix hb] at h
    exact h
  have hprod : (z - y) * (z + y - b) = 0 := by linear_combination hz - hy
  rcases mul_eq_zero.1 hprod with h | h
  · have h1 : z = y := sub_eq_zero.1 h
    rw [h1]
    exact h1
  · have h2 : z = b - y := by linear_combination h
    rw [h2, map_sub, hfix hb]
    have h3 : φ y = z := rfl
    rw [h3, h2]
    ring

/-- An element of `K` that is quadratic over `F` lies in `K₂`.  The proof is
by Frobenius and the root count of `X^(q²) − X` against the `q²` elements of
`K₂`, with `q = |F|`; it needs no premise beyond finiteness of `K` (the
cardinality of `F` is read from its `Fintype` structure), and it holds for
every `x : K`, not only `x ∈ K₄`. -/
theorem mem_K2_of_quadratic (B : PackBasis F) (hB : PackField B) {x : K}
    (hx : x * x ∈ Submodule.span F ({1, x} : Set K)) : x ∈ K2 B hB := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  set q := Fintype.card F with hq
  have hq1 : 1 < q := Fintype.one_lt_card
  have hqq : 1 < q * q := by nlinarith
  by_contra hxK
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 hx
  rw [fsmul_eq, fsmul_eq, mul_one] at hab
  have hroot {w : K} (hw : (w ^ q) ^ q = w) :
      w ∈ (Polynomial.X ^ (q * q) - Polynomial.X : Polynomial K).roots := by
    rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero K hqq)]
    simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X]
    rw [pow_mul, hw, sub_self]
  let S : Finset K := Finset.univ.image (fun p : F × F => (p.1 : K) + B.i * p.2)
  have hinj : Function.Injective (fun p : F × F => (p.1 : K) + B.i * p.2) := by
    intro p p' h0
    have h : (p.1 : K) + B.i * p.2 = p'.1 + B.i * p'.2 := h0
    have h' : ((p.1 : K) - p'.1) + B.i * ((p.2 : K) - p'.2) + B.u * 0 + B.i * B.u * 0 = 0 := by
      linear_combination h
    obtain ⟨h1, h2, -, -⟩ := B.indep _ _ _ _ (F.sub_mem p.1.2 p'.1.2)
      (F.sub_mem p.2.2 p'.2.2) F.zero_mem F.zero_mem h'
    exact Prod.ext (Subtype.ext (sub_eq_zero.1 h1)) (Subtype.ext (sub_eq_zero.1 h2))
  have hS : S.card = q * q := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod]
  have hxS : x ∉ S := by
    intro h
    obtain ⟨p, -, hp⟩ := Finset.mem_image.1 h
    exact hxK ((mem_K2 B hB).2 ⟨p.1, p.1.2, p.2, p.2.2, hp.symm⟩)
  have hsub : (insert x S).val ⊆
      (Polynomial.X ^ (q * q) - Polynomial.X : Polynomial K).roots := by
    intro w hw
    have hw' : w ∈ insert x S := hw
    rcases Finset.mem_insert.1 hw' with h | h
    · rw [h]
      exact hroot (frob_sq_of_quadratic a.2 b.2 hab.symm)
    · obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 h
      apply hroot
      have hs := hB.1
      refine frob_sq_of_quadratic (a := -((p.1 : K) * p.1) + (B.i * B.i) * ((p.2 : K) * p.2))
        (b := 2 * (p.1 : K)) ?_ ?_ ?_
      · exact F.add_mem (F.neg_mem (F.mul_mem p.1.2 p.1.2)) (F.mul_mem hs (F.mul_mem p.2.2 p.2.2))
      · have h2 : (2 : K) ∈ F := by
          have h := natCast_mem F 2
          simpa using h
        exact F.mul_mem h2 p.1.2
      · ring
  have hcard := Polynomial.card_le_degree_of_subset_roots hsub
  rw [Finset.card_insert_of_notMem hxS, hS,
    FiniteField.X_pow_card_sub_X_natDegree_eq K hqq] at hcard
  omega

/-! ### Invariant subspaces of `K₄` -/

/-- A subspace of `K₄` containing 1 and stable under multiplication by some
`β ∈ K₄ ∖ K₂` is all of `K₄`. -/
theorem K4F_le_of_invariant (B : PackBasis F) (hB : PackField B)
    {T : Submodule F K} (hT : T ≤ K4F B hB) (h1 : (1 : K) ∈ T)
    {β : K} (hβ : β ∈ K4 B hB) (hβ2 : β ∉ K2 B hB)
    (hinv : ∀ y ∈ T, β * y ∈ T) : K4F B hB ≤ T := by
  have hβT : β ∈ T := by simpa using hinv 1 h1
  have hββ : β * β ∈ T := hinv β hβT
  have hβF : β ∉ F := fun h => hβ2 (F_le_K2 B hB h)
  have hTle : Module.finrank F T ≤ 4 := by
    have := Submodule.finrank_mono hT
    rw [finrank_K4F] at this
    exact this
  have hP1 : Module.finrank F (Submodule.span F ({1} : Set K)) = 1 :=
    finrank_span_singleton one_ne_zero
  have hlt : Submodule.span F ({1} : Set K) < Submodule.span F ({1, β} : Set K) := by
    refine lt_of_le_of_ne (Submodule.span_mono (by simp)) ?_
    intro heq
    have hm : β ∈ Submodule.span F ({1} : Set K) := by
      rw [heq]
      exact Submodule.subset_span (by simp)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hm
    rw [fsmul_eq, mul_one] at hc
    exact hβF (hc ▸ c.2)
  have hP2 : 2 ≤ Module.finrank F (Submodule.span F ({1, β} : Set K)) := by
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hP2T : Submodule.span F ({1, β} : Set K) ≤ T := by
    rw [Submodule.span_le]
    intro w hw
    rcases hw with rfl | hw
    · exact h1
    · rw [Set.mem_singleton_iff.1 hw]
      exact hβT
  by_cases hT4 : Module.finrank F T = 4
  · exact (Submodule.eq_of_le_of_finrank_eq hT (hT4.trans (finrank_K4F B hB).symm)).ge
  by_cases hT3 : Module.finrank F T = 3
  · exfalso
    have hne : ¬ K4F B hB ≤ T := fun h => by
      have := Submodule.finrank_mono h
      rw [finrank_K4F] at this
      omega
    obtain ⟨y, hyK, hyT⟩ := SetLike.not_le_iff_exists.1 hne
    have hlt' : T < T ⊔ Submodule.span F ({y} : Set K) := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro h
      apply hyT
      rw [h]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)
    have hsup_le : T ⊔ Submodule.span F ({y} : Set K) ≤ K4F B hB :=
      sup_le hT (by
        rw [Submodule.span_le, Set.singleton_subset_iff]
        exact hyK)
    have hfin : Module.finrank F ↥(T ⊔ Submodule.span F ({y} : Set K)) = 4 := by
      have h3 := Submodule.finrank_lt_finrank_of_lt hlt'
      have h4 := Submodule.finrank_mono hsup_le
      rw [finrank_K4F] at h4
      omega
    have hsup : T ⊔ Submodule.span F ({y} : Set K) = K4F B hB :=
      Submodule.eq_of_le_of_finrank_eq hsup_le (hfin.trans (finrank_K4F B hB).symm)
    have hβy : β * y ∈ T ⊔ Submodule.span F ({y} : Set K) := by
      rw [hsup]
      exact (K4 B hB).mul_mem hβ hyK
    obtain ⟨p, hp, q', hq', hpq⟩ := Submodule.mem_sup.1 hβy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hq'
    rw [fsmul_eq] at hpq
    have key : ∀ w ∈ K4F B hB, (β - (c : K)) * w ∈ T := by
      intro w hw
      rw [← hsup] at hw
      obtain ⟨t, ht, s, hs, rfl⟩ := Submodule.mem_sup.1 hw
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hs
      rw [fsmul_eq]
      have e : (β - (c : K)) * (t + (d : K) * y) =
          β * t + ((-c : F) : K) * t + (d : K) * p := by
        have hn : ((-c : F) : K) = -(c : K) := rfl
        rw [hn]
        linear_combination (d : K) * hpq.symm
      rw [e]
      have m2 : ((-c : F) : K) * t ∈ T := by
        rw [← fsmul_eq]
        exact T.smul_mem _ ht
      have m3 : (d : K) * p ∈ T := by
        rw [← fsmul_eq]
        exact T.smul_mem _ hp
      exact T.add_mem (T.add_mem (hinv t ht) m2) m3
    apply hne
    intro w hw
    have hβc : β - (c : K) ≠ 0 := by
      intro h
      apply hβF
      rw [sub_eq_zero.1 h]
      exact c.2
    have hm : (β - (c : K))⁻¹ * w ∈ K4F B hB :=
      (K4 B hB).mul_mem ((K4 B hB).inv_mem ((K4 B hB).sub_mem hβ (F_le_K4 B hB c.2))) hw
    have := key _ hm
    rwa [← mul_assoc, mul_inv_cancel₀ hβc, one_mul] at this
  · exfalso
    have h2 : Module.finrank F T ≤ Module.finrank F (Submodule.span F ({1, β} : Set K)) := by
      have := Submodule.finrank_mono hP2T
      omega
    have heq : Submodule.span F ({1, β} : Set K) = T :=
      Submodule.eq_of_le_of_finrank_le hP2T h2
    have hm : β * β ∈ Submodule.span F ({1, β} : Set K) := by
      rw [heq]
      exact hββ
    exact hβ2 (mem_K2_of_quadratic B hB hm)

/-! ### One growth step -/

/-- `T + β·T`. -/
def stepT (T : Submodule F K) (β : K) : Submodule F K :=
  T ⊔ T.map (LinearMap.mulLeft F β)

/-- Indicator of `β ∉ S`, as a natural number. -/
def notIn (S : Subfield K) (β : K) : ℕ := by
  classical
  exact if β ∈ S then 0 else 1

theorem notIn_of_not_mem {S : Subfield K} {β : K} (h : β ∉ S) : notIn S β = 1 := by
  unfold notIn
  rw [if_neg h]

/-- The growth invariant: `K₄ ⊆ T` or `n ≤ dim T`. -/
def Grow (B : PackBasis F) (hB : PackField B) (T : Submodule F K) (n : ℕ) : Prop :=
  K4F B hB ≤ T ∨ n ≤ Module.finrank F T

theorem step_grow (B : PackBasis F) (hB : PackField B)
    {T : Submodule F K} (hT : T ≤ K4F B hB) (h1 : (1 : K) ∈ T)
    {β : K} (hβ : β ∈ K4 B hB) {n : ℕ} (hG : Grow B hB T n) :
    stepT T β ≤ K4F B hB ∧ (1 : K) ∈ stepT T β ∧
      Grow B hB (stepT T β) (n + notIn (K2 B hB) β) := by
  have hle : T ≤ stepT T β := le_sup_left
  have hT' : stepT T β ≤ K4F B hB := by
    refine sup_le hT ?_
    rw [Submodule.map_le_iff_le_comap]
    intro y hy
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
    exact (K4 B hB).mul_mem hβ (hT hy)
  refine ⟨hT', hle h1, ?_⟩
  have hmono : Module.finrank F T ≤ Module.finrank F (stepT T β) := Submodule.finrank_mono hle
  by_cases hb : β ∈ K2 B hB
  · have h0 : notIn (K2 B hB) β = 0 := by
      unfold notIn
      rw [if_pos hb]
    rw [h0, add_zero]
    rcases hG with h | h
    · exact Or.inl (h.trans hle)
    · exact Or.inr (h.trans hmono)
  · rw [notIn_of_not_mem hb]
    rcases hG with h | h
    · exact Or.inl (h.trans hle)
    · by_cases hinv : stepT T β ≤ T
      · left
        refine (K4F_le_of_invariant B hB hT h1 hβ hb ?_).trans hle
        intro y hy
        apply hinv
        exact Submodule.mem_sup_right (Submodule.mem_map_of_mem hy)
      · right
        have hlt : T < stepT T β := lt_of_le_of_ne hle (fun h => hinv (by rw [← h]))
        have := Submodule.finrank_lt_finrank_of_lt hlt
        omega

theorem grow_mono (B : PackBasis F) (hB : PackField B) {T : Submodule F K}
    {m n : ℕ} (hmn : m ≤ n) (hG : Grow B hB T n) : Grow B hB T m := by
  rcases hG with h | h
  · exact Or.inl h
  · exact Or.inr (hmn.trans h)

end Field

/-! ### The prefix spans `Λ_j` -/

section Lambda
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- `Λ_j = span_F {eqPrefix(a, r, j) : r}`; the range is symbolic. -/
def Lambda (F : Subfield K) (a : Fin 10 → K) (j : Fin 10) : Submodule F K :=
  Submodule.span F (Set.range fun r : Fin 1024 => R0Z.PureRounds.eqPrefix a r j)

/-- Extending a prefix by one bit multiplies by that bit's factor. -/
theorem eqPrefix_update (a : Fin 10 → K) (j : Fin 9) (r : Fin 1024) (b : Bool) :
    R0Z.PureRounds.eqPrefix a (rowOf (Function.update (rowBits r) j.castSucc b)) j.succ =
      R0Z.PureRounds.eqPrefix a r j.castSucc * bitFactor b (a j.castSucc) := by
  unfold R0Z.PureRounds.eqPrefix
  rw [rowBits_rowOf]
  have h : ∀ i : Fin 10,
      (if i.val < j.succ.val then
        bitFactor (Function.update (rowBits r) j.castSucc b i) (a i) else 1) =
      (if i.val < j.castSucc.val then bitFactor (rowBits r i) (a i) else 1) *
        (if i = j.castSucc then bitFactor b (a j.castSucc) else 1) := by
    intro i
    by_cases h1 : i = j.castSucc
    · subst h1
      have hlt : j.castSucc.val < j.succ.val := by
        rw [Fin.val_succ, Fin.val_castSucc]
        omega
      rw [if_pos hlt, if_neg (lt_irrefl _), if_pos rfl, Function.update_self, one_mul]
    · rw [if_neg h1, mul_one, Function.update_of_ne h1]
      have hne : i.val ≠ j.val := fun h => h1 (Fin.ext (by rw [Fin.val_castSucc]; exact h))
      by_cases h2 : i.val < j.castSucc.val
      · rw [if_pos h2, if_pos]
        rw [Fin.val_succ]
        rw [Fin.val_castSucc] at h2
        omega
      · rw [if_neg h2, if_neg]
        rw [Fin.val_succ]
        rw [Fin.val_castSucc] at h2
        omega
  rw [Finset.prod_congr rfl (fun i _ => h i), Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp only [Finset.mem_univ, if_true]

theorem bitFactor_true (x : K) : bitFactor true x = x := rfl
theorem bitFactor_false (x : K) : bitFactor false x = 1 - x := rfl

variable {F : Subfield K}

theorem eqPrefix_mem_succ (a : Fin 10 → K) (j : Fin 9) (r : Fin 1024) :
    R0Z.PureRounds.eqPrefix a r j.castSucc ∈ Lambda F a j.succ ∧
      R0Z.PureRounds.eqPrefix a r j.castSucc * a j.castSucc ∈ Lambda F a j.succ := by
  have g (b : Bool) : R0Z.PureRounds.eqPrefix a
      (rowOf (Function.update (rowBits r) j.castSucc b)) j.succ ∈ Lambda F a j.succ :=
    Submodule.subset_span ⟨_, rfl⟩
  have e1 := eqPrefix_update a j r true
  have e0 := eqPrefix_update a j r false
  rw [bitFactor_true] at e1
  rw [bitFactor_false] at e0
  have h1 := g true
  have h0 := g false
  rw [e1] at h1
  rw [e0] at h0
  refine ⟨?_, h1⟩
  have hs := Submodule.add_mem _ h1 h0
  have e : R0Z.PureRounds.eqPrefix a r j.castSucc * a j.castSucc +
      R0Z.PureRounds.eqPrefix a r j.castSucc * (1 - a j.castSucc) =
      R0Z.PureRounds.eqPrefix a r j.castSucc := by ring
  rw [e] at hs
  exact hs

theorem Lambda_le_succ (a : Fin 10 → K) (j : Fin 9) :
    Lambda F a j.castSucc ≤ Lambda F a j.succ := by
  rw [Lambda, Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  exact (eqPrefix_mem_succ a j r).1

theorem mul_mem_Lambda_succ (a : Fin 10 → K) (j : Fin 9) {x : K}
    (hx : x ∈ Lambda F a j.castSucc) : x * a j.castSucc ∈ Lambda F a j.succ := by
  have hle : Lambda F a j.castSucc ≤
      (Lambda F a j.succ).comap (LinearMap.mulRight F (a j.castSucc)) := by
    rw [Lambda, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulRight_apply]
    exact (eqPrefix_mem_succ a j r).2
  have := hle hx
  rw [Submodule.mem_comap, LinearMap.mulRight_apply] at this
  exact this

theorem Lambda_mono (a : Fin 10 → K) {j k : Fin 10} (h : j ≤ k) :
    Lambda F a j ≤ Lambda F a k := by
  have key : ∀ n : ℕ, ∀ k : Fin 10, k.val = j.val + n → Lambda F a j ≤ Lambda F a k := by
    intro n
    induction n with
    | zero =>
      intro k hk
      have hkj : k = j := Fin.ext (by omega)
      subst hkj
      exact le_rfl
    | succ n ih =>
      intro k hk
      have hk9 : j.val + n < 9 := by omega
      let k' : Fin 9 := ⟨j.val + n, hk9⟩
      have h1 : k'.castSucc.val = j.val + n := rfl
      have h2 : k'.succ = k := Fin.ext (by rw [Fin.val_succ]; show j.val + n + 1 = k.val; omega)
      refine (ih k'.castSucc h1).trans ?_
      rw [← h2]
      exact Lambda_le_succ a k'
  exact key (k.val - j.val) k (by have := Fin.le_iff_val_le_val.mp h; omega)

theorem one_mem_Lambda (a : Fin 10 → K) (j : Fin 10) : (1 : K) ∈ Lambda F a j := by
  have h0 : R0Z.PureRounds.eqPrefix a 0 0 = 1 := by
    unfold R0Z.PureRounds.eqPrefix
    simp
  have hm : (1 : K) ∈ Lambda F a 0 := Submodule.subset_span ⟨0, h0⟩
  exact Lambda_mono a (Fin.le_iff_val_le_val.2 (Nat.zero_le _)) hm

theorem alpha_mem_Lambda (a : Fin 10 → K) {i j : Fin 10} (h : i < j) :
    a i ∈ Lambda F a j := by
  have hi : i.val < 9 := by have := Fin.lt_def.mp h; have := j.isLt; omega
  let i' : Fin 9 := ⟨i.val, hi⟩
  have hc : i'.castSucc = i := Fin.ext rfl
  have h1 := mul_mem_Lambda_succ (F := F) a i' (one_mem_Lambda a i'.castSucc)
  rw [one_mul, hc] at h1
  refine Lambda_mono a ?_ h1
  rw [Fin.le_iff_val_le_val, Fin.val_succ]
  have := Fin.lt_def.mp h
  show i.val + 1 ≤ j.val
  omega

theorem Lambda_le_K4F (B : PackBasis F) (hB : PackField B) (a : Fin 10 → K)
    (ha : ∀ i, a i ∈ K4 B hB) (j : Fin 10) : Lambda F a j ≤ K4F B hB := by
  rw [Lambda, Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  show R0Z.PureRounds.eqPrefix a r j ∈ K4 B hB
  unfold R0Z.PureRounds.eqPrefix
  refine prod_mem (fun i _ => ?_)
  split_ifs
  · unfold bitFactor
    split_ifs
    · exact ha i
    · exact (K4 B hB).sub_mem (K4 B hB).one_mem (ha i)
  · exact (K4 B hB).one_mem

/-- One `Λ` step: `T ≤ Λ_j ⇒ T + a_j·T ≤ Λ_{j+1}`. -/
theorem stepT_le_Lambda (a : Fin 10 → K) (j : Fin 9) {T : Submodule F K}
    (hT : T ≤ Lambda F a j.castSucc) : stepT T (a j.castSucc) ≤ Lambda F a j.succ := by
  refine sup_le (hT.trans (Lambda_le_succ a j)) ?_
  rw [Submodule.map_le_iff_le_comap]
  intro y hy
  rw [Submodule.mem_comap, LinearMap.mulLeft_apply, mul_comm]
  exact mul_mem_Lambda_succ a j (hT hy)

/-! ### `Good₃` and `Λ₄ = K₄` -/

/-- `Good₃` as proposed in design §1.2 and kept by LOG D21.3/D23.3:
`Good`, every semantic challenge in `K₄`, and at least three of `α₀..α₃`
outside `K₂`. -/
def Good3 (B : PackBasis F) (hB : PackField B) (ch : Challenges K) : Prop :=
  R0Z.Shift.Good ch ∧ (∀ i : Fin 25, ch.sem i ∈ K4 B hB) ∧
    ∃ s : Finset (Fin 4), 3 ≤ s.card ∧
      ∀ i ∈ s, alpha ch ⟨i.val, lt_trans i.isLt (by norm_num)⟩ ∉ K2 B hB

/-- Design lemma lambda4_eq_K4: on `Good₃`, `Λ_j = K₄` for every `j ≥ 4`. -/
theorem lambda4_eq_K4 (B : PackBasis F) (hB : PackField B) (ch : Challenges K)
    (hG : Good3 B hB ch) (j : Fin 10) (hj : 4 ≤ j.val) :
    Lambda F (alpha ch) j = K4F B hB := by
  obtain ⟨-, hsem, s, hs3, hs⟩ := hG
  have hα (k : Fin 10) : alpha ch k ∈ K4 B hB := hsem _
  apply le_antisymm (Lambda_le_K4F B hB _ hα j)
  -- count of α₀..α₃ outside K₂
  have hcount : 3 ≤ notIn (K2 B hB) (alpha ch 0) + notIn (K2 B hB) (alpha ch 1) +
      notIn (K2 B hB) (alpha ch 2) + notIn (K2 B hB) (alpha ch 3) := by
    have hsum : s.card ≤ ∑ i : Fin 4,
        notIn (K2 B hB) (alpha ch ⟨i.val, lt_trans i.isLt (by norm_num)⟩) := by
      calc s.card = ∑ _i ∈ s, (1 : ℕ) := by simp
        _ = ∑ i ∈ s,
            notIn (K2 B hB) (alpha ch ⟨i.val, lt_trans i.isLt (by norm_num)⟩) :=
            Finset.sum_congr rfl (fun i hi => (notIn_of_not_mem (hs i hi)).symm)
        _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ s)
    rw [Fin.sum_univ_four] at hsum
    exact hs3.trans hsum
  -- the chain T₀ ≤ … ≤ T₄
  let T0 : Submodule F K := Submodule.span F ({1} : Set K)
  have hT0K : T0 ≤ K4F B hB := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact (K4 B hB).one_mem
  have hT01 : (1 : K) ∈ T0 := Submodule.subset_span rfl
  have hT0G : Grow B hB T0 1 := Or.inr (finrank_span_singleton one_ne_zero).ge
  have hT0L : T0 ≤ Lambda F (alpha ch) 0 := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact one_mem_Lambda _ _
  obtain ⟨hT1K, hT11, hT1G⟩ := step_grow B hB hT0K hT01 (hα 0) hT0G
  have hT1L := stepT_le_Lambda (alpha ch) 0 hT0L
  obtain ⟨hT2K, hT21, hT2G⟩ := step_grow B hB hT1K hT11 (hα 1) hT1G
  have hT2L := stepT_le_Lambda (alpha ch) 1 hT1L
  obtain ⟨hT3K, hT31, hT3G⟩ := step_grow B hB hT2K hT21 (hα 2) hT2G
  have hT3L := stepT_le_Lambda (alpha ch) 2 hT2L
  obtain ⟨hT4K, -, hT4G⟩ := step_grow B hB hT3K hT31 (hα 3) hT3G
  have hT4L := stepT_le_Lambda (alpha ch) 3 hT3L
  have hG4 := grow_mono B hB (m := 4) (by omega) hT4G
  have hK4 : K4F B hB ≤ Lambda F (alpha ch) ((3 : Fin 9).succ) := by
    rcases hG4 with h | h
    · exact h.trans hT4L
    · have he := Submodule.eq_of_le_of_finrank_le hT4K (by rw [finrank_K4F]; exact h)
      rw [← he]
      exact hT4L
  exact hK4.trans (Lambda_mono _ (Fin.le_iff_val_le_val.2 (show 4 ≤ j.val from hj)))

end Lambda

#print axioms inv_mem_of_subring
#print axioms mem_K2
#print axioms mem_K4_iff_pack4
#print axioms K2_le_K4
#print axioms F_le_K4
#print axioms pack4_mem_K4
#print axioms towerBasis_mem_K4
#print axioms natCast_mem_K4
#print axioms half_mem_K4
#print axioms towerBasis_linearIndependent
#print axioms K4F_eq_span
#print axioms finrank_K4F
#print axioms finrank_K2F
#print axioms K2F_le_K4F
#print axioms frob_sq_of_quadratic
#print axioms mem_K2_of_quadratic
#print axioms K4F_le_of_invariant
#print axioms step_grow
#print axioms eqPrefix_update
#print axioms eqPrefix_mem_succ
#print axioms Lambda_le_succ
#print axioms mul_mem_Lambda_succ
#print axioms Lambda_mono
#print axioms one_mem_Lambda
#print axioms alpha_mem_Lambda
#print axioms Lambda_le_K4F
#print axioms stepT_le_Lambda
#print axioms lambda4_eq_K4

end R0Z.K4
