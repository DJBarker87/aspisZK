import R1Z.PredicateR1

/-! D49.4 C2: RF-bat and RF-rel (zf1/DESIGN-P-CERT.txt §0 "bat", §1.5, §2.3), Lean side.

The batched values are WideExact values (γ, κ, α₀, α₁ are WideExact
challenges), so the checker's batched coordinates are eight base limbs per
cell (z9.rs:501-503 `wflat`, limb `k` of cell `c` at index `8c + k`), over the
read support in the order round0 (7), round1 (7), the opened folded cells
`fp` (z9c.rs `lay`), final (64) — 1,328 coordinates at nf = 88 (the probe's
extra inactive cell, limbs 0..7, is not an `R1Bat` cell and is dropped,
z9c.rs:163 `BAT0`).

The limb basis is a hypothesis `wb : Module.Basis (Fin 8) F K` (the WideExact limb
basis `decode8`; on the instance K = WideExact over F = M31 it is
wide_exact.rs `from_limbs`).  The opened list `fp` must cover the open folded
cells (`hcov`, a decidable fact about the query list the checker tests).

* `iotaB_flatB`: `iotaB ∘ flatB = id` on vectors vanishing off the open
  folded cells (`unopenedZero`).
* `rf_bat`: for every mask tape `m`, `batMap m = iotaB (flatB (batMap m))`;
  hence the `rf_bat` premise with `Bt i t = flatB (batMap (src t)) i`.
* `rf_rel`: with `Rel y c` the `wb`-limb `(rows y).2` of relation `(rows y).1`
  of `relR1 (iotaB e_c)` (for any list `rows` of relation limbs, z9b.rs:107
  `design_relations` + `limb_functionals`), `B0R1' ≤ iotaB (ker Rel)`.  The
  line relation inside `relR1` uses `lineInverse` (D34.3, `R1Z.RfLine`).

Matching the Rust `limb_functionals` rows to `Rel` is C3. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.RfBat

open scoped BigOperators
open R0P R0Z.HonestView R1Z.Batched R1Z.VerifierRelationsR1 R1Z.PredicateR1

attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

variable (wb : Module.Basis (Fin 8) F K)

/-- The support cell at position `c` (round0, round1, opened folded, final). -/
def batCell {nf : ℕ} (fp : Fin nf → Fin 262144) (c : Fin (78 + nf)) : R1Bat :=
  if h1 : c.val < 7 then .round0 ⟨c.val, h1⟩
  else if h2 : c.val < 14 then .round1 ⟨c.val - 7, by omega⟩
  else if h3 : c.val < 14 + nf then .folded (fp ⟨c.val - 14, by omega⟩)
  else .final ⟨c.val - 14 - nf, by omega⟩

/-- `wflat` order: limb `k` of cell `c` is index `8c + k`. -/
def fpb (nf : ℕ) : Fin (78 + nf) × Fin 8 ≃ Fin ((78 + nf) * 8) := finProdFinEquiv

/-- Value of one cell from its eight limbs. -/
def combL : (Fin 8 → F) →ₗ[F] K where
  toFun x := ∑ k, x k • wb k
  map_add' x y := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, smul_smul, RingHom.id_apply, Finset.smul_sum]

/-- The checker's limbs at support position `c`. -/
def cellL {nf : ℕ} (c : Fin (78 + nf)) : (Fin ((78 + nf) * 8) → F) →ₗ[F] K :=
  (combL wb).comp (LinearMap.funLeft F F (fun k => fpb nf (c, k)))

/-- The checker's batched coordinate embedding `ιb`. -/
def iotaB {nf : ℕ} (fp : Fin nf → Fin 262144) : (Fin ((78 + nf) * 8) → F) →ₗ[F] (R1Bat → K) :=
  LinearMap.pi fun b => match b with
  | .round0 i => cellL wb ⟨i.val, by omega⟩
  | .round1 i => cellL wb ⟨7 + i.val, by omega⟩
  | .final e => cellL wb ⟨14 + nf + e.val, by omega⟩
  | .folded p => if h : ∃ f : Fin nf, fp f = p then
      cellL wb ⟨14 + (Classical.choose h).val, by omega⟩ else 0

/-- The checker's batched coordinates of a vector. -/
def flatB {nf : ℕ} (fp : Fin nf → Fin 262144) (x : R1Bat → K) : Fin ((78 + nf) * 8) → F :=
  fun i => wb.repr (x (batCell fp ((fpb nf).symm i).1)) ((fpb nf).symm i).2

theorem cellL_flatB {nf : ℕ} (fp : Fin nf → Fin 262144) (x : R1Bat → K) (c : Fin (78 + nf)) :
    cellL wb c (flatB wb fp x) = x (batCell fp c) := by
  show ∑ k, flatB wb fp x (fpb nf (c, k)) • wb k = _
  simp only [flatB, Equiv.symm_apply_apply]
  exact wb.sum_repr _

theorem batCell_round0 {nf : ℕ} (fp : Fin nf → Fin 262144) (i : Fin 7) :
    batCell fp ⟨i.val, by omega⟩ = .round0 i := by
  unfold batCell
  rw [dif_pos i.isLt]

theorem batCell_round1 {nf : ℕ} (fp : Fin nf → Fin 262144) (i : Fin 7) :
    batCell fp ⟨7 + i.val, by omega⟩ = .round1 i := by
  have hi := i.isLt
  unfold batCell
  rw [dif_neg (show ¬ 7 + i.val < 7 by omega), dif_pos (show 7 + i.val < 14 by omega)]
  congr 1
  exact Fin.ext (show 7 + i.val - 7 = i.val by omega)

theorem batCell_folded {nf : ℕ} (fp : Fin nf → Fin 262144) (f : Fin nf) :
    batCell fp ⟨14 + f.val, by omega⟩ = .folded (fp f) := by
  have hf := f.isLt
  unfold batCell
  rw [dif_neg (show ¬ 14 + f.val < 7 by omega), dif_neg (show ¬ 14 + f.val < 14 by omega),
    dif_pos (show 14 + f.val < 14 + nf by omega)]
  congr 2
  exact Fin.ext (show 14 + f.val - 14 = f.val by omega)

theorem batCell_final {nf : ℕ} (fp : Fin nf → Fin 262144) (e : Fin 64) :
    batCell fp ⟨14 + nf + e.val, by omega⟩ = .final e := by
  have he := e.isLt
  unfold batCell
  rw [dif_neg (show ¬ 14 + nf + e.val < 7 by omega), dif_neg (show ¬ 14 + nf + e.val < 14 by omega),
    dif_neg (show ¬ 14 + nf + e.val < 14 + nf by omega)]
  congr 1
  exact Fin.ext (show 14 + nf + e.val - 14 - nf = e.val by omega)

/-- `iotaB ∘ flatB = id` on vectors with zero unopened folded cells. -/
theorem iotaB_flatB (ch : Challenges K) {nf : ℕ} (fp : Fin nf → Fin 262144)
    (hcov : ∀ p, FoldedOpen ch p → ∃ f, fp f = p) (x : R1Bat → K) (hx : x ∈ unopenedZero (F := F) ch) :
    iotaB wb fp (flatB wb fp x) = x := by
  funext b
  cases b with
  | round0 i =>
    show cellL wb ⟨i.val, _⟩ (flatB wb fp x) = _
    rw [cellL_flatB, batCell_round0]
  | round1 i =>
    show cellL wb ⟨7 + i.val, _⟩ (flatB wb fp x) = _
    rw [cellL_flatB, batCell_round1]
  | final e =>
    show cellL wb ⟨14 + nf + e.val, _⟩ (flatB wb fp x) = _
    rw [cellL_flatB, batCell_final]
  | folded p =>
    show (if h : ∃ f : Fin nf, fp f = p then
      cellL wb ⟨14 + (Classical.choose h).val, by omega⟩ else 0) (flatB wb fp x) = _
    split_ifs with h
    · rw [cellL_flatB, batCell_folded, Classical.choose_spec h]
    · rw [LinearMap.zero_apply]
      exact (hx p (fun ho => h (hcov p ho))).symm

/-- **RF-bat.**  Every mask tape's batched cells are the `ιb`-image of its
checker coordinates. -/
theorem rf_bat (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) {nf : ℕ}
    (fp : Fin nf → Fin 262144) (hcov : ∀ p, FoldedOpen ch p → ∃ f, fp f = p)
    (m : R0Z.Partition.M K F) :
    R0Z.SilentReduction.batMap (Bat := R1Bat) π B ch m =
      iotaB wb fp (flatB wb fp (R0Z.SilentReduction.batMap (Bat := R1Bat) π B ch m)) :=
  (iotaB_flatB wb ch fp hcov _ (fun p hp => batMap_unopened π B ch m p hp)).symm

/-- The checker's relation limb functionals: limb `(rows y).2` of relation
`(rows y).1` of `relR1` on the `c`-th unit coordinate. -/
def relMat (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) {nf q : ℕ} (fp : Fin nf → Fin 262144)
    (rows : Fin q → R1Rel × Fin 8) : Fin q → Fin ((78 + nf) * 8) → F := fun y c =>
  wb.repr (relR1 π ch (iotaB wb fp (fun c' => if c = c' then 1 else 0)) (rows y).1) (rows y).2

/-- **RF-rel.** -/
theorem rf_rel (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) {nf q : ℕ}
    (fp : Fin nf → Fin 262144) (hcov : ∀ p, FoldedOpen ch p → ∃ f, fp f = p)
    (rows : Fin q → R1Rel × Fin 8) :
    ∀ x ∈ B0R1' (F := F) π ch, ∃ v : Fin ((78 + nf) * 8) → F,
      (∀ y, ∑ c, relMat wb π ch fp rows y c * v c = 0) ∧ iotaB wb fp v = x := by
  intro x hx
  rcases Submodule.mem_inf.1 hx with ⟨hrel, hun⟩
  refine ⟨flatB wb fp x, fun y => ?_, iotaB_flatB wb ch fp hcov x hun⟩
  let Φ : (Fin ((78 + nf) * 8) → F) →ₗ[F] F :=
    (wb.coord (rows y).2).comp ((LinearMap.proj (rows y).1 : (R1Rel → K) →ₗ[F] K).comp
      (((relR1 π ch).restrictScalars F).comp (iotaB wb fp)))
  have hΦ : ∀ v, Φ v = wb.repr (relR1 π ch (iotaB wb fp v) (rows y).1) (rows y).2 := fun v => rfl
  have hdec : flatB wb fp x = ∑ c, flatB wb fp x c • (fun c' => if c = c' then (1 : F) else 0) := by
    funext j
    rw [Finset.sum_apply]
    simp [Finset.sum_ite_eq']
  have hsum : ∑ c, relMat wb π ch fp rows y c * flatB wb fp x c = Φ (flatB wb fp x) := by
    conv_rhs => rw [hdec]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [map_smul, smul_eq_mul, mul_comm]
    rfl
  rw [hsum, hΦ, iotaB_flatB wb ch fp hcov x hun]
  have h0 : relR1 π ch x = 0 := hrel
  rw [h0]
  simp

#print axioms cellL_flatB
#print axioms batCell_round0
#print axioms batCell_folded
#print axioms iotaB_flatB
#print axioms rf_bat
#print axioms rf_rel

end R1Z.RfBat

end
