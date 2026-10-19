import R1Z.RfBat

/-! D64 hRel, pure part (no Aeneas): the relation limb functionals `relMat` on a unit
coordinate, and the Rust relation coefficients (builder 4 `coef`, z9b.rs
`design_relations` with line reading 1) as the `relR1` coefficients.

* `iotaB_unit`: with `fp` injective, `iotaB` of the unit coordinate `8c + m` is the
  single vector `wb m` at the cell `batCell fp c`;
* `relMat_unit`: `relMat` at `8c + m` is limb `(rows y).2` of `R(c) · wb m`, with
  `R(c)` the `relR1` value of the unit vector at `batCell fp c`;
* `coefM`: the `K` model of the Rust `coef(rho, i)` (kind `kd`: 0 S2a, 1 S2b, 2 S1,
  3 C_u, 4 L_u at the query `U`), with the Rust inputs as functions: `A2, A3` the
  openings 2, 3, `Q` the M31 quarter, `W2` the second dual fold, `Fp` the folded
  positions, `LF t` the line-fold value of slot `t`, `NL e` the natural basis at the
  stored log-16 node;
* `coefM_eq`: under the identifications of those inputs, `coefM = R(c)` for the
  relation `relOf kd U`. -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertRel

open scoped BigOperators
open R0P R0Z.HonestView R1Z.Batched R1Z.VerifierRelationsR1 R1Z.PredicateR1 R1Z.RfBat

attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-! ### The cells of the support -/

theorem round0_eq {nf : ℕ} (fp : Fin nf → Fin 262144) (c : Fin (78 + nf)) (j : Fin 7) :
    (R1Bat.round0 j = batCell fp c) ↔ c.val = j.val := by
  have hj := j.isLt
  unfold batCell
  split_ifs with h1 h2 h3
  · simp only [R1Bat.round0.injEq, Fin.ext_iff]
    constructor <;> intro e <;> omega
  · simp only [false_iff]; omega
  · simp only [false_iff]; omega
  · simp only [false_iff]; omega

theorem round1_eq {nf : ℕ} (fp : Fin nf → Fin 262144) (c : Fin (78 + nf)) (j : Fin 7) :
    (R1Bat.round1 j = batCell fp c) ↔ c.val = 7 + j.val := by
  have hj := j.isLt
  unfold batCell
  split_ifs with h1 h2 h3
  · simp only [false_iff]; omega
  · simp only [R1Bat.round1.injEq, Fin.ext_iff]
    constructor <;> intro e <;> omega
  · simp only [false_iff]; omega
  · simp only [false_iff]; omega

theorem final_eq {nf : ℕ} (fp : Fin nf → Fin 262144) (c : Fin (78 + nf)) (e : Fin 64) :
    (R1Bat.final e = batCell fp c) ↔ c.val = 14 + nf + e.val := by
  have he := e.isLt
  unfold batCell
  split_ifs with h1 h2 h3
  · simp only [false_iff]; omega
  · simp only [false_iff]; omega
  · simp only [false_iff]; omega
  · simp only [R1Bat.final.injEq, Fin.ext_iff]
    constructor <;> intro e <;> omega

theorem folded_eq {nf : ℕ} (fp : Fin nf → Fin 262144) (c : Fin (78 + nf)) (p : Fin 262144) :
    (R1Bat.folded p = batCell fp c) ↔
      ∃ h : 14 ≤ c.val ∧ c.val < 14 + nf, fp ⟨c.val - 14, by omega⟩ = p := by
  unfold batCell
  split_ifs with h1 h2 h3
  · simp only [false_iff]
    rintro ⟨h, -⟩
    omega
  · simp only [false_iff]
    rintro ⟨h, -⟩
    omega
  · simp only [R1Bat.folded.injEq]
    constructor
    · intro e
      exact ⟨⟨by omega, h3⟩, e.symm⟩
    · rintro ⟨_, e⟩
      exact e.symm
  · simp only [false_iff]
    rintro ⟨h, -⟩
    omega

theorem batCell_inj {nf : ℕ} {fp : Fin nf → Fin 262144} (hinj : Function.Injective fp) :
    Function.Injective (batCell fp) := by
  intro c d h
  apply Fin.ext
  have hc := c.isLt
  have hd := d.isLt
  by_cases c1 : c.val < 7
  · have e := (round0_eq fp d ⟨c.val, c1⟩).1 (by
      rw [← h]; unfold batCell; rw [dif_pos c1])
    exact e.symm
  by_cases c2 : c.val < 14
  · have e := (round1_eq fp d ⟨c.val - 7, by omega⟩).1 (by
      rw [← h]; unfold batCell; rw [dif_neg c1, dif_pos c2])
    simp only at e
    omega
  by_cases c3 : c.val < 14 + nf
  · obtain ⟨⟨hd1, hd2⟩, e⟩ := (folded_eq fp d (fp ⟨c.val - 14, by omega⟩)).1 (by
      rw [← h]; unfold batCell; rw [dif_neg c1, dif_neg c2, dif_pos c3])
    have := congrArg Fin.val (hinj e)
    simp only at this
    omega
  · have e := (final_eq fp d ⟨c.val - 14 - nf, by omega⟩).1 (by
      rw [← h]; unfold batCell; rw [dif_neg c1, dif_neg c2, dif_neg c3])
    simp only at e
    omega

/-! ### `relMat` on a unit coordinate -/

variable (wb : Module.Basis (Fin 8) F K)

theorem cellL_unit {nf : ℕ} (c d : Fin (78 + nf)) (m : Fin 8) :
    cellL wb d (fun c' => if fpb nf (c, m) = c' then (1 : F) else 0) = if d = c then wb m else 0 := by
  show ∑ k, (if fpb nf (c, m) = fpb nf (d, k) then (1 : F) else 0) • wb k = _
  simp only [(fpb nf).apply_eq_iff_eq, Prod.mk.injEq]
  by_cases h : d = c
  · subst h
    simp only [true_and, if_true, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq]
    simp
  · have h' : ¬ c = d := fun e => h e.symm
    simp only [h', false_and, if_false, zero_smul, Finset.sum_const_zero]
    rw [if_neg h]

theorem iotaB_unit {nf : ℕ} (fp : Fin nf → Fin 262144) (hinj : Function.Injective fp)
    (c : Fin (78 + nf)) (m : Fin 8) (b : R1Bat) :
    iotaB wb fp (fun c' => if fpb nf (c, m) = c' then (1 : F) else 0) b =
      if batCell fp c = b then wb m else 0 := by
  cases b with
  | round0 i =>
    show cellL wb ⟨i.val, _⟩ _ = _
    rw [cellL_unit]
    by_cases h : (⟨i.val, by omega⟩ : Fin (78 + nf)) = c
    · rw [if_pos h, if_pos (by rw [← h, batCell_round0])]
    · rw [if_neg h, if_neg (fun e => h ((batCell_inj hinj) (by rw [batCell_round0]; exact e.symm)))]
  | round1 i =>
    show cellL wb ⟨7 + i.val, _⟩ _ = _
    rw [cellL_unit]
    by_cases h : (⟨7 + i.val, by omega⟩ : Fin (78 + nf)) = c
    · rw [if_pos h, if_pos (by rw [← h, batCell_round1])]
    · rw [if_neg h, if_neg (fun e => h ((batCell_inj hinj) (by rw [batCell_round1]; exact e.symm)))]
  | final e =>
    show cellL wb ⟨14 + nf + e.val, _⟩ _ = _
    rw [cellL_unit]
    by_cases h : (⟨14 + nf + e.val, by omega⟩ : Fin (78 + nf)) = c
    · rw [if_pos h, if_pos (by rw [← h, batCell_final])]
    · rw [if_neg h, if_neg (fun e2 => h ((batCell_inj hinj) (by rw [batCell_final]; exact e2.symm)))]
  | folded p =>
    show (if h : ∃ f : Fin nf, fp f = p then
      cellL wb ⟨14 + (Classical.choose h).val, by omega⟩ else 0) _ = _
    by_cases h : ∃ f : Fin nf, fp f = p
    · rw [dif_pos h, cellL_unit]
      have hp : batCell fp ⟨14 + (Classical.choose h).val, by omega⟩ = R1Bat.folded p := by
        rw [batCell_folded, Classical.choose_spec h]
      by_cases h2 : (⟨14 + (Classical.choose h).val, by omega⟩ : Fin (78 + nf)) = c
      · rw [if_pos h2, if_pos (by rw [← h2, hp])]
      · rw [if_neg h2, if_neg (fun e => h2 ((batCell_inj hinj) (hp.trans e.symm)))]
    · rw [dif_neg h, LinearMap.zero_apply, if_neg]
      intro e
      obtain ⟨_, e2⟩ := (folded_eq fp c p).1 e.symm
      exact h ⟨_, e2⟩

/-- `relMat` at the coordinate `8c + m`. -/
theorem relMat_unit (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) {nf q : ℕ}
    (fp : Fin nf → Fin 262144) (hinj : Function.Injective fp) (rows : Fin q → R1Rel × Fin 8)
    (y : Fin q) (c : Fin (78 + nf)) (m : Fin 8) :
    relMat wb π ch fp rows y (fpb nf (c, m)) =
      wb.repr (relR1 π ch (Pi.single (batCell fp c) (1 : K) : R1Bat → K) (rows y).1 * wb m) (rows y).2 := by
  have hv : iotaB wb fp (fun c' => if fpb nf (c, m) = c' then (1 : F) else 0) =
      wb m • Pi.single (batCell fp c) (1 : K) := by
    funext b
    rw [iotaB_unit wb fp hinj c m b, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    by_cases h : batCell fp c = b
    · rw [if_pos h, if_pos h.symm, mul_one]
    · rw [if_neg h, if_neg (fun e => h e.symm), mul_zero]
  show wb.repr (relR1 π ch (iotaB wb fp (fun c' => if fpb nf (c, m) = c' then (1 : F) else 0))
    (rows y).1) (rows y).2 = _
  rw [hv, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

/-! ### Indicator sums -/

theorem sum_ind {n : ℕ} (f : ℕ → K) (a b : ℕ) :
    ∑ i : Fin n, f i.val * (if a = b + i.val then 1 else 0) =
      if b ≤ a ∧ a < b + n then f (a - b) else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a - b, by omega⟩]
    · rw [if_pos (by simp only; omega), mul_one]
    · intro i _ hi
      rw [if_neg (fun e => hi (Fin.ext (by simp only; omega))), mul_zero]
    · intro hn; exact absurd (Finset.mem_univ _) hn
  · refine Finset.sum_eq_zero fun i _ => ?_
    have := i.isLt
    rw [if_neg (by omega), mul_zero]

theorem sum_ind' {n : ℕ} (f : ℕ → K) (a b : ℕ) :
    ∑ i : Fin n, (if a = b + i.val then 1 else 0) * f i.val =
      if b ≤ a ∧ a < b + n then f (a - b) else 0 := by
  rw [← sum_ind f a b]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem sum_pow {n : ℕ} (A : K) (a b : ℕ) :
    ∑ i : Fin n, A ^ i.val * (if a = b + i.val then 1 else 0) =
      if b ≤ a ∧ a < b + n then A ^ (a - b) else 0 :=
  sum_ind (fun k => A ^ k) a b

/-! ### The Rust coefficient model -/

/-- The relation of descriptor `(kd, U)`. -/
def relOf (kd U : ℕ) : R1Rel :=
  if kd = 0 then .s2a else if kd = 1 then .s2b else if kd = 2 then .s1
  else if kd = 3 then .circ ⟨U % 262144, Nat.mod_lt _ (by norm_num)⟩
  else .line ⟨U % 262144, Nat.mod_lt _ (by norm_num)⟩

/-- The Rust `coef(rho, i)` as a `K` value. -/
def coefM (nf : ℕ) (A2 A3 Q : K) (W2 : ℕ → K) (Fp : ℕ → ℕ) (LF NL : ℕ → K) (kd U i : ℕ) : K :=
  if kd = 0 then (if i = 0 then 1 else 0) + (if i = 4 then 1 else 0)
  else if kd = 1 then (if i < 7 then 0 - Q * A2 ^ i else if i = 7 ∨ i = 11 then 1 else 0)
  else if kd = 2 then
    (if i < 7 then 0 else if i < 14 then A3 ^ (i - 7) else if i < 14 + nf then 0 else 0 - W2 (i - (14 + nf)))
  else if kd = 3 then
    (if i < 14 then 0 else if i < 14 + nf then (if Fp (i - 14) = U then 1 else 0) else 0)
  else if i < 14 then 0
  else if i < 14 + nf then (if Fp (i - 14) / 4 = U / 4 then 1 else 0) * LF (Fp (i - 14) % 4)
  else 0 - NL (i - (14 + nf))

theorem pairFold_zero (c inv : K) :
    AspisV5ComponentCConcreteFoldLinearity.pairFoldValue c inv 0 0 = 0 := by
  simp [AspisV5ComponentCConcreteFoldLinearity.pairFoldValue]

theorem lineFold_zero (a i0 i1 i2 : K) (v : Fin 4 → K) (hv : ∀ s, v s = 0) :
    AspisV5ComponentCConcreteFoldLinearity.lineFoldValue a i0 i1 i2 v = 0 := by
  simp only [AspisV5ComponentCConcreteFoldLinearity.lineFoldValue, hv, pairFold_zero]

/-- The Rust coefficient is the `relR1` coefficient at the cell. -/
theorem coefM_eq (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) {nf : ℕ} (fp : Fin nf → Fin 262144)
    (Fp : ℕ → ℕ) (hFp : ∀ f : Fin nf, Fp f.val = (fp f).val)
    (A2 A3 Q : K) (hA2 : A2 = ch.opening 2) (hA3 : A3 = ch.opening 3)
    (hQ : Q = AspisR1.RoundPairing.quarter) (W2 : ℕ → K) (hW2 : ∀ e : Fin 64, W2 e.val = w2 π ch e)
    (kd U : ℕ) (LF NL : ℕ → K) (hU1 : U < 262144)
    (hU2 : 3 ≤ kd → (⟨U % 262144, Nat.mod_lt _ (by norm_num)⟩ : Fin 262144) ∈ ch.queries)
    (hLF : 4 ≤ kd → ∀ t, t < 4 → LF t = AspisV5ComponentCConcreteFoldLinearity.lineFoldValue A3
      (algebraMap (ZMod AspisCircleGroupOrder.P) K (R1Z.BatchedAlgebra.lineInverse ⟨U / 4, by omega⟩ 0))
      (algebraMap (ZMod AspisCircleGroupOrder.P) K (R1Z.BatchedAlgebra.lineInverse ⟨U / 4, by omega⟩ 1))
      (algebraMap (ZMod AspisCircleGroupOrder.P) K (R1Z.BatchedAlgebra.lineInverse ⟨U / 4, by omega⟩ 2))
      (fun s => if t = s.val then 1 else 0))
    (hNL : 4 ≤ kd → ∀ e, e < 64 → NL e = AspisCircleTensorBinding.naturalLineValue
      (algebraMap (ZMod AspisCircleGroupOrder.P) K
        (AspisV5FriReleasedLineGeometry.storedLine16X ⟨U / 4, by omega⟩)) e)
    (c : Fin (78 + nf)) :
    coefM nf A2 A3 Q W2 Fp LF NL kd U c.val =
      relR1 π ch (Pi.single (batCell fp c) (1 : K) : R1Bat → K) (relOf kd U) := by
  have hc := c.isLt
  have v0 : ∀ j : Fin 7, (Pi.single (batCell fp c) (1 : K) : R1Bat → K) (.round0 j) =
      if c.val = 0 + j.val then 1 else 0 := by
    intro j
    rw [Pi.single_apply, zero_add]
    exact if_congr (round0_eq fp c j) rfl rfl
  have v1 : ∀ j : Fin 7, (Pi.single (batCell fp c) (1 : K) : R1Bat → K) (.round1 j) =
      if c.val = 7 + j.val then 1 else 0 := by
    intro j
    rw [Pi.single_apply]
    exact if_congr (round1_eq fp c j) rfl rfl
  have vf : ∀ e : Fin 64, (Pi.single (batCell fp c) (1 : K) : R1Bat → K) (.final e) =
      if c.val = (14 + nf) + e.val then 1 else 0 := by
    intro e
    rw [Pi.single_apply]
    exact if_congr (final_eq fp c e) rfl rfl
  have vw : ∀ p : Fin 262144, (Pi.single (batCell fp c) (1 : K) : R1Bat → K) (.folded p) =
      if 14 ≤ c.val ∧ c.val < 14 + nf ∧ Fp (c.val - 14) = p.val then 1 else 0 := by
    intro p
    rw [Pi.single_apply]
    refine if_congr ?_ rfl rfl
    rw [folded_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, e⟩
      have hF := hFp ⟨c.val - 14, by omega⟩
      simp only at hF
      exact ⟨h1, h2, by rw [hF, e]⟩
    · rintro ⟨h1, h2, e⟩
      have hF := hFp ⟨c.val - 14, by omega⟩
      simp only at hF
      exact ⟨⟨h1, h2⟩, Fin.ext (by rw [← hF]; exact e)⟩
  have v00 : (Pi.single (batCell fp c) (1 : K) : R1Bat → K) (.round0 0) = if c.val = 0 then 1 else 0 := by
    rw [v0]; rfl
  have v04 : (Pi.single (batCell fp c) (1 : K) : R1Bat → K) (.round0 4) = if c.val = 4 then 1 else 0 := by
    rw [v0]; rfl
  have v10 : (Pi.single (batCell fp c) (1 : K) : R1Bat → K) (.round1 0) = if c.val = 7 then 1 else 0 := by
    rw [v1]; rfl
  have v14 : (Pi.single (batCell fp c) (1 : K) : R1Bat → K) (.round1 4) = if c.val = 11 then 1 else 0 := by
    rw [v1]; rfl
  unfold coefM relOf
  by_cases k0 : kd = 0
  · rw [if_pos k0, if_pos k0, relR1_s2a, v00, v04]
  rw [if_neg k0, if_neg k0]
  by_cases k1 : kd = 1
  · rw [if_pos k1, if_pos k1, relR1_s2b, v10, v14]
    simp only [v0, sum_pow, ← hA2, ← hQ]
    split_ifs <;> first | omega | (simp only [Nat.sub_zero]; ring) | ring
  rw [if_neg k1, if_neg k1]
  by_cases k2 : kd = 2
  · rw [if_pos k2, if_pos k2, relR1_s1]
    simp only [v1, vf, sum_pow, ← hA3, ← hW2, sum_ind]
    split_ifs <;> first | omega | ring
  rw [if_neg k2, if_neg k2]
  have hUm : U % 262144 = U := Nat.mod_eq_of_lt hU1
  by_cases k3 : kd = 3
  · rw [if_pos k3, if_pos k3, relR1_circ π ch _ _ (hU2 (by omega)), vw]
    simp only [hUm]
    split_ifs <;> first | omega | rfl
  rw [if_neg k3, if_neg k3, relR1_line π ch _ _ (hU2 (by omega)),
    AspisV5ComponentCConcreteFoldLinearity.lineFoldLayer_apply]
  have hd : parent16 (⟨U % 262144, Nat.mod_lt _ (by norm_num)⟩ : Fin 262144) = ⟨U / 4, by omega⟩ :=
    Fin.ext (by simp only [parent16]; rw [hUm])
  have hsl : ∀ m : AspisR1.RepeatedLift.SecondCoefficients K, AspisR1.RepeatedLift.secondLinear m
      ⟨U / 4, by omega⟩ = ∑ e : Fin 64, m e * AspisCircleTensorBinding.naturalLineValue
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (AspisV5FriReleasedLineGeometry.storedLine16X ⟨U / 4, by omega⟩)) e.val := by
    intro m
    exact AspisV5FriConcreteEncoderApplicability.naturalCoefficientPolynomial_eval_eq_sum (by norm_num) m _
  rw [hd, hsl]
  have hfin : ∀ e : Fin 64, finalOf (Pi.single (batCell fp c) (1 : K) : R1Bat → K) e =
      if c.val = (14 + nf) + e.val then 1 else 0 := fun e => vf e
  have hfw : ∀ s : Fin 4, foldedWordOf (Pi.single (batCell fp c) (1 : K) : R1Bat → K)
      (AspisV5ComponentCConcreteFoldLinearity.childIndex (⟨U / 4, by omega⟩ : Fin 65536) s) =
      if 14 ≤ c.val ∧ c.val < 14 + nf ∧ Fp (c.val - 14) = 4 * (U / 4) + s.val then 1 else 0 :=
    fun s => vw _
  simp only [hfin, sum_ind', hfw, ← hA3]
  by_cases h14 : c.val < 14
  · rw [if_pos h14, if_neg (show ¬ (14 + nf ≤ c.val ∧ c.val < 14 + nf + 64) by omega), sub_zero,
      lineFold_zero]
    intro s
    rw [if_neg (by omega)]
  rw [if_neg h14]
  by_cases hn : c.val < 14 + nf
  · rw [if_pos hn, if_neg (show ¬ (14 + nf ≤ c.val ∧ c.val < 14 + nf + 64) by omega), sub_zero]
    by_cases e : Fp (c.val - 14) / 4 = U / 4
    · rw [if_pos e, one_mul, hLF (by omega) (Fp (c.val - 14) % 4) (Nat.mod_lt _ (by norm_num))]
      congr 1
      funext s
      have hs := s.isLt
      split_ifs <;> first | rfl | omega
    · rw [if_neg e, zero_mul, lineFold_zero]
      intro s
      have := s.isLt
      rw [if_neg (by omega)]
  · rw [if_neg hn, if_pos (show 14 + nf ≤ c.val ∧ c.val < 14 + nf + 64 by omega),
      hNL (by omega) (c.val - (14 + nf)) (by omega), lineFold_zero, zero_sub]
    intro s
    rw [if_neg (by omega)]

#print axioms round0_eq
#print axioms folded_eq
#print axioms batCell_inj
#print axioms iotaB_unit
#print axioms relMat_unit
#print axioms sum_ind
#print axioms coefM_eq

end R1Z.CertRel

end
