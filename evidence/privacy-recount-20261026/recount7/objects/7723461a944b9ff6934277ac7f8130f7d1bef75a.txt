import R1Z.LensR1
import R1Z.PoleN8

/-! Sem1Uniform (LOG D42.3) discharge, generic part.  The R1 χ sampler is
`qm31_sample` on the row-1 squeeze answer: the 32-byte block is ranked as a
256-bit integer (a bijection), reduced mod p⁴ (four base-p digits) and the
digits are packed injectively into QM31.  Restated from the spend path
(`ExtractedQM31SamplerCorrect.sample_total`, `SamplerNatModel.qm31Digits_value`,
`SourceSamplerByteRank.rank`, `ModuloField.blockRank`; SHAs in
zf1/sem1-uniform-evidence.json) as the hypothesis shape
`s1 b = emb ((rank b) % q)` with `rank` a bijection and `emb` injective
below `q`.

* `residue_card_le`: at most `n / q + 1` points of `Fin n` per residue mod q;
* `fibre_card_le`: hence every fibre of `s1` has at most `n / q + 1` points;
* `lens_mem_mass_le`: if a lens coordinate `u` feeds `s1` and the family
  index `lam` does not move with `u`, a family of `m` values is hit with mass
  at most `m · f / |U|` (f = fibre bound);
* `lens_qm31_mass_le`: for q = p⁴, n = 2^256 this is at most `m / (p⁴ − 1)`
  (exact: `m · (⌊2^256/p⁴⌋ + 1) / 2^256`), from the symbolic
  `(q − 1)(⌊n/q⌋ + 1) ≤ n` when `q² ≤ n`.
No concrete Finset over the 2^256 answers is evaluated. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SamplerLawR1
open R0Z R0Z.FsAbortBounds R1Z.LensR1
attribute [local instance] Classical.propDecidable

/-! ### Counting -/

/-- At most `n / q + 1` ranks below `n` have a given residue mod `q`. -/
theorem residue_card_le {U : Type} [Fintype U] {n : ℕ} (rank : U ≃ Fin n) (q t : ℕ)
    (hq : 0 < q) :
    (Finset.univ.filter (fun u => (rank u).val % q = t)).card ≤ n / q + 1 := by
  have hmaps : Set.MapsTo (fun u => (rank u).val / q)
      (↑(Finset.univ.filter (fun u => (rank u).val % q = t)) : Set U)
      (↑(Finset.range (n / q + 1)) : Set ℕ) := by
    intro u _
    show (rank u).val / q ∈ Finset.range (n / q + 1)
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (rank u).isLt.le)
  have hinj : Set.InjOn (fun u => (rank u).val / q)
      (↑(Finset.univ.filter (fun u => (rank u).val % q = t)) : Set U) := by
    intro u hu v hv huv
    have hmu : (rank u).val % q = t := (Finset.mem_filter.1 (Finset.mem_coe.1 hu)).2
    have hmv : (rank v).val % q = t := (Finset.mem_filter.1 (Finset.mem_coe.1 hv)).2
    have huv' : (rank u).val / q = (rank v).val / q := huv
    have hval : (rank u).val = (rank v).val :=
      calc (rank u).val = q * ((rank u).val / q) + (rank u).val % q := (Nat.div_add_mod _ _).symm
        _ = q * ((rank v).val / q) + (rank v).val % q := by rw [huv', hmu, hmv]
        _ = (rank v).val := Nat.div_add_mod _ _
    exact rank.injective (Fin.ext hval)
  calc (Finset.univ.filter (fun u => (rank u).val % q = t)).card
      ≤ (Finset.range (n / q + 1)).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = n / q + 1 := Finset.card_range _

/-- The fibres of `b ↦ emb (rank b mod q)` have at most `n / q + 1` points. -/
theorem fibre_card_le {U K : Type} [Fintype U] {n : ℕ} (rank : U ≃ Fin n) (q : ℕ) (hq : 0 < q)
    (emb : ℕ → K) (hemb : ∀ x y : ℕ, x < q → y < q → emb x = emb y → x = y)
    (s1 : U → K) (hs : ∀ b, s1 b = emb ((rank b).val % q)) (y : K) :
    (Finset.univ.filter (fun u => s1 u = y)).card ≤ n / q + 1 := by
  by_cases h : ∃ u₀, s1 u₀ = y
  · obtain ⟨u₀, hu₀⟩ := h
    refine (Finset.card_le_card ?_).trans (residue_card_le rank q ((rank u₀).val % q) hq)
    intro u hu
    have hu2 : s1 u = y := (Finset.mem_filter.1 hu).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    apply hemb _ _ (Nat.mod_lt _ hq) (Nat.mod_lt _ hq)
    rw [← hs, ← hs, hu2, hu₀]
  · have he : Finset.univ.filter (fun u => s1 u = y) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      intro u _ hu
      exact h ⟨u, hu⟩
    rw [he, Finset.card_empty]
    exact Nat.zero_le _

/-- A family of `m` values is hit by `s1` on at most `m · f` points. -/
theorem mem_card_le {U K : Type} [Fintype U] (s1 : U → K) (T0 : Finset K) (m f : ℕ)
    (hT : T0.card ≤ m) (hfib : ∀ y, (Finset.univ.filter (fun u => s1 u = y)).card ≤ f) :
    (Finset.univ.filter (fun u => s1 u ∈ T0)).card ≤ m * f := by
  have h := Finset.card_le_mul_card_image_of_maps_to (f := s1)
    (s := Finset.univ.filter (fun u => s1 u ∈ T0)) (t := T0)
    (fun u hu => (Finset.mem_filter.1 hu).2) f
    (fun y _ => (Finset.card_le_card (fun u hu => Finset.mem_filter.2
      ⟨Finset.mem_univ _, (Finset.mem_filter.1 hu).2⟩)).trans (hfib y))
  calc _ ≤ f * T0.card := h
    _ ≤ f * m := Nat.mul_le_mul_left f hT
    _ = m * f := Nat.mul_comm _ _

/-- Uniform mass form of `mem_card_le`. -/
theorem mass_mem_le {U K : Type} [Fintype U] (s1 : U → K) (T0 : Finset K) (m f : ℕ)
    (hT : T0.card ≤ m) (hfib : ∀ y, (Finset.univ.filter (fun u => s1 u = y)).card ≤ f) :
    mass (fun u => s1 u ∈ T0) ≤ ((m * f : ℕ) : ℚ) / Fintype.card U := by
  have h' : ((Finset.univ.filter (fun u => s1 u ∈ T0)).card : ℚ) ≤ ((m * f : ℕ) : ℚ) := by
    exact_mod_cast mem_card_le s1 T0 m f hT hfib
  have hsum : (∑ u, if s1 u ∈ T0 then (1 : ℚ) else 0) =
      ((Finset.univ.filter (fun u => s1 u ∈ T0)).card : ℚ) := by
    first
      | exact Finset.sum_boole _ _
      | simp only [Finset.sum_boole]
      | rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      | simp
  have key : (∑ u, if s1 u ∈ T0 then (1 : ℚ) else 0) / (Fintype.card U : ℚ) ≤
      ((m * f : ℕ) : ℚ) / Fintype.card U := by
    rw [hsum]
    exact div_le_div_of_nonneg_right h' (Nat.cast_nonneg _)
  unfold mass mean
  convert key using 3 with x _
  by_cases hx : s1 x ∈ T0 <;> simp [hx]

/-! ### The lens step -/

/-- If the lens coordinate `u` feeds `s1` and the family index `lam` does not
move with `u`, the event `s1 u ∈ T (lam s)` has mass at most `m · f / |U|`. -/
theorem lens_mem_mass_le {S U K : Type} [Fintype S] [Fintype U] [Nonempty U]
    (L : Lens S U) (lam : S → K) (s1 : U → K) (T : K → Finset K) (m f : ℕ)
    (hlam : ∀ s u, lam (L.set s u) = lam s) (hT : ∀ l, (T l).card ≤ m)
    (hfib : ∀ y, (Finset.univ.filter (fun u => s1 u = y)).card ≤ f) :
    mass (fun s => s1 (L.get s) ∈ T (lam s)) ≤ ((m * f : ℕ) : ℚ) / Fintype.card U := by
  have hδ : (0 : ℚ) ≤ ((m * f : ℕ) : ℚ) / Fintype.card U := by positivity
  have h := mass_cond_le (L.equiv (Classical.arbitrary U)) (fun _ => True)
    (fun s => s1 (L.get s) ∈ T (lam s)) _ hδ (fun _ _ _ _ => trivial) (by
      intro r x₀ _
      have hc : ∀ x, s1 (L.get ((L.equiv (Classical.arbitrary U)).symm (r, x))) ∈
          T (lam ((L.equiv (Classical.arbitrary U)).symm (r, x))) ↔ s1 x ∈ T (lam r.1) := by
        intro x
        rw [Lens.equiv_symm, L.get_set, hlam]
      rw [mass_congr _ _ hc]
      exact mass_mem_le s1 (T (lam r.1)) m f (hT _) hfib)
  calc mass (fun s => s1 (L.get s) ∈ T (lam s))
      = mass (fun s => True ∧ s1 (L.get s) ∈ T (lam s)) :=
        mass_congr _ _ (fun s => ⟨fun hs => ⟨trivial, hs⟩, fun hs => hs.2⟩)
    _ ≤ mass (fun _ : S => True) * (((m * f : ℕ) : ℚ) / Fintype.card U) := h
    _ ≤ 1 * (((m * f : ℕ) : ℚ) / Fintype.card U) :=
        mul_le_mul_of_nonneg_right (mass_le_one _) hδ
    _ = ((m * f : ℕ) : ℚ) / Fintype.card U := one_mul _

/-- The lens step with the rank-mod-q sampler: mass at most `m (n/q + 1) / n`. -/
theorem lens_sampler_mass_le {S U K : Type} [Fintype S] [Fintype U] [Nonempty U]
    (L : Lens S U) (lam : S → K) (s1 : U → K) (T : K → Finset K) (m n q : ℕ)
    (rank : U ≃ Fin n) (hq : 0 < q) (emb : ℕ → K)
    (hemb : ∀ x y : ℕ, x < q → y < q → emb x = emb y → x = y)
    (hs : ∀ b, s1 b = emb ((rank b).val % q))
    (hlam : ∀ s u, lam (L.set s u) = lam s) (hT : ∀ l, (T l).card ≤ m) :
    mass (fun s => s1 (L.get s) ∈ T (lam s)) ≤ ((m * (n / q + 1) : ℕ) : ℚ) / n := by
  have hc : Fintype.card U = n := by rw [Fintype.card_congr rank, Fintype.card_fin]
  have h := lens_mem_mass_le L lam s1 T m (n / q + 1) hlam hT
    (fibre_card_le rank q hq emb hemb s1 hs)
  rwa [hc] at h

/-! ### Arithmetic: from the exact bound to `m / (q − 1)` -/

/-- `(q − 1)(⌊n/q⌋ + 1) ≤ n` whenever `q² ≤ n`. -/
theorem pred_mul_div_succ_le (q n : ℕ) (hq : 0 < q) (hqq : q * q ≤ n) :
    (q - 1) * (n / q + 1) ≤ n := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have hf : r + 1 ≤ n / (r + 1) := (Nat.le_div_iff_mul_le hq).2 hqq
  have hr : r ≤ n / (r + 1) := Nat.le_of_succ_le hf
  rw [Nat.add_sub_cancel]
  calc r * (n / (r + 1) + 1) = r * (n / (r + 1)) + r := by rw [Nat.mul_add, Nat.mul_one]
    _ ≤ r * (n / (r + 1)) + n / (r + 1) := Nat.add_le_add_left hr _
    _ = (r + 1) * (n / (r + 1)) := (add_one_mul r (n / (r + 1))).symm
    _ ≤ n := Nat.mul_div_le n (r + 1)

theorem mul_div_le_div (m g n Q : ℕ) (hQ : 0 < Q) (hn : 0 < n) (h : Q * g ≤ n) :
    ((m * g : ℕ) : ℚ) / n ≤ (m : ℚ) / Q := by
  rw [div_le_div_iff₀ (by exact_mod_cast hn) (by exact_mod_cast hQ)]
  have hm : m * g * Q ≤ m * n :=
    calc m * g * Q = m * (Q * g) := by rw [Nat.mul_assoc, Nat.mul_comm g Q]
      _ ≤ m * n := Nat.mul_le_mul_left m h
  exact_mod_cast hm

/-! ### The M31 numerals (symbolic) -/

/-- `p⁴ · p⁴ ≤ 2^256` for `p = 2^31 − 1`. -/
theorem m31_q_sq_le : (2 ^ 31 - 1) ^ 4 * (2 ^ 31 - 1) ^ 4 ≤ 2 ^ 256 := by
  have h : (2 ^ 31 - 1 : ℕ) ≤ 2 ^ 31 := Nat.sub_le _ _
  have h4 : ((2 : ℕ) ^ 31 - 1) ^ 4 ≤ (2 ^ 31) ^ 4 := Nat.pow_le_pow_left h 4
  calc ((2 : ℕ) ^ 31 - 1) ^ 4 * (2 ^ 31 - 1) ^ 4 ≤ (2 ^ 31) ^ 4 * (2 ^ 31) ^ 4 :=
        Nat.mul_le_mul h4 h4
    _ ≤ 2 ^ 256 := by
        rw [← pow_mul, ← pow_add]
        exact Nat.pow_le_pow_right (by norm_num) (by norm_num)

/-- `p⁴ − 1 ≥ 2^123` for `p = 2^31 − 1` (as `PoleN8.m31_pow4`, with the slack). -/
theorem m31_pow4_pred : 2 ^ 123 ≤ (2 ^ 31 - 1) ^ 4 - 1 := by
  have h31 : (2 : ℕ) ^ 31 = 2 * 2 ^ 30 := by norm_num
  have h123 : (2 : ℕ) ^ 123 = 2 ^ 3 * (2 ^ 30) ^ 4 := by
    rw [← pow_mul, ← pow_add]
  have h4 : (4 : ℕ) ≤ 2 ^ 30 := by norm_num
  rw [h31, h123]
  obtain ⟨y, hy⟩ := Nat.exists_eq_add_of_le h4
  rw [hy, show 2 * (4 + y) - 1 = 2 * y + 7 by omega,
    show (2 * y + 7) ^ 4 = 2 ^ 3 * (4 + y) ^ 4 +
      (8 * y ^ 4 + 96 * y ^ 3 + 408 * y ^ 2 + 696 * y + 353) by ring]
  exact Nat.le_sub_one_of_lt (Nat.lt_add_of_pos_right (by positivity))

theorem m31_q_pos : 0 < (2 ^ 31 - 1) ^ 4 :=
  lt_of_lt_of_le (by positivity) (m31_pow4_pred.trans (Nat.sub_le _ _))

theorem m31_qpred_pos : 0 < (2 ^ 31 - 1) ^ 4 - 1 :=
  lt_of_lt_of_le (by positivity) m31_pow4_pred

/-- `(p⁴ − 1)(⌊2^256/p⁴⌋ + 1) ≤ 2^256`. -/
theorem m31_pred_mul_le :
    ((2 ^ 31 - 1) ^ 4 - 1) * (2 ^ 256 / (2 ^ 31 - 1) ^ 4 + 1) ≤ 2 ^ 256 :=
  pred_mul_div_succ_le _ _ m31_q_pos m31_q_sq_le

/-- The QM31 sampler on a lens coordinate of 2^256 points: a family of `m`
values is hit with mass at most `m / (p⁴ − 1)`. -/
theorem lens_qm31_mass_le {S U K : Type} [Fintype S] [Fintype U] [Nonempty U]
    (L : Lens S U) (lam : S → K) (s1 : U → K) (T : K → Finset K) (m : ℕ)
    (rank : U ≃ Fin (2 ^ 256)) (emb : ℕ → K)
    (hemb : ∀ x y : ℕ, x < (2 ^ 31 - 1) ^ 4 → y < (2 ^ 31 - 1) ^ 4 → emb x = emb y → x = y)
    (hs : ∀ b, s1 b = emb ((rank b).val % (2 ^ 31 - 1) ^ 4))
    (hlam : ∀ s u, lam (L.set s u) = lam s) (hT : ∀ l, (T l).card ≤ m) :
    mass (fun s => s1 (L.get s) ∈ T (lam s)) ≤ (m : ℚ) / (((2 ^ 31 - 1) ^ 4 - 1 : ℕ) : ℚ) :=
  (lens_sampler_mass_le L lam s1 T m (2 ^ 256) ((2 ^ 31 - 1) ^ 4) rank m31_q_pos emb hemb hs
    hlam hT).trans
    (mul_div_le_div m _ _ _ m31_qpred_pos (by positivity) m31_pred_mul_le)

/-- The pole term at N = 8 with `Q = p⁴ − 1`: still `≤ 2^-108`. -/
theorem pole_N8_M31_pred :
    ((8 : ℕ) : ℚ) * ((4096 : ℚ) / (((2 ^ 31 - 1) ^ 4 - 1 : ℕ) : ℚ)) ≤ 1 / 2 ^ 108 :=
  R1Z.PoleN8.pole_N8 _ m31_pow4_pred

#print axioms residue_card_le
#print axioms fibre_card_le
#print axioms mem_card_le
#print axioms mass_mem_le
#print axioms lens_mem_mass_le
#print axioms lens_sampler_mass_le
#print axioms pred_mul_div_succ_le
#print axioms mul_div_le_div
#print axioms m31_q_sq_le
#print axioms m31_pow4_pred
#print axioms m31_q_pos
#print axioms m31_qpred_pos
#print axioms m31_pred_mul_le
#print axioms lens_qm31_mass_le
#print axioms pole_N8_M31_pred
end R1Z.SamplerLawR1
