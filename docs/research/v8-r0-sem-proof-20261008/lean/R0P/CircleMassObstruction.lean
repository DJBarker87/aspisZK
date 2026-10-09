import R0P.CircleSampler

/-! G22 diagnostic: a heavy residue of the existing one-block modulo sampler.
All fiber counting is symbolic over abstract finite types. -/
set_option autoImplicit false
namespace R0P.CircleMassObstruction
open FS R0C.ModuloCounting R0P.SemSource
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.SourceDuplexStep AspisV8R19.R599CanonicalFieldTuple
open AspisV5ComponentCQM31TowerExact
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The residues below the remainder have an extra preimage. -/
theorem heavy_fiber_card (B n : Nat) (hn : 0 < n) (y : Fin n) (hy : y.val < B % n) :
    B / n + 1 ≤ Fintype.card {x : Fin B // reduce hn x = y} := by
  let f : Fin (B / n + 1) → {x : Fin B // reduce hn x = y} := fun k =>
    ⟨⟨y.val + n * k.val, by
        have hk : k.val ≤ B / n := Nat.le_of_lt_succ k.isLt
        have hd := Nat.mod_add_div B n
        have hm := Nat.mul_le_mul_left n hk
        omega⟩, by
      apply Fin.ext
      change (y.val + n * k.val) % n = y.val
      rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod, Nat.add_zero,
        Nat.mod_mod, Nat.mod_eq_of_lt y.isLt]⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    have he := congrArg (fun x : {x : Fin B // reduce hn x = y} => x.val.val) hab
    change y.val + n * a.val = y.val + n * b.val at he
    nlinarith
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

theorem encoded_mass_lower {A E : Type} [Fintype A] [Fintype E]
    {B n : Nat} (hn : 0 < n) (input : A ≃ Fin B) (output : Fin n ≃ E)
    (y : E) (hy : (output.symm y).val < B % n) :
    ((B / n + 1 : Nat) : ℚ) / B ≤
      mean (fun a => indicator (output (reduce hn (input a)) = y)) := by
  rw [R0C.Counting.mean_indicator_card]
  have hc : Fintype.card A = B := (Fintype.card_congr input).trans (Fintype.card_fin B)
  rw [hc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have he : {a : A // output (reduce hn (input a)) = y} ≃
      {x : Fin B // reduce hn x = output.symm y} :=
    input.subtypeEquiv (fun a => output.apply_eq_iff_eq_symm_apply)
  have h := (heavy_fiber_card B n hn (output.symm y) hy).trans
    (Fintype.card_congr he).symm.le
  exact_mod_cast h

theorem encoded_mass_gt_uniform {A E : Type} [Fintype A] [Fintype E]
    {B n : Nat} (hB : 0 < B) (hn : 0 < n) (input : A ≃ Fin B) (output : Fin n ≃ E)
    (y : E) (hy : (output.symm y).val < B % n) :
    1 / (n : ℚ) < mean (fun a => indicator (output (reduce hn (input a)) = y)) := by
  have hBq : (0 : ℚ) < B := by exact_mod_cast hB
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hlt : B < (B / n + 1) * n := by
    have hd := Nat.mod_add_div B n
    have hm := Nat.mod_lt B hn
    nlinarith
  have hltq : (B : ℚ) < ((B / n + 1 : Nat) : ℚ) * (n : ℚ) := by exact_mod_cast hlt
  apply lt_of_lt_of_le _ (encoded_mass_lower hn input output y hy)
  apply (div_lt_div_iff₀ hnq hBq).mpr
  simpa only [one_mul, mul_one, mul_comm] using hltq

#print axioms heavy_fiber_card
#print axioms encoded_mass_lower
#print axioms encoded_mass_gt_uniform

/-- Four symbolic limbs, before specializing the small fallback parameter. -/
theorem qm31Rank_symm_value (t : CircleParam) :
    (qm31Rank.symm t).val = t.re.re.val + P * t.re.im.val +
      P ^ 2 * t.im.re.val + P ^ 3 * t.im.im.val := by
  change (finFunctionFinEquiv (fieldTuple t)).val = _
  rw [finFunctionFinEquiv_apply]
  simp [fieldTuple, Fin.sum_univ_succ]
  ring

theorem fallback1_rank : (qm31Rank.symm circleFallbackParameter1).val = P ^ 2 + 1 := by
  rw [qm31Rank_symm_value]
  change ZMod.val (1 : M31Exact) + P * ZMod.val (0 : M31Exact) +
    P ^ 2 * ZMod.val (1 : M31Exact) + P ^ 3 * ZMod.val (0 : M31Exact) = P ^ 2 + 1
  simp only [ZMod.val_one, ZMod.val_zero, mul_zero, mul_one, add_zero]
  exact Nat.add_comm _ _

theorem fallback1_heavy :
    (qm31Rank.symm circleFallbackParameter1).val < 256 ^ 32 % P ^ 4 := by
  rw [fallback1_rank]
  norm_num [P]

theorem fallback1_mass_gt :
    1 / (P ^ 4 : ℚ) < mean (fun s : State => indicator (qm31Sample s = circleFallbackParameter1)) := by
  simpa only [qm31Sample, Nat.cast_pow, Nat.cast_ofNat] using
    encoded_mass_gt_uniform (by positivity : 0 < 256 ^ 32) (by norm_num [P] : 0 < P ^ 4)
      R0C.ModuloField.blockRank qm31Rank circleFallbackParameter1 fallback1_heavy

/-- The requested G22 first-row 1/P⁴ theorem is false for the current sampler. -/
theorem not_circleSample0_mass :
    ¬ mean (fun s : State => indicator (z0Bad' (circleSample0 s))) ≤ 1 / (P ^ 4 : ℚ) := by
  rw [mean_congr (fun s => indicator_iff (circleSample0_bad_iff s))]
  exact not_le_of_gt fallback1_mass_gt

#print axioms qm31Rank_symm_value
#print axioms fallback1_rank
#print axioms fallback1_heavy
#print axioms fallback1_mass_gt
#print axioms not_circleSample0_mass

theorem fallback0_rank : (qm31Rank.symm circleFallbackParameter0).val = P ^ 2 := by
  rw [qm31Rank_symm_value]
  change ZMod.val (0 : M31Exact) + P * ZMod.val (0 : M31Exact) +
    P ^ 2 * ZMod.val (1 : M31Exact) + P ^ 3 * ZMod.val (0 : M31Exact) = P ^ 2
  simp only [ZMod.val_one, ZMod.val_zero, mul_zero, mul_one, add_zero, zero_add]

theorem fallback0_heavy :
    (qm31Rank.symm circleFallbackParameter0).val < 256 ^ 32 % P ^ 4 := by
  rw [fallback0_rank]
  norm_num [P]

theorem fallback0_mass_gt :
    1 / (P ^ 4 : ℚ) < mean (fun s : State => indicator (qm31Sample s = circleFallbackParameter0)) := by
  simpa only [qm31Sample, Nat.cast_pow, Nat.cast_ofNat] using
    encoded_mass_gt_uniform (by positivity : 0 < 256 ^ 32) (by norm_num [P] : 0 < P ^ 4)
      R0C.ModuloField.blockRank qm31Rank circleFallbackParameter0 fallback0_heavy

/-- Row 25 also fails the ideal target even with its requested side condition. -/
theorem circleSample1_mass_counterexample :
    circleFallback0 ≠ circleFallback1 ∧
    ¬ mean (fun s : State => indicator
      (R0C.SemStatement.z1Bad circleFallback0 (circleSample1 s))) ≤ 1 / (P ^ 4 : ℚ) := by
  refine ⟨circleFallback_ne, not_le_of_gt ?_⟩
  apply lt_of_lt_of_le fallback0_mass_gt
  apply mean_mono
  intro s
  apply indicator_mono
  intro hs
  apply Or.inr
  change circleSampleParameterWith circleFallback1 (qm31Sample s) = circleFallback0
  rw [hs]
  exact circleSampleParameterWith_accepted _ _ circleFallbackParameter0_im

#print axioms fallback0_rank
#print axioms fallback0_heavy
#print axioms fallback0_mass_gt
#print axioms circleSample1_mass_counterexample
end
end R0P.CircleMassObstruction
