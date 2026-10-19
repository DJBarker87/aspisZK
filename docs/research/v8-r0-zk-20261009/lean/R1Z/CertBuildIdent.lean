import R1Z.CertBuildFill
import R1Z.RfChain

/-! D57.3: the extracted chain-target builder computes the Lean ChainT0K4
targets.  `chain_ident`: if `fill_tq al hinv = ok r`, the tower premise holds,
the alpha limbs encode `a` (`ha`) and `hinv` encodes `(a₉ - ½)⁻¹` (`hH`), then
`chainTarget B hB a i t = φ (r[i·1084 + t])` for all `i t` — the identification
`hChain` of `check_sound`, with `Rf`'s `normalize`/`finalVal` (z9c `chain_targets`). -/

set_option autoImplicit false

noncomputable section

namespace R1Z.CertBuild
open Aeneas Aeneas.Std Result R1Z.CertCheck R0P R1Z.RfChain R0Z.K4
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K} (B : PackBasis F) (φ : ZP →+* ↥F)

theorem pack4_sub (f g : Fin 4 → K) : pack4 B (fun l => f l - g l) = pack4 B f - pack4 B g := by
  unfold pack4; ring

/-- `limbs` inverts `pack4` on base-field limbs. -/
theorem limbs_pack4 (hB : PackField B) (w : Fin 4 → F) :
    limbs B hB (pack4 B (fun l => (w l : K))) = w := by
  have hx : pack4 B (fun l => (w l : K)) ∈ K4 B hB := (mem_K4_iff_pack4 B hB).2 ⟨_, fun j => (w j).2, rfl⟩
  have e := pack4_limbs B hB hx
  have hz : pack4 B (fun l => ((limbs B hB (pack4 B (fun l => (w l : K))) l : K) - (w l : K))) = 0 := by
    rw [pack4_sub, e, sub_self]
  have := (pack4_eq_zero_iff B _ (fun j => F.sub_mem (limbs B hB _ j).2 (w j).2)).1 hz
  funext l
  exact Subtype.ext (sub_eq_zero.1 (this l))

theorem fpe_val (q : Fin 271) (l : Fin 4) : (fpe (q, l)).val = l.val + 4 * q.val := by
  simp [fpe, finProdFinEquiv]

/-- The Rust unit vector is `unflat e_i`. -/
theorem unflat_unit (i : Fin 1084) (q : Fin 271) :
    unflatL B (fun t => if i = t then (1 : F) else 0) q = Vu B (i.val / 4) (i.val % 4) q.val := by
  rw [unflatL_apply]
  have key : ∀ l : Fin 4, (i = fpe (q, l)) ↔ (q.val = i.val / 4 ∧ l.val = i.val % 4) := by
    intro l
    rw [Fin.ext_iff, fpe_val]
    omega
  unfold pack4 Vu tb
  beta_reduce
  by_cases hq : q.val = i.val / 4
  · rw [if_pos hq]
    simp only [key, hq, true_and]
    rcases (by omega : i.val % 4 = 0 ∨ i.val % 4 = 1 ∨ i.val % 4 = 2 ∨ i.val % 4 = 3) with e | e | e | e <;>
      simp [e]
  · rw [if_neg hq]
    have hn : ∀ l : Fin 4, ¬ (i = fpe (q, l)) := fun l h => hq ((key l).1 h).1
    simp [hn]

/-- One `roundK` step is `pev ∘ reconRound`. -/
theorem roundK_eq (V : ℕ → K) (V' : Fin 271 → K) (hVV : ∀ (q : ℕ) (h : q < 271), V q = V' ⟨q, h⟩)
    (j : Fin 10) (prev A : K) :
    roundK V j.val prev A = pev (reconRound V' j prev) A := by
  have hj := j.2
  have e0 : reconRound V' j prev 0 = V (1 + 27 * j.val) := by
    rw [hVV _ (by omega)]; simp [reconRound]; try rfl
  have e1 : reconRound V' j prev 1 = prev - (V (1 + 27 * j.val) + V (1 + 27 * j.val)) -
      ∑ t ∈ Finset.Ico 1 27, V (1 + 27 * j.val + t) := by
    have hs : ∑ t ∈ Finset.Ico 1 27, V (1 + 27 * j.val + t) = ∑ k : Fin 26, V' (idx j k.succ) := by
      rw [Finset.sum_Ico_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hVV _ (by omega)]
      congr 1
      exact Fin.ext (by simp [idx]; omega)
    rw [hs, hVV _ (by omega)]
    simp [reconRound]
    try rfl
  have e2 : ∀ x : Fin 26, reconRound V' j prev x.succ.succ = V (1 + 27 * j.val + (x.val + 1)) := by
    intro x
    rw [hVV _ (by omega)]
    have h0 : ¬ ((x.succ.succ : Fin 28).val = 0) := by simp
    have h1 : ¬ ((x.succ.succ : Fin 28).val = 1) := by simp
    simp only [reconRound, if_neg h0, if_neg h1]
    congr 1
  unfold pev roundK Hk Sk
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, e0, Fin.succ_zero_eq_one, e1]
  simp only [e2, Fin.val_zero, Fin.val_one, Fin.val_succ, pow_zero, mul_one, pow_one]
  have hH : (∑ t ∈ Finset.Ico 0 26, V (1 + 27 * j.val + 26 - t) * A ^ (26 - 1 - t)) * A * A =
      ∑ x : Fin 26, V (1 + 27 * j.val + (x.val + 1)) * A ^ (x.val + 1 + 1) := by
    rw [← Finset.range_eq_Ico, ← Finset.sum_range_reflect, Finset.sum_mul, Finset.sum_mul,
      ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx := x.2
    rw [show 1 + 27 * j.val + 26 - (26 - 1 - x.val) = 1 + 27 * j.val + (x.val + 1) by omega,
      show 26 - 1 - (26 - 1 - x.val) = x.val by omega]
    ring
  rw [← hH]
  ring

theorem prevR_eq (V : ℕ → K) (V' : Fin 271 → K) (hVV : ∀ (q : ℕ) (h : q < 271), V q = V' ⟨q, h⟩)
    (A : ℕ → K) (a : Fin 10 → K) (hA : ∀ (j : ℕ) (h : j < 10), A j = a ⟨j, h⟩) :
    ∀ n, n ≤ 10 → prevR V A n = prevAt a V' n
  | 0, _ => by rw [prevR, prevAt, hVV 0 (by norm_num)]; rfl
  | n + 1, hn => by
      rw [prevR, prevAt, dif_pos (by omega), prevR_eq V V' hVV A a hA n (by omega), hA n (by omega)]
      exact roundK_eq V V' hVV ⟨n, by omega⟩ _ _

theorem finalVal_eq (V : ℕ → K) (V' : Fin 271 → K) (hVV : ∀ (q : ℕ) (h : q < 271), V q = V' ⟨q, h⟩)
    (A : ℕ → K) (a : Fin 10 → K) (hA : ∀ (j : ℕ) (h : j < 10), A j = a ⟨j, h⟩) :
    finalVal a V' = prevR V A 10 := by
  rw [prevR_eq V V' hVV A a hA 10 le_rfl, prevAt, dif_pos (by norm_num)]
  rfl

#print axioms limbs_pack4
#print axioms unflat_unit
#print axioms roundK_eq
#print axioms finalVal_eq

end R1Z.CertBuild
