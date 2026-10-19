import CompPolyFactorMeanTools
import AspisV8R19.CausalFirstHitUnionBound

set_option autoImplicit false
noncomputable section
namespace AspisR1.FixedInputBankUnionBound
open AspisR1.CompPolyFactorMeanTools AspisV8R19.OracleResampling

variable {A B I J R : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

private theorem none_indicator_eq_abort (o : Option R) :
    AspisV8R19.CausalFirstHitUnionBound.indicator (o = none) = abortIndicator o := by
  cases o <;> simp [AspisV8R19.CausalFirstHitUnionBound.indicator, abortIndicator]

/-- Fixed-input bank union bound; the calls in each group may share all coins.
Only individual marginal error bounds are needed. -/
theorem bank_union_le (f : I → A → Option R) (g : J → B → Option R)
    (a b : ℚ)
    (hf : ∀ i, mean (fun x => abortIndicator (f i x)) ≤ a)
    (hg : ∀ j, mean (fun y => abortIndicator (g j y)) ≤ b) :
    mean (fun H : A × B => AspisV8R19.CausalFirstHitUnionBound.indicator
      (∃ i : I ⊕ J, Sum.elim (fun i => f i H.1) (fun j => g j H.2) i = none)) ≤
      (Fintype.card I : ℚ) * a + (Fintype.card J : ℚ) * b := by
  let bad : (I ⊕ J) → (A × B) → Prop := fun i H =>
    Sum.elim (fun i => f i H.1) (fun j => g j H.2) i = none
  let bound : I ⊕ J → ℚ := Sum.elim (fun _ => a) (fun _ => b)
  have hb : ∀ i, mean (fun H =>
      AspisV8R19.CausalFirstHitUnionBound.indicator (bad i H)) ≤ bound i := by
    intro i
    cases i with
    | inl i =>
      change mean (fun H : A × B =>
        AspisV8R19.CausalFirstHitUnionBound.indicator (f i H.1 = none)) ≤ a
      calc
        _ = mean (fun x : A => mean (fun _ : B =>
            AspisV8R19.CausalFirstHitUnionBound.indicator (f i x = none))) := mean_prod _
        _ = mean (fun x => abortIndicator (f i x)) := by
          apply mean_congr
          intro x
          rw [mean_const]
          exact none_indicator_eq_abort _
        _ ≤ a := hf i
    | inr j =>
      change mean (fun H : A × B =>
        AspisV8R19.CausalFirstHitUnionBound.indicator (g j H.2 = none)) ≤ b
      calc
        _ = mean (fun _ : A => mean (fun y : B =>
            AspisV8R19.CausalFirstHitUnionBound.indicator (g j y = none))) := mean_prod _
        _ = mean (fun y =>
            AspisV8R19.CausalFirstHitUnionBound.indicator (g j y = none)) := mean_const _
        _ = mean (fun y => abortIndicator (g j y)) :=
          mean_congr (fun y => none_indicator_eq_abort _)
        _ ≤ b := hg j
  have hu := AspisV8R19.CausalFirstHitUnionBound.mean_firstHit_union_le bad bound hb
  have hsum : (∑ i : I ⊕ J, bound i) =
      (Fintype.card I : ℚ) * a + (Fintype.card J : ℚ) * b := by
    simp only [bound, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact hu.trans_eq hsum

#print axioms bank_union_le
end AspisR1.FixedInputBankUnionBound
end
