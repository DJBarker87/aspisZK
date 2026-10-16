import R1AllAddressFiatShamir

/-! Oracle-observation equivalence over arbitrary address types. Two finite
causal programs agreeing under every oracle have the same lazy-sampling
expectation, even when they query different sets or repeat cells differently.
The proof reuses the existing finite-support oracle law on the union of their
potential supports; it does not posit a uniform infinite oracle space. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleProgramLawExt

open FS AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.OracleResampling AspisV8R19.OracleFiniteSupport

variable {I A O O' : Type} [DecidableEq I] [Fintype A] [Inhabited A]

theorem lazyMean_eq_of_eval (p : Program I A O) (q : Program I A O')
    (f : View I A O → ℚ) (g : View I A O' → ℚ)
    (h : ∀ H : I → A, f (eval H p) = g (eval H q)) :
    lazyMean p emptyTable f = lazyMean q emptyTable g := by
  let s := support p ∪ support q
  have hp : support p ⊆ s := Finset.subset_union_left
  have hq : support q ⊆ s := Finset.subset_union_right
  calc
    _ = mean (fun H : {i // i ∈ s} → A => f (eval (extend s H default) p)) :=
      (finite_support_oracle_law p s hp default f).symm
    _ = mean (fun H : {i // i ∈ s} → A => g (eval (extend s H default) q)) :=
      mean_congr (fun H => h (extend s H default))
    _ = _ := finite_support_oracle_law q s hq default g

theorem lazyMean_le_of_eval (p : Program I A O) (q : Program I A O')
    (f : View I A O → ℚ) (g : View I A O' → ℚ)
    (h : ∀ H : I → A, f (eval H p) ≤ g (eval H q)) :
    lazyMean p emptyTable f ≤ lazyMean q emptyTable g := by
  let s := support p ∪ support q
  have hp : support p ⊆ s := Finset.subset_union_left
  have hq : support q ⊆ s := Finset.subset_union_right
  calc
    _ = mean (fun H : {i // i ∈ s} → A => f (eval (extend s H default) p)) :=
      (finite_support_oracle_law p s hp default f).symm
    _ ≤ mean (fun H : {i // i ∈ s} → A => g (eval (extend s H default) q)) :=
      mean_mono (fun H => h (extend s H default))
    _ = _ := finite_support_oracle_law q s hq default g

#print axioms lazyMean_eq_of_eval
#print axioms lazyMean_le_of_eval
end AspisR1.OracleProgramLawExt
end
