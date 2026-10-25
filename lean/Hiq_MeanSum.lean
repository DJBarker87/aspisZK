import OracleProgramLawExt
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_MeanSum
open FS AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.OracleResampling AspisV8R19.OracleFiniteSupport
variable {I A X Y Z : Type} [DecidableEq I] [Fintype A] [Inhabited A]

/-- All three causal programs are coupled only through the same oracle.
No independence, conditioning, replay erasure or infinite uniform measure. -/
theorem le_sum (p : Program I A X) (q : Program I A Y) (r : Program I A Z)
    (f : View I A X → Rat) (g : View I A Y → Rat) (h : View I A Z → Rat)
    (pointwise : ∀ H : I → A, f (eval H p) ≤ g (eval H q) + h (eval H r)) :
    lazyMean p emptyTable f ≤ lazyMean q emptyTable g + lazyMean r emptyTable h := by
  let s := (support p ∪ support q) ∪ support r
  have hp : support p ⊆ s := Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
  have hq : support q ⊆ s := Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
  have hr : support r ⊆ s := Finset.subset_union_right
  calc
    _ = mean (fun H : {i // i ∈ s} → A => f (eval (extend s H default) p)) :=
      (finite_support_oracle_law p s hp default f).symm
    _ ≤ mean (fun H : {i // i ∈ s} → A => g (eval (extend s H default) q) + h (eval (extend s H default) r)) :=
      mean_mono (fun H => pointwise (extend s H default))
    _ = mean (fun H : {i // i ∈ s} → A => g (eval (extend s H default) q)) +
        mean (fun H : {i // i ∈ s} → A => h (eval (extend s H default) r)) := mean_add _ _
    _ = _ := congrArg₂ (· + ·) (finite_support_oracle_law q s hq default g)
      (finite_support_oracle_law r s hr default h)

#print axioms le_sum
end AspisR1.Hiq_MeanSum
end
