import CompPolyFactorMeanTools

namespace AspisR1.SequentialFreshProgram
open AspisV8R19.MemoizedProgramLaw AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.OracleResampling AspisV8PairedCommitment
open AspisR1.CompPolyFactorMeanTools

/-- Execute the same adaptive branches but consume fresh tape blocks in
strict sequential order. The final cursor records exact consumption. -/
def sequential {I A O : Type} : Program I A O → Nat → Program Nat A (O × Nat)
  | .done o, cursor => .done (o,cursor)
  | .ask _ next, cursor => .ask cursor (fun a => sequential (next a) (cursor+1))

noncomputable section
variable {I A O : Type} [Fintype A] [Nonempty A]

theorem sequential_outMean (p : Program I A O) (cursor : Nat) (observe : O → ℚ) :
    outMean (sequential p cursor) (fun oc => observe oc.1) = outMean p observe := by
  induction p generalizing cursor with
  | done o => rfl
  | ask i next ih =>
    change mean (fun a => outMean (sequential (next a) (cursor+1))
      (fun oc => observe oc.1)) = mean (fun a => outMean (next a) observe)
    exact mean_congr (fun a => ih a (cursor+1))

/-- Freshness follows from increasing the cursor, independently of the
adaptive choice of continuation and its original heap/query address. -/
theorem sequential_fresh (p : Program I A O) (cursor : Nat) (table : Table Nat A)
    (hfuture : ∀ i, cursor ≤ i → table i = none) :
    FreshFrom (sequential p cursor) table := by
  induction p generalizing cursor table with
  | done o => trivial
  | ask i next ih =>
    refine ⟨hfuture cursor (Nat.le_refl _), ?_⟩
    intro a
    apply ih a (cursor+1) (put table cursor a)
    intro j hj
    have hne : j ≠ cursor := by omega
    simp only [put, if_neg hne]
    exact hfuture j (by omega)

/-- Reuses the proved first-read interpreter law. A sequential sampler with
an initially empty future has exactly the independent-answer outcome law. -/
theorem sequential_lazy_mean (p : Program I A O) (cursor : Nat)
    (table : Table Nat A) (hfuture : ∀ i, cursor ≤ i → table i = none)
    (observe : O → ℚ) :
    lazyMean (sequential p cursor) table (fun v => observe v.2.1) = outMean p observe := by
  rw [lazyMean_eq_independentMean _ _ (sequential_fresh p cursor table hfuture)]
  exact sequential_outMean p cursor observe

#print axioms sequential
#print axioms sequential_outMean
#print axioms sequential_fresh
#print axioms sequential_lazy_mean
end
end AspisR1.SequentialFreshProgram
