import AspisV8R19.R372SourceColumnCompatibility

set_option autoImplicit false

namespace AspisR19.R511SourceDegenerateFold

open NormalizationLoopBridge NormalizedQuotient SourceCircleBoundary
open R370KernelEvaluation
open scoped BigOperators

variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem source_quotient_slot_factor (t : Fin 22 → F) (alpha : F)
    (d : Fin 32) (s k : Fin 4) (hs : s ≠ 0) (i : Fin 32) :
    sourceQuotient t alpha d s (i,k) =
      finished (List.ofFn t) d i * slotFactor alpha s k := by
  by_cases hk0 : k = 0
  · subst k
    simp [NormalizationLoopBridge.sourceQuotient,
      NormalizedQuotient.slotFactor, hs]
    ring
  · by_cases hks : k = s
    · subst k
      simp [NormalizationLoopBridge.sourceQuotient,
        NormalizedQuotient.slotFactor, hk0]
      ring
    · simp [NormalizationLoopBridge.sourceQuotient,
        NormalizedQuotient.slotFactor, hk0, hks]

theorem source_quotient_first_fold_zero (t : Fin 22 → F) (alpha : F)
    (d : Fin 32) (s : Fin 4) (hs : s ≠ 0) (i : Fin 32) :
    firstFold 32 alpha (sourceQuotient t alpha d s) i = 0 := by
  unfold R370KernelEvaluation.firstFold
  calc
    (∑ k : Fin 4, sourceQuotient t alpha d s (i,k) * alpha^k.val) =
        finished (List.ofFn t) d i *
          (∑ k : Fin 4, alpha^k.val * slotFactor alpha s k) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [source_quotient_slot_factor t alpha d s k hs i]
      ring
    _ = 0 := by rw [slot_fold alpha s]; ring

theorem selected_column_first_fold_zero (t : Fin 22 → F)
    (alpha : F) (j : Fin 13) (i : Fin 32) :
    firstFold 32 alpha (SourceCircleBoundary.column t alpha j) i = 0 := by
  have hs : SparseHighWitness.slot j ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [SparseHighWitness.slot, Fin.val_zero] at hv
    split_ifs at hv <;> omega
  simpa only [SourceCircleBoundary.column] using
    source_quotient_first_fold_zero t alpha
      (SparseHighWitness.degree j) (SparseHighWitness.slot j) hs i

theorem selected_column_kernel_eval_zero (t : Fin 22 → F)
    (quarter alpha : F) (j : Fin 13) (w : Fin 32 × Fin 4 → F) :
    kernelEval 32 quarter alpha (SourceCircleBoundary.column t alpha j) w = 0 :=
  kernel_eval_zero_of_first_fold 32 quarter alpha
    (SourceCircleBoundary.column t alpha j) w
    (selected_column_first_fold_zero t alpha j)

#print axioms source_quotient_slot_factor
#print axioms source_quotient_first_fold_zero
#print axioms selected_column_first_fold_zero
#print axioms selected_column_kernel_eval_zero

end AspisR19.R511SourceDegenerateFold
