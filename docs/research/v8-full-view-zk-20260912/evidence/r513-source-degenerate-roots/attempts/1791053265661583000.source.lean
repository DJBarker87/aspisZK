import AspisV8R19.R511SourceDegenerateFold

set_option autoImplicit false

namespace AspisR19.R513SourceDegenerateRoots

open NormalizationLoopBridge NormalizedQuerySection DescendingRemainder
open SourceFactorEvaluation SourceCircleBoundary R511SourceDegenerateFold
open scoped BigOperators

variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem finished_eq_unit_sub (t : Fin 22 → F) (d i : Fin 32)
    (hd : 22 ≤ d.val) :
    finished (List.ofFn t) d i =
      unit d.val i.val - remainder (List.ofFn t) d i.val := by
  by_cases hi : i = d
  · subst i
    have hz := remainder_support (List.ofFn t) (by simp) d hd d.val hd
    simp [NormalizationLoopBridge.finished, DescendingRemainder.unit, hz]
  · have hval : i.val ≠ d.val := fun h => hi (Fin.ext h)
    simp [NormalizationLoopBridge.finished, DescendingRemainder.unit, hi, hval]

theorem finished_evaluate_root_zero (t : Fin 22 → F) (d : Fin 32)
    (hd : 22 ≤ d.val) (j : Fin 22) :
    evaluate (finished (List.ofFn t) d) (t j) = 0 := by
  have hunit : evaluate (fun i : Fin 32 => unit d.val i.val) (t j) =
      naturalLineValue (t j) d.val := by
    unfold NormalizedQuerySection.evaluate
    have hunitval : ∀ i : Fin 32,
        unit d.val i.val = if i = d then 1 else 0 := by
      intro i
      simp [unit, Fin.ext_iff]
    simp_rw [hunitval]
    rw [Finset.sum_eq_single d]
    · simp
    · intro i hi hne
      simp [hne]
    · simp
  have hrem := remainder_evaluation (List.ofFn t) (by simp) d (t j)
    (List.mem_ofFn.mpr ⟨j, rfl⟩)
  rw [SourceFactorEvaluation.line, Finset.sum_range] at hrem
  have hrem_eval : evaluate (fun i : Fin 32 => remainder (List.ofFn t) d i.val) (t j) =
      naturalLineValue (t j) d.val := by
    simpa only [NormalizedQuerySection.evaluate, mul_comm] using hrem
  calc
    evaluate (finished (List.ofFn t) d) (t j) =
        evaluate (fun i : Fin 32 => unit d.val i.val - remainder (List.ofFn t) d i.val) (t j) := by
      apply congrArg
      funext i
      exact finished_eq_unit_sub t d i hd
    _ = evaluate (fun i : Fin 32 => unit d.val i.val) (t j) -
          evaluate (fun i : Fin 32 => remainder (List.ofFn t) d i.val) (t j) := by
      simp only [NormalizedQuerySection.evaluate, sub_mul, Finset.sum_sub_distrib]
    _ = 0 := by rw [hunit, hrem_eval]; exact sub_self _

theorem source_quotient_slot_evaluate_root_zero (t : Fin 22 → F)
    (alpha : F) (d : Fin 32) (s k : Fin 4) (hs : s ≠ 0)
    (j : Fin 22) :
    evaluate (fun i : Fin 32 => sourceQuotient t alpha d s (i,k)) (t j) = 0 := by
  calc
    evaluate (fun i : Fin 32 => sourceQuotient t alpha d s (i,k)) (t j) =
        ∑ i : Fin 32, slotFactor alpha s k *
          (finished (List.ofFn t) d i * naturalLineValue (t j) i.val) := by
      unfold NormalizedQuerySection.evaluate
      apply Finset.sum_congr rfl
      intro i _
      rw [source_quotient_slot_factor t alpha d s k hs i]
      ring
    _ = slotFactor alpha s k *
          evaluate (finished (List.ofFn t) d) (t j) := by
      simp only [Finset.mul_sum, NormalizedQuerySection.evaluate]
    _ = 0 := by rw [finished_evaluate_root_zero t d (by
      -- This theorem is general in d only once the high-degree bound is supplied.
      omega) j]; simp

theorem selected_column_slot_root_zero (t : Fin 22 → F) (alpha : F)
    (j : Fin 13) (k : Fin 4) (root : Fin 22) :
    evaluate (fun i : Fin 32 => SourceCircleBoundary.column t alpha j (i,k))
      (t root) = 0 := by
  have hd : 22 ≤ (SparseHighWitness.degree j).val := by
    simp only [SparseHighWitness.degree]
    split_ifs <;> omega
  have hs : SparseHighWitness.slot j ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [SparseHighWitness.slot, Fin.val_zero] at hv
    split_ifs at hv <;> omega
  simpa only [SourceCircleBoundary.column] using
    source_quotient_slot_evaluate_root_zero t alpha
      (SparseHighWitness.degree j) (SparseHighWitness.slot j) k hs root

#print axioms finished_eq_unit_sub
#print axioms finished_evaluate_root_zero
#print axioms source_quotient_slot_evaluate_root_zero
#print axioms selected_column_slot_root_zero

end AspisR19.R513SourceDegenerateRoots
