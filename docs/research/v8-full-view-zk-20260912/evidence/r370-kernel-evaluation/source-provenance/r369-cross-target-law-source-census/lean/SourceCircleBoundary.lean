import AspisV8R19.PreparedCircleFold
import AspisV8R19.SourceNormalizationBoundary

/-! The exact-field source normalization, evaluator, transport and prepared
fold now share one observation boundary. Source sampler and word refinement
are not smuggled in as assumptions about independent challenges. -/
namespace AspisR19.SourceCircleBoundary
open AspisV8R16 AspisCircleTensorBinding NormalizationLoopBridge
open SourceMaskTransport SourceEncodedOpening CircleObservationBridge PreparedCircleFold
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

def column (t : Fin 22 → F) (alpha : F) (j : Fin 13) :=
  sourceQuotient t alpha (SparseHighWitness.degree j) (SparseHighWitness.slot j)

theorem coefficient_fold_zero (t : Fin 22 → F) (ht : Function.Injective t) (alpha : F) (j : Fin 13) :
    ∀ i, ∑ k : Fin 4, alpha^k.val*column t alpha j (i,k)=0 := by
  rw [column,selected_sourceQuotient_eq t ht alpha j]
  exact NormalizedQuotient.quotient_fold t ht alpha _ _

theorem raw_point_zero (t : Fin 22 → F) (ht : Function.Injective t) (alpha : F)
    (j : Fin 13) (rootIndex : Fin 22) (a b c x y : F)
    (circle : x^2+y^2=1) (root : doubledFactor x 1=t rootIndex) :
    sourceMaskEvaluate (mask (2:F)⁻¹ a b c (column t alpha j)) x y=0 := by
  rw [column,selected_sourceQuotient_eq t ht alpha j]
  exact mask_root_zero t ht alpha _ _ rootIndex a b c x y circle root

theorem raw_fibre_zero (t : Fin 22 → F) (ht : Function.Injective t) (alpha : F)
    (j : Fin 13) (rootIndex : Fin 22) (a b c x y : F)
    (circle : x^2+y^2=1) (root : doubledFactor x 1=t rootIndex) :
    let m := mask (2:F)⁻¹ a b c (column t alpha j)
    sourceMaskEvaluate m x y=0 ∧ sourceMaskEvaluate m x (-y)=0 ∧
      sourceMaskEvaluate m (-x) (-y)=0 ∧ sourceMaskEvaluate m (-x) y=0 := by
  dsimp only
  exact ⟨raw_point_zero t ht alpha j rootIndex a b c x y circle root,
    raw_point_zero t ht alpha j rootIndex a b c x (-y) (by simpa using circle) root,
    raw_point_zero t ht alpha j rootIndex a b c (-x) (-y) (by simpa using circle) (by rwa [doubled_neg]),
    raw_point_zero t ht alpha j rootIndex a b c (-x) y (by simpa using circle) (by rwa [doubled_neg])⟩

theorem final_value_zero (t : Fin 22 → F) (ht : Function.Injective t) (alpha : F) (j : Fin 13)
    (a b c x y : F) (circle : x^2+y^2=1) (hx : x≠0) (hy : y≠0)
    (l0 : a+b*x+c*y≠0) (l1 : a+b*x+c*(-y)≠0)
    (l2 : a+b*(-x)+c*(-y)≠0) (l3 : a+b*(-x)+c*y≠0) :
    let m := mask (2:F)⁻¹ a b c (column t alpha j)
    polynomialFold (2*x)⁻¹ (2*y)⁻¹ alpha
      (sourceMaskEvaluate m x y/(a+b*x+c*y))
      (sourceMaskEvaluate m x (-y)/(a+b*x+c*(-y)))
      (sourceMaskEvaluate m (-x) (-y)/(a+b*(-x)+c*(-y)))
      (sourceMaskEvaluate m (-x) y/(a+b*(-x)+c*y))=0 :=
  prepared_mask_final_zero _ alpha (coefficient_fold_zero t ht alpha j)
    a b c x y circle hx hy l0 l1 l2 l3

theorem legal_coins_OOD (t : Fin 22 → F) (ht : Function.Injective t) (alpha : F) (j : Fin 13)
    (x0 y0 x1 y1 : F) (h0 : x0^2+y0^2=1) (h1 : x1^2+y1^2=1) :
    let m := mask (2:F)⁻¹ (x0*y1-y0*x1) (y0-y1) (x1-x0) (column t alpha j)
    (∑ r ∈ T163SourceTable.inactive,m r)=0 ∧
    (∀ i, mixedCoin m i=0) ∧ sourceMaskEvaluate m x0 y0=0 ∧ sourceMaskEvaluate m x1 y1=0 := by
  dsimp only
  refine ⟨mask_balanced _ _ _ _ _,?_,?_,?_⟩
  · rw [column,selected_sourceQuotient_eq t ht alpha j]
    exact normalized_mask_coins_zero t ht _ _ _ _ _ j
  · rw [sourceMaskEvaluate_eq]
    exact mask_first_ood_zero _ _ _ _ _ h0
  · rw [sourceMaskEvaluate_eq]
    exact mask_second_ood_zero _ _ _ _ _ h1

#print axioms coefficient_fold_zero
#print axioms raw_point_zero
#print axioms raw_fibre_zero
#print axioms final_value_zero
#print axioms legal_coins_OOD
end
end AspisR19.SourceCircleBoundary
