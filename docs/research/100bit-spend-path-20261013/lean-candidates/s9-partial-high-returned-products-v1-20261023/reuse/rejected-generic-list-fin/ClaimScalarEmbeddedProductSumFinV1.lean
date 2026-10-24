import AspisR1S5ClaimScalarEmbeddedProductSum

set_option autoImplicit false

namespace AspisR1S5ClaimScalarEmbeddedProductSumFin

theorem list_map_sum_eq_fin_sum {α β : Type} [AddCommMonoid β]
    (xs : List α) (f : α → β) :
    (xs.map f).sum = ∑ i : Fin xs.length, f (xs.get i) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Fin.sum_univ_succ]
      simp only [List.get_cons_zero, List.get_cons_succ']
      exact congrArg (fun z : β => f x + z) ih

theorem productSum_finishRows_eq_fin_scalarEmbedded_sum
    (xs : List (Aeneas.Std.Usize × AspisR1CurrentPreparedClaim.Concrete.E ×
      AspisR1S5ClaimScalarConcreteQRawTrace.ClaimQM)) :
    AspisR1FinishDotReturnedFieldProductV1.productSum
        (AspisR1S5ClaimScalarConcreteQRawTrace.finishRows xs) =
      ∑ i : Fin xs.length,
        AspisR1CurrentPreparedClaim.Concrete.decode (xs.get i).2.1 *
          AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed (xs.get i).2.2 := by
  rw [AspisR1S5ClaimScalarEmbeddedProductSum.productSum_finishRows_eq_scalarEmbedded_sum]
  exact list_map_sum_eq_fin_sum xs
    (fun t => AspisR1CurrentPreparedClaim.Concrete.decode t.2.1 *
      AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed t.2.2)

#print axioms list_map_sum_eq_fin_sum
#print axioms productSum_finishRows_eq_fin_scalarEmbedded_sum

end AspisR1S5ClaimScalarEmbeddedProductSumFin
