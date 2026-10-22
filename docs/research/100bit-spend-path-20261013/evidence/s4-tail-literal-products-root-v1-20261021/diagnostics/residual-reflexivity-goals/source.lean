import S4TailFinishFieldRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsTailLiteralProductsRootV1
open AspisR1FastDotsPushProductTraceRootV1
open AspisR1FastDotsTailFieldProductRootV1
open AspisR1FastDotsTailFinishSourceMapV1
open AspisR1FastDotsTailFinishFieldRootV1

def embedQM (q : QM) : TowerWide := ⟨qmDecoded q,0⟩

theorem scalarProduct_eq_mul (p : Wide × QM) :
    scalarProduct p = wideDecoded p.1 * embedQM p.2 := by
  apply QuadraticAlgebra.ext <;> simp [scalarProduct,wideDecoded,embedQM]

theorem productSum_eq_literal_sum (ps : List (Wide × QM)) :
    productSum ps = (ps.map (fun p=>wideDecoded p.1 * embedQM p.2)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [productSum,List.map_cons,List.sum_cons,scalarProduct_eq_mul,ih]

/-- The retained tail finish is exactly an ordinary sum of Wide field
multiplications, with each QM operand embedded in its actual subfield. -/
theorem finished_tail_eq_literal_sum (s : State) (out : Wide)
    (ps : List (Wide × QM))
    (hproduct : stateValue s = ps.foldl addProduct
      (stateValue EbyKNewToPushStateABI.pushZero))
    (hwords : (currentFinishWords out).map (fun w=>w.val) =
      ((s.c0.sums.val ++ s.c1.sums.val).map
        (fun x=>x.val % AspisV8R17.RawReducer.P))) :
    AspisR1CurrentWide.Proof.decodeWide
      (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE out) =
      (ps.map (fun p=>wideDecoded p.1 * embedQM p.2)).sum :=
  (finish_is_ordered_field_product_sum s out ps hproduct hwords).trans
    (productSum_eq_literal_sum ps)

#print axioms scalarProduct_eq_mul
#print axioms productSum_eq_literal_sum
#print axioms finished_tail_eq_literal_sum
end AspisR1FastDotsTailLiteralProductsRootV1
