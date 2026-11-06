import RPv_FJe_Sum3Value
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_Sum3Total
open Aeneas Aeneas.Std Result
open FJe_Sum3BridgeBase
open FJe_Sum3Value (cell mappedCell)
open FIv_NativeArithmetic (NQ qm)
open FIv_NativeValue (Canon)
open FIv_PreparedNew (prepared)
open ExtractedMaskPreparedState (PreparedFor)
open AspisR1PoseidonPreparedIndexProductBounds (uFin)
/-- Totality supplement for the CLOSED sum3 child, needed by this parent.
Its SAME ordered witness array is never an arbitrary successful reply. -/
theorem result (a : Left) (b w : Right)
 (cw : FIw_ArrayValue.canonical w) (cb : FIw_ArrayValue.canonical b)
 (hp : ∀ i : Fin 3,PreparedFor (prepared (cell a i)) (qm (cell w i))) :
 ∃ out,FIq_Native.field.qm31_sum_products3_prepared a b=ok out ∧ Canon out := by
  have cmem (i : Fin 3) : Canon (cell w i) := cw _ (List.getElem_mem _)
  have bmem (i : Fin 3) : Canon (cell b i) := cb _ (List.getElem_mem _)
  obtain ⟨v,x0,x1,x2,rv,cv,p0,p1,p2,vv⟩ :=
    PoseidonPreparedSum3ActualValue.actual_sum3_value (left a) (right b)
      (by
        intro i
        refine ⟨qm (cell w i),cmem i,?_⟩
        change PreparedFor ((left a).val[(uFin i).val]'_) (qm (cell w i))
        exact Eq.mpr (congrArg (fun p=>PreparedFor p (qm (cell w i)))
          (mappedCell prepared a i)) (hp i))
      (by
        intro i
        change ExtractedMaskQM31Exact.CurrentCanonicalQM ((right b).val[(uFin i).val]'_)
        exact Eq.mpr (congrArg ExtractedMaskQM31Exact.CurrentCanonicalQM
          (mappedCell qm b i)) (bmem i))
  have same := FJe_Sum3WrapperBridge.same a b
  rw [rv] at same
  cases run : FIq_Native.field.qm31_sum_products3_prepared a b with
  | fail e => rw [run] at same;cases same
  | div => rw [run] at same;cases same
  | ok out => exact ⟨out,rfl,(FJe_Sum3Value.value a b w out cw cb hp run).1⟩
#print result
#print axioms result
end AspisR1.NKG_Sum3Total
end
