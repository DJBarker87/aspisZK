import R1Z.ProverRw18FieldFold
import R1Z.ProverRw18FieldInitial
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18FieldCompression
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning

-- A field-value theorem on its explicit canonical domain. The earlier
-- source/reference Result equality remains unrestricted on raw inputs.
theorem owned (tag : U32) (values : Slice U32) (lambda : Raw)
    (htag : tag.val<2147483647) (hlambda : Canonical lambda) :
    ∃ out : Raw, PV_RW_CompressClosed.owned tag values (full lambda)=ok (full out) ∧
      Canonical out ∧ decode out=(tag.val : K)+
        decode lambda*ProverRw18FieldModel.eval values.val (decode lambda) := by
  obtain ⟨out,power,hs,hco,_,hd⟩ := ProverRw18FieldFold.fold values.val lambda
    (ProverRw18FieldInitial.base tag) lambda hlambda
    (ProverRw18FieldInitial.canonical tag htag) hlambda
  refine ⟨out,?_,hco,?_⟩
  · unfold PV_RW_CompressClosed.owned
    rw [← ProverRw18FieldInitial.full_base tag,hs]
    rfl
  · have output := congrArg Prod.fst hd
    rw [ProverRw18FieldModel.output] at output
    simpa only [ProverRw18FieldInitial.decoded] using output

variable [ProverRwFull.ExternalTypes]

theorem context (ops : ProverRwFull.ExternalFuns) (tag : U32) (values : Slice U32) (lambda : Raw)
    (htag : tag.val<2147483647) (hlambda : Canonical lambda) :
    ∃ out : Raw, @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)
      tag values (full lambda)=ok (full out) ∧ Canonical out ∧
      decode out=(tag.val : K)+decode lambda*ProverRw18FieldModel.eval values.val (decode lambda) := by
  rw [ProverRw18ContextCompression.owned]
  exact owned tag values lambda htag hlambda

#print axioms owned
#print axioms context
end R1Z.ProverRw18FieldCompression
