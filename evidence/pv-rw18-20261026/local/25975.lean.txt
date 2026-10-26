import R1Z.ProverRw18ArrayValues
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18CopyArray
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning

def tuple (tag : U32) (values : Array U32 16#usize) : K × (Fin 16 → K) :=
  ProverRw18CopyPolynomial.tuple tag (ProverRw18ArrayValues.elements values)

theorem closed (tag : U32) (values : Array U32 16#usize) (lambda : Raw)
    (htag : tag.val<2147483647) (hlambda : Canonical lambda) :
    PV_RW_CompressClosed.owned tag (Array.to_slice values) (full lambda)=
      ok (full (ProverRw18FieldEncode.encode ((R0P.compressPoly (tuple tag values)).eval (decode lambda)))) := by
  rw [← ProverRw18ArrayValues.input values]
  exact ProverRw18CopyReference.closed tag (ProverRw18ArrayValues.elements values) lambda htag hlambda

variable [ProverRwFull.ExternalTypes]
theorem context (ops : ProverRwFull.ExternalFuns) (tag : U32) (values : Array U32 16#usize) (lambda : Raw)
    (htag : tag.val<2147483647) (hlambda : Canonical lambda) :
    @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)
      tag (Array.to_slice values) (full lambda)=
        ok (full (ProverRw18FieldEncode.encode ((R0P.compressPoly (tuple tag values)).eval (decode lambda)))) := by
  rw [ProverRw18ContextCompression.owned]
  exact closed tag values lambda htag hlambda

#print axioms closed
#print axioms context
end R1Z.ProverRw18CopyArray
