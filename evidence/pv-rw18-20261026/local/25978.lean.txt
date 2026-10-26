import R1Z.ProverRw18CopyArray
import R1Z.ProverRw18FullCarrier
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18CopyCarrier
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning

theorem closed (tag : U32) (values : Array U32 16#usize) (lambda : Q)
    (htag : tag.val<2147483647) (hlambda : ProverRw18FullCarrier.canonical lambda) :
    PV_RW_CompressClosed.owned tag (Array.to_slice values) lambda=
      ok (ProverRw18FullCarrier.encode
        ((R0P.compressPoly (ProverRw18CopyArray.tuple tag values)).eval
          (ProverRw18FullCarrier.value lambda))) := by
  have result := ProverRw18CopyArray.closed tag values (ProverRw18FullCarrier.raw lambda) htag hlambda
  rw [ProverRw18FullCarrier.full_raw] at result
  exact result

variable [ProverRwFull.ExternalTypes]
theorem context (ops : ProverRwFull.ExternalFuns) (tag : U32) (values : Array U32 16#usize) (lambda : Q)
    (htag : tag.val<2147483647) (hlambda : ProverRw18FullCarrier.canonical lambda) :
    @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)
      tag (Array.to_slice values) lambda=
        ok (ProverRw18FullCarrier.encode
          ((R0P.compressPoly (ProverRw18CopyArray.tuple tag values)).eval
            (ProverRw18FullCarrier.value lambda))) := by
  rw [ProverRw18ContextCompression.owned]
  exact closed tag values lambda htag hlambda

#print axioms closed
#print axioms context
end R1Z.ProverRw18CopyCarrier
