import R1Z.ProverRw18CopyCarrier
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18CopyCongruence
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning

theorem closed (leftTag rightTag : U32) (left right : Array U32 16#usize) (lambda : Q)
    (hleft : leftTag.val<2147483647) (hright : rightTag.val<2147483647)
    (hlambda : ProverRw18FullCarrier.canonical lambda)
    (same : ProverRw18CopyArray.tuple leftTag left=ProverRw18CopyArray.tuple rightTag right) :
    PV_RW_CompressClosed.owned leftTag (Array.to_slice left) lambda=
      PV_RW_CompressClosed.owned rightTag (Array.to_slice right) lambda := by
  rw [ProverRw18CopyCarrier.closed leftTag left lambda hleft hlambda,
    ProverRw18CopyCarrier.closed rightTag right lambda hright hlambda,same]

variable [ProverRwFull.ExternalTypes]
theorem context (ops : ProverRwFull.ExternalFuns) (leftTag rightTag : U32)
    (left right : Array U32 16#usize) (lambda : Q)
    (hleft : leftTag.val<2147483647) (hright : rightTag.val<2147483647)
    (hlambda : ProverRw18FullCarrier.canonical lambda)
    (same : ProverRw18CopyArray.tuple leftTag left=ProverRw18CopyArray.tuple rightTag right) :
    @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)
      leftTag (Array.to_slice left) lambda=
        @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)
          rightTag (Array.to_slice right) lambda := by
  rw [ProverRw18ContextCompression.owned,ProverRw18ContextCompression.owned]
  exact closed leftTag rightTag left right lambda hleft hright hlambda same

#print axioms closed
#print axioms context
end R1Z.ProverRw18CopyCongruence
