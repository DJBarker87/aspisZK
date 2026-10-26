import R1Z.ProverRw18CopyCarrier
import R1Z.ProverRw18ContextJoin
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18CallbackModel
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning
variable [ProverRwFull.ExternalTypes]

-- Both source cuts remain explicit. This theorem is a consumer of the
-- sibling-owned op223 law, not a second extraction of that callback.
theorem value (ops : ProverRwFull.ExternalFuns) (extracted : ProverRw18ContextJoin.Compression)
    (source_law : ops.op223=extracted)
    (context_identity : extracted=
      @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops))
    (tag : U32) (values : Array U32 16#usize) (lambda : Q)
    (htag : tag.val<2147483647) (hlambda : ProverRw18FullCarrier.canonical lambda) :
    ops.op223 tag (Array.to_slice values) lambda=
      ok (ProverRw18FullCarrier.encode
        ((R0P.compressPoly (ProverRw18CopyArray.tuple tag values)).eval
          (ProverRw18FullCarrier.value lambda))) := by
  rw [ProverRw18ContextJoin.callback ops extracted source_law context_identity]
  exact ProverRw18CopyCarrier.closed tag values lambda htag hlambda

#print axioms value
end R1Z.ProverRw18CallbackModel
