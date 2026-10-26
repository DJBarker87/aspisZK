import R1Z.ProverRw18FieldCompression
import R1Z.ProverRw18FieldEncode
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18FieldReference
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning

-- A conventional polynomial plus a canonical field-coordinate encoder.
-- This is solely the compression component's mathematical reference, not
-- V163's uninstantiated whole proof/audit model.
def value (tag : U32) (values : List U32) (lambda : K) : K :=
  (tag.val : K)+lambda*ProverRw18FieldModel.eval values lambda

def reference (tag : U32) (values : Slice U32) (lambda : Raw) : Result Q :=
  ok (full (ProverRw18FieldEncode.encode (value tag values.val (decode lambda))))

theorem closed (tag : U32) (values : Slice U32) (lambda : Raw)
    (htag : tag.val<2147483647) (hlambda : Canonical lambda) :
    PV_RW_CompressClosed.owned tag values (full lambda)=reference tag values lambda := by
  obtain ⟨out,hr,hc,hd⟩ := ProverRw18FieldCompression.owned tag values lambda htag hlambda
  have same : out=ProverRw18FieldEncode.encode (value tag values.val (decode lambda)) := by
    apply ProverRw18FieldInjective.raw _ _ hc (ProverRw18FieldEncode.canonical _)
    rw [ProverRw18FieldEncode.decoded]
    exact hd
  rw [hr,same]
  rfl

variable [ProverRwFull.ExternalTypes]

theorem context (ops : ProverRwFull.ExternalFuns) (tag : U32) (values : Slice U32) (lambda : Raw)
    (htag : tag.val<2147483647) (hlambda : Canonical lambda) :
    @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)
      tag values (full lambda)=reference tag values lambda := by
  rw [ProverRw18ContextCompression.owned]
  exact closed tag values lambda htag hlambda

#print axioms closed
#print axioms context
end R1Z.ProverRw18FieldReference
