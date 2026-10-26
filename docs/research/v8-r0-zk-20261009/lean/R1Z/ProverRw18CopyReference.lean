import R1Z.ProverRw18CopyPolynomial
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18CopyReference
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning

def input (values : Fin 16 → U32) : Slice U32 :=
  Array.to_slice (⟨List.ofFn values,by simp⟩ : Array U32 16#usize)

theorem input_values (values : Fin 16 → U32) : (input values).val=List.ofFn values := rfl

theorem closed (tag : U32) (values : Fin 16 → U32) (lambda : Raw)
    (htag : tag.val<2147483647) (hlambda : Canonical lambda) :
    PV_RW_CompressClosed.owned tag (input values) (full lambda)=
      ok (full (ProverRw18FieldEncode.encode
        ((R0P.compressPoly (ProverRw18CopyPolynomial.tuple tag values)).eval (decode lambda)))) := by
  rw [ProverRw18FieldReference.closed tag (input values) lambda htag hlambda]
  unfold ProverRw18FieldReference.reference
  rw [input_values,ProverRw18CopyPolynomial.value]

variable [ProverRwFull.ExternalTypes]

theorem context (ops : ProverRwFull.ExternalFuns) (tag : U32) (values : Fin 16 → U32) (lambda : Raw)
    (htag : tag.val<2147483647) (hlambda : Canonical lambda) :
    @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)
      tag (input values) (full lambda)=
        ok (full (ProverRw18FieldEncode.encode
          ((R0P.compressPoly (ProverRw18CopyPolynomial.tuple tag values)).eval (decode lambda)))) := by
  rw [ProverRw18ContextCompression.owned]
  exact closed tag values lambda htag hlambda

#print axioms input_values
#print axioms closed
#print axioms context
end R1Z.ProverRw18CopyReference
