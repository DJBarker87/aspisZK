import R1Z.ProverRw18FieldReference
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18LambdaEdges
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning

theorem eval_one (values : List U32) :
    ProverRw18FieldModel.eval values 1=(values.map (fun value => (value.val : K))).sum := by
  induction values with
  | nil => rfl
  | cons value values ih => simp only [ProverRw18FieldModel.eval,one_mul,ih,List.map_cons,List.sum_cons]

theorem base_encoded (tag : U32) (bound : tag.val<2147483647) :
    ProverRw18FieldEncode.encode (tag.val : K)=ProverRw18FieldInitial.base tag := by
  rw [← ProverRw18FieldInitial.decoded tag]
  exact ProverRw18FieldEncode.encoded _ (ProverRw18FieldInitial.canonical tag bound)

theorem zero (tag : U32) (values : Slice U32) (bound : tag.val<2147483647) :
    PV_RW_CompressClosed.owned tag values (full (ProverRw18FieldEncode.encode 0))=
      ok (PV_RW_CompressLiftSelectors.initial tag) := by
  rw [ProverRw18FieldReference.closed tag values _ bound (ProverRw18FieldEncode.canonical 0)]
  simp only [ProverRw18FieldReference.reference,ProverRw18FieldReference.value,
    ProverRw18FieldEncode.decoded,zero_mul,add_zero,base_encoded tag bound,
    ProverRw18FieldInitial.full_base]

theorem one (tag : U32) (values : Slice U32) (bound : tag.val<2147483647) :
    PV_RW_CompressClosed.owned tag values (full (ProverRw18FieldEncode.encode 1))=
      ok (full (ProverRw18FieldEncode.encode
        ((tag.val : K)+(values.val.map (fun value => (value.val : K))).sum))) := by
  rw [ProverRw18FieldReference.closed tag values _ bound (ProverRw18FieldEncode.canonical 1)]
  simp only [ProverRw18FieldReference.reference,ProverRw18FieldReference.value,
    ProverRw18FieldEncode.decoded,one_mul,eval_one]

#print axioms eval_one
#print axioms base_encoded
#print axioms zero
#print axioms one
end R1Z.ProverRw18LambdaEdges
