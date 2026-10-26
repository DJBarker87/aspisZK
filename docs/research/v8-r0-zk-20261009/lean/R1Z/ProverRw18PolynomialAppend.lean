import R1Z.ProverRw18FieldReference
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18PolynomialAppend
open Aeneas Aeneas.Std ProverRw18FieldMeaning

theorem eval (left right : List U32) (lambda : K) :
    ProverRw18FieldModel.eval (left++right) lambda=
      ProverRw18FieldModel.eval left lambda+lambda^left.length*ProverRw18FieldModel.eval right lambda := by
  induction left with
  | nil => simp only [List.nil_append,ProverRw18FieldModel.eval,List.length_nil,pow_zero,one_mul,zero_add]
  | cons value values ih =>
    simp only [List.cons_append,ProverRw18FieldModel.eval,ih,List.length_cons,pow_succ]
    ring

theorem value (tag : U32) (left right : List U32) (lambda : K) :
    ProverRw18FieldReference.value tag (left++right) lambda=
      ProverRw18FieldReference.value tag left lambda+
        lambda^(left.length+1)*ProverRw18FieldModel.eval right lambda := by
  simp only [ProverRw18FieldReference.value,eval,pow_succ]
  ring

#print axioms eval
#print axioms value
end R1Z.ProverRw18PolynomialAppend
