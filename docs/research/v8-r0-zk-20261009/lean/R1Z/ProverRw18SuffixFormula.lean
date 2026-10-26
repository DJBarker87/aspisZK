import R1Z.ProverRw18FieldSuffix
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18SuffixFormula
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning
variable [ProverRwFull.ExternalTypes]

theorem exact_run (ops : ProverRwFull.ExternalFuns) (values : Slice U32) (i : Nat)
    (lambda out power : Raw) (hlambda : Canonical lambda) (hout : Canonical out) (hpower : Canonical power) :
    PV_RW_IteratorStateLoop.run ops (full lambda) (⟨values,i⟩ : core.slice.iter.Iter U32)
      (full out,full power)=ok
        (full (ProverRw18FieldEncode.encode (decode out+decode power*
          ProverRw18FieldModel.eval (values.val.drop i) (decode lambda))),
         full (ProverRw18FieldEncode.encode
          (decode power*(decode lambda)^(values.val.length-i)))) := by
  rw [ProverRw18FieldSuffix.field ops values i lambda out power hlambda hout hpower]
  simp only [ProverRw18FieldStateReference.reference,ProverRw18FieldModel.output,
    ProverRw18FieldModel.power,List.length_drop]

#print axioms exact_run
end R1Z.ProverRw18SuffixFormula
