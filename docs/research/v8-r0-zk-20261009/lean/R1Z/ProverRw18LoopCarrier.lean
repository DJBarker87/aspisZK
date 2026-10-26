import R1Z.ProverRw18SuffixFormula
import R1Z.ProverRw18FullCarrier
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18LoopCarrier
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning
variable [ProverRwFull.ExternalTypes]

theorem value (ops : ProverRwFull.ExternalFuns) (values : Slice U32) (i : Nat) (lambda out power : Q)
    (hlambda : ProverRw18FullCarrier.canonical lambda)
    (hout : ProverRw18FullCarrier.canonical out) (hpower : ProverRw18FullCarrier.canonical power) :
    PV_RW_IteratorStateLoop.run ops lambda (⟨values,i⟩ : core.slice.iter.Iter U32) (out,power)=
      ok (ProverRw18FullCarrier.encode
        (ProverRw18FullCarrier.value out+ProverRw18FullCarrier.value power*
          ProverRw18FieldModel.eval (values.val.drop i) (ProverRw18FullCarrier.value lambda)),
        ProverRw18FullCarrier.encode (ProverRw18FullCarrier.value power*
          (ProverRw18FullCarrier.value lambda)^(values.val.length-i))) := by
  have result := ProverRw18SuffixFormula.exact_run ops values i
    (ProverRw18FullCarrier.raw lambda) (ProverRw18FullCarrier.raw out) (ProverRw18FullCarrier.raw power)
    hlambda hout hpower
  simp only [ProverRw18FullCarrier.full_raw] at result
  exact result

#print axioms value
end R1Z.ProverRw18LoopCarrier
