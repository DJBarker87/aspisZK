import NDO_JGv_QueryFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_QueryStep
open Aeneas Aeneas.Std Result AspisR1Stage2
abbrev E := SAQ_WideABI.E
abbrev K := SAQ_WideABI.K
theorem source (seed : Port3_NativeQueryBody.Ops) (n : Nat)
    (a out : verifier.Accumulator) (b after : verifier.BatchedWeights)
    (beforeRhs rhs product : E) (beforePower power : K)
    (weights : a.weights=JFo_Prepared.accumulator.weights)
    (oldRhs : a.rhs=beforeRhs) (oldPower : a.power=beforePower)
    (multiply : SAQ_MixedSource.mulE (JFz_TX2_Gates.lineValue (JFz_TX2_ChainStep.query n)) beforePower=ok product)
    (addition : SAQ_Arithmetic.add beforeRhs product=ok rhs)
    (advance : SAQ_Arithmetic.mulK beforePower JFo_Prepared.value.rho=ok power)
    (call : JFz_TX2_ChainStep.transition seed n (a,b)=ok (out,after)) :
    out.rhs=rhs ∧ out.power=power := by
  exact JGv_QueryFields.source seed JFo_Prepared.value a out b after _ _ product rhs power
    (by rw [weights];exact JFo_Prepared.weights_length)
    (by rw [oldPower];exact multiply)
    (by rw [oldRhs];exact addition)
    (by rw [oldPower];exact advance) call
#print axioms source
end AspisR1.JGv_QueryStep
end
