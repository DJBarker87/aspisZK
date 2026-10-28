import NDO_JGv_QueryChain
import NDO_JGv_QueryStep
import NDO_JGv_QueryScalars11
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_QueryScalars
open Aeneas Aeneas.Std Result AspisR1Stage2
abbrev E := SAQ_WideABI.E
abbrev K := SAQ_WideABI.K
def rhs : Nat → E
  | 0 => JGv_QueryScalars0.beforeRhs
  | 1 => JGv_QueryScalars0.rhs
  | 2 => JGv_QueryScalars1.rhs
  | 3 => JGv_QueryScalars2.rhs
  | 4 => JGv_QueryScalars3.rhs
  | 5 => JGv_QueryScalars4.rhs
  | 6 => JGv_QueryScalars5.rhs
  | 7 => JGv_QueryScalars6.rhs
  | 8 => JGv_QueryScalars7.rhs
  | 9 => JGv_QueryScalars8.rhs
  | 10 => JGv_QueryScalars9.rhs
  | 11 => JGv_QueryScalars10.rhs
  | _ => JGv_QueryScalars11.rhs
def power : Nat → K
  | 0 => JGv_QueryScalars0.beforePower
  | 1 => JGv_QueryScalars0.power
  | 2 => JGv_QueryScalars1.power
  | 3 => JGv_QueryScalars2.power
  | 4 => JGv_QueryScalars3.power
  | 5 => JGv_QueryScalars4.power
  | 6 => JGv_QueryScalars5.power
  | 7 => JGv_QueryScalars6.power
  | 8 => JGv_QueryScalars7.power
  | 9 => JGv_QueryScalars8.power
  | 10 => JGv_QueryScalars9.power
  | 11 => JGv_QueryScalars10.power
  | _ => JGv_QueryScalars11.power
theorem step (seed : Port3_NativeQueryBody.Ops) (n : Nat) (hn : n<12)
    (a : verifier.Accumulator) (b : verifier.BatchedWeights)
    (out : verifier.Accumulator) (after : verifier.BatchedWeights)
    (weights : a.weights=JFo_Prepared.accumulator.weights)
    (oldRhs : a.rhs=rhs n) (oldPower : a.power=power n)
    (call : JFz_TX2_ChainStep.transition seed n (a,b)=ok (out,after)) :
    out.rhs=rhs (n+1) ∧ out.power=power (n+1) := by
  interval_cases n
  · exact JGv_QueryStep.source seed 0 a out b after _ _ JGv_QueryScalars0.product _ _
      weights oldRhs oldPower JGv_QueryScalars0.multiply JGv_QueryScalars0.addition JGv_QueryScalars0.advance call
  · exact JGv_QueryStep.source seed 1 a out b after _ _ JGv_QueryScalars1.product _ _
      weights oldRhs oldPower JGv_QueryScalars1.multiply JGv_QueryScalars1.addition JGv_QueryScalars1.advance call
  · exact JGv_QueryStep.source seed 2 a out b after _ _ JGv_QueryScalars2.product _ _
      weights oldRhs oldPower JGv_QueryScalars2.multiply JGv_QueryScalars2.addition JGv_QueryScalars2.advance call
  · exact JGv_QueryStep.source seed 3 a out b after _ _ JGv_QueryScalars3.product _ _
      weights oldRhs oldPower JGv_QueryScalars3.multiply JGv_QueryScalars3.addition JGv_QueryScalars3.advance call
  · exact JGv_QueryStep.source seed 4 a out b after _ _ JGv_QueryScalars4.product _ _
      weights oldRhs oldPower JGv_QueryScalars4.multiply JGv_QueryScalars4.addition JGv_QueryScalars4.advance call
  · exact JGv_QueryStep.source seed 5 a out b after _ _ JGv_QueryScalars5.product _ _
      weights oldRhs oldPower JGv_QueryScalars5.multiply JGv_QueryScalars5.addition JGv_QueryScalars5.advance call
  · exact JGv_QueryStep.source seed 6 a out b after _ _ JGv_QueryScalars6.product _ _
      weights oldRhs oldPower JGv_QueryScalars6.multiply JGv_QueryScalars6.addition JGv_QueryScalars6.advance call
  · exact JGv_QueryStep.source seed 7 a out b after _ _ JGv_QueryScalars7.product _ _
      weights oldRhs oldPower JGv_QueryScalars7.multiply JGv_QueryScalars7.addition JGv_QueryScalars7.advance call
  · exact JGv_QueryStep.source seed 8 a out b after _ _ JGv_QueryScalars8.product _ _
      weights oldRhs oldPower JGv_QueryScalars8.multiply JGv_QueryScalars8.addition JGv_QueryScalars8.advance call
  · exact JGv_QueryStep.source seed 9 a out b after _ _ JGv_QueryScalars9.product _ _
      weights oldRhs oldPower JGv_QueryScalars9.multiply JGv_QueryScalars9.addition JGv_QueryScalars9.advance call
  · exact JGv_QueryStep.source seed 10 a out b after _ _ JGv_QueryScalars10.product _ _
      weights oldRhs oldPower JGv_QueryScalars10.multiply JGv_QueryScalars10.addition JGv_QueryScalars10.advance call
  · exact JGv_QueryStep.source seed 11 a out b after _ _ JGv_QueryScalars11.product _ _
      weights oldRhs oldPower JGv_QueryScalars11.multiply JGv_QueryScalars11.addition JGv_QueryScalars11.advance call
#print axioms step
theorem source {C : Type} (err : C) (geometry : Port3_NativeGeometryBody.Ops C)
    (seed : Port3_NativeQueryBody.Ops) (a : verifier.Accumulator) (b : verifier.BatchedWeights)
    (call : JFz_TX2_AccumulationChain.updates seed 12=ok (a,b)) :
    a.rhs=JGv_QueryScalars11.rhs ∧ a.power=JGv_QueryScalars11.power := by
  exact JGv_QueryChain.source err geometry seed rhs power (by rfl) (by rfl) (step seed) 12 (by omega) a b call
#print axioms source
end AspisR1.JGv_QueryScalars
end
