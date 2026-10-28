import NDO_JFz_TX2_ChainStep
import Port3_PushFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_QueryFields
open Aeneas Aeneas.Std Result AspisR1Stage2
/-- A successful actual accumulation fixes rhs and power independently of its
row carrier. It consumes the native return; it does not invent another one. -/
theorem source (seed : Port3_NativeQueryBody.Ops) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (b after : verifier.BatchedWeights)
    (node : U32) (value product rhs : SAQ_WideABI.E) (power : SAQ_WideABI.K)
    (size : a.weights.val.length=64)
    (multiply : SAQ_MixedSource.mulE value a.power=ok product)
    (addition : SAQ_Arithmetic.add a.rhs product=ok rhs)
    (advance : SAQ_Arithmetic.mulK a.power p.rho=ok power)
    (call : Port3_NativeQueryBody.verifier.accumulate_batched_with_node
      (JFn_ArrayBuilder.ops seed) p a node value b=ok (out,after)) :
    out.rhs=rhs ∧ out.power=power := by
  rw [Port4C_BasisMeaning.factor _ _ _ _ _ _ size] at call
  obtain ⟨basis,_,call⟩ := Port3_PushFrame.bind_success _ _ _ call
  obtain ⟨rows,_,call⟩ := Port3_PushFrame.bind_success _ _ _ call
  have hp : (JFn_ArrayBuilder.ops seed).op3 value a.power=ok product := multiply
  have hr : (JFn_ArrayBuilder.ops seed).op2 a.rhs product=ok rhs := addition
  have hq : (JFn_ArrayBuilder.ops seed).op9 a.power p.rho=ok power := advance
  have hm : (JFn_ArrayBuilder.ops seed).op15 11#u16 a.next rhs=ok () := rfl
  simp only [lift,bind_tc_ok,hp,hr,hq,hm] at call
  have same := Result.ok.inj call
  exact ⟨(congrArg (fun x=>x.1.rhs) same).symm,(congrArg (fun x=>x.1.power) same).symm⟩
#print axioms source
end AspisR1.JGv_QueryFields
end
