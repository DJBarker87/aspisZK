import FJd_LoopReference
import FJc_WeightConstants
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJd_SourceSuccessor
open Aeneas Aeneas.Std Result
open FJc_WeightQMBridge (SQ)
open FJc_WeightValues
/-- Owned monadic reference for one reverse carry step, in source order. -/
def reference (bit carry : SQ) : Result (SQ × SQ) := do
  let bc ← FIn_WeightsExtract.field.QM31.mul bit carry
  let sum ← FIn_WeightsExtract.field.QM31.add bit carry
  let twice ← FIn_WeightsExtract.field.QM31.add bc bc
  let out ← FIn_WeightsExtract.field.QM31.sub sum twice
  ok (bc,out)

theorem value (bit carry bc out : SQ) (hb : Canon bit) (hc : Canon carry)
    (run : reference bit carry=ok (bc,out)) :
    Canon bc ∧ Canon out ∧ decode bc=decode bit*decode carry ∧
      decode out=decode bit+decode carry-2*(decode bit*decode carry) := by
  unfold reference at run
  obtain ⟨bc',hbc,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨sum,hs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨twice,ht,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨out',ho,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run
  have vbc := FJc_WeightValues.mul _ _ _ hb hc hbc
  have vs := FJc_WeightValues.add _ _ _ hb hc hs
  have vt := FJc_WeightValues.add _ _ _ vbc.1 vbc.1 ht
  have vo := FJc_WeightValues.sub _ _ _ vs.1 vt.1 ho
  refine ⟨vbc.1,vo.1,vbc.2,?_⟩
  rw [vo.2,vs.2,vt.2,vbc.2]
  ring
#print axioms value
end AspisR1.FJd_SourceSuccessor
end
