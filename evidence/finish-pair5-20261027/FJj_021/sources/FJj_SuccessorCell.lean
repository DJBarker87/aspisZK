import FJf_OriginalPoint
import FJf_ArraySlots
import FJc_WeightArray
import FJd_LoopReference
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_SuccessorCell
open Aeneas Aeneas.Std Result ControlFlow
open FJc_WeightQMBridge (SQ)
open FJc_WeightValues (Canon decode)
abbrev Rev := core.iter.adapters.rev.Rev (core.ops.range.Range Usize)
abbrev next := core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
  (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize)

theorem update (p out : Array SQ 10#usize) (i : Usize) (x : SQ)
    (run : Array.update p i x=ok out) (j : Nat) :
    FJc_WeightArray.value out j=if i.val=j then decode x else FJc_WeightArray.value p j := by
  unfold FJc_WeightArray.value
  rw [FJf_ArraySlots.update_slot p out i x run j]
  by_cases h : i.val=j
  · simp only [h,if_true]
  · simp only [h,if_false]

theorem value (z p out : Array SQ 10#usize) (carry carryOut : SQ)
    (iter cursor : Rev) (i : Usize)
    (hz : FJc_WeightArray.canonical z) (hp : FJc_WeightArray.canonical p) (hc : Canon carry)
    (hn : next iter=ok (some i,cursor))
    (run : FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop.body z iter p carry=
      ok (.cont (cursor,out,carryOut))) :
    FJc_WeightArray.canonical out ∧ Canon carryOut ∧
    decode carryOut=FJc_WeightArray.value z i.val*decode carry ∧
    ∀ j,FJc_WeightArray.value out j=if i.val=j then
      FJc_WeightArray.value z i.val+decode carry-
        (FJc_WeightArray.value z i.val*decode carry+FJc_WeightArray.value z i.val*decode carry)
      else FJc_WeightArray.value p j := by
  unfold FIn_WeightsExtract.state_only_prefix.state_only_statement_points_loop.body at run
  unfold next at hn
  rw [hn] at run
  simp only [bind_tc_ok] at run
  obtain ⟨bit,hbit,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨bc,hbc,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q,hq,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q1,hq1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q2,hq2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨p',hu,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run
  have cb := FJc_WeightArray.canonical_read z i bit hz hbit
  have vb := FJc_WeightArray.read z i bit hbit
  have vbc := FJc_WeightValues.mul bit carry bc cb hc hbc
  have vq := FJc_WeightValues.add bit carry q cb hc hq
  have vq1 := FJc_WeightValues.add bc bc q1 vbc.1 vbc.1 hq1
  have vq2 := FJc_WeightValues.sub q q1 q2 vq.1 vq1.1 hq2
  refine ⟨FJc_WeightArray.update p p' i q2 hp vq2.1 hu,vbc.1,?_,?_⟩
  · rw [vbc.2,vb]
  · intro j
    rw [update p p' i q2 hu j,vq2.2,vq.2,vq1.2,vbc.2,vb]
#print axioms update
#print axioms value
end AspisR1.FJj_SuccessorCell
end
