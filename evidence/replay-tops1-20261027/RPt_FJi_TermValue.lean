import RPt_FJi_EightValue
import RPt_FJi_Inputs
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_TermValue
open Aeneas Aeneas.Std Result ControlFlow
open FJi_Accumulations FJi_Inputs
open FJf_U64Array (cell)
/-- Natural VALUES on the SAME input arrays after one actual term body. -/
theorem value (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize)
    (iter next : FIo_RangeNext.Range) (s out : Sums) (stop : iter.end.val ≤ 26)
    (run : FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body q g slot iter s=
      ok (.cont (next,out))) :
    next.end=iter.end ∧ next.start.val=iter.start.val+1 ∧ iter.start.val < iter.end.val ∧
      ∀ j,j < 8 → (cell out j).val=(cell s j).val+product q g slot j iter.start.val := by
  rw [JFr_TX2_DotStep.body] at run
  unfold JFr_TX2_DotStep.step at run
  obtain ⟨⟨o,cursor⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none => cases run
  | some term =>
    obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨s1,hs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases Result.ok.inj run
    have pr := FIo_RangeNext.some_next iter next term hn
    rw [FJi_Inputs.update] at hs
    obtain ⟨w,hw,hs⟩ := Port3_PushFrame.bind_success _ _ _ hs
    refine ⟨pr.2.1,pr.2.2.1,pr.2.2.2,?_⟩
    intro j hj
    rw [FJi_EightValue.value _ _ _ _ hs j hj]
    unfold product
    rw [←pr.1,coefficient_value g term w hw j,
      cursor_same term (by rw [pr.1];omega),scalar_value q slot term a ha]
    rfl

theorem done (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize)
    (iter : FIo_RangeNext.Range) (s out : Sums)
    (run : FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body q g slot iter s=
      ok (.done out)) : iter.end.val ≤ iter.start.val ∧ out=s := by
  rw [JFr_TX2_DotStep.body] at run
  unfold JFr_TX2_DotStep.step at run
  obtain ⟨⟨o,cursor⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none =>
    cases Result.ok.inj run
    exact ⟨FIp_RangeNone.none_next iter cursor hn,rfl⟩
  | some term =>
    obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨s1,hs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases run
#print axioms value
#print axioms done
end AspisR1.FJi_TermValue
end
