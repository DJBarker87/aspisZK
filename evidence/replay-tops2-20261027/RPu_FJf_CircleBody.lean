import RPu_FJf_PointDone
set_option autoImplicit false
namespace AspisR1.FJf_CircleBody
open Aeneas Aeneas.Std Result ControlFlow
open FJf_PointBody (Factors)
open FJc_WeightQMBridge (SQ)
theorem cont (k : Usize) (iter cursor : FIo_RangeNext.Range)
    (factors next : Factors) (x x' : SQ)
    (run : FIn_WeightsExtract.weights_new_loop1_loop0.body k iter factors x=
      ok (.cont (cursor,next,x'))) :
    ∃ (d : Usize) (row updated : FJf_FactorArray.Row)
      (back : FJf_FactorArray.Row → Factors) (digit : Array SQ 4#usize),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some d,cursor) ∧
      Array.index_mut_usize factors (Usize.wrapping_add 3#usize k)=ok (row,back) ∧
      Array.update row d digit=ok updated ∧ next=back updated := by
  unfold FIn_WeightsExtract.weights_new_loop1_loop0.body at run
  obtain ⟨⟨o,cursor'⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none => cases run
  | some d =>
    obtain ⟨y,hy,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨q,hq,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨i,hi,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨⟨row,back⟩,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨updated,hu,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨x1,hx,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases Result.ok.inj run
    have ei := Result.ok.inj hi
    subst i
    exact ⟨d,row,updated,back,_,hn,hr,hu,rfl⟩

theorem done (k : Usize) (iter : FIo_RangeNext.Range) (factors out : Factors) (x : SQ)
    (run : FIn_WeightsExtract.weights_new_loop1_loop0.body k iter factors x=ok (.done out)) :
    iter.end.val ≤ iter.start.val ∧ out=factors := by
  unfold FIn_WeightsExtract.weights_new_loop1_loop0.body at run
  obtain ⟨⟨o,cursor⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none =>
    cases Result.ok.inj run
    exact ⟨FIp_RangeNone.none_next iter cursor hn,rfl⟩
  | some d =>
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases run
#print axioms cont
#print axioms done
end AspisR1.FJf_CircleBody
