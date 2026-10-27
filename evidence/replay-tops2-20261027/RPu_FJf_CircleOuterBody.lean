import RPu_FJf_CircleFrame
set_option autoImplicit false
namespace AspisR1.FJf_CircleOuterBody
open Aeneas Aeneas.Std Result ControlFlow
open FJf_PointBody (Factors)
open FJc_WeightQMBridge (SQ)
abbrev Z := Array FIn_WeightsExtract.circle.SecureCirclePoint 2#usize

theorem cont (z : Z) (iter cursor : FIo_RangeNext.Range) (factors next : Factors)
    (run : FIn_WeightsExtract.weights_new_loop1.body z iter factors=ok (.cont (cursor,next))) :
    ∃ (k : Usize) (row updated : FJf_FactorArray.Row)
      (back : FJf_FactorArray.Row → Factors) (digit : Array SQ 4#usize) (x : SQ),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some k,cursor) ∧
      Array.index_mut_usize factors (Usize.wrapping_add 3#usize k)=ok (row,back) ∧
      Array.update row 0#usize digit=ok updated ∧
      FIn_WeightsExtract.weights_new_loop1_loop0 {start:=1#usize,«end»:=5#usize}
        (back updated) k x=ok next := by
  unfold FIn_WeightsExtract.weights_new_loop1.body at run
  obtain ⟨⟨o,cursor'⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none => cases run
  | some k =>
    obtain ⟨scp,hscp,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨q,hq,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨i,hi,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨⟨row,back⟩,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨updated,hu,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨x,hx,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨f,hf,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases Result.ok.inj run
    have ei := Result.ok.inj hi
    subst i
    exact ⟨k,row,updated,back,_,x,hn,hr,hu,hf⟩

theorem done (z : Z) (iter : FIo_RangeNext.Range) (factors out : Factors)
    (run : FIn_WeightsExtract.weights_new_loop1.body z iter factors=ok (.done out)) :
    iter.end.val ≤ iter.start.val ∧ out=factors := by
  unfold FIn_WeightsExtract.weights_new_loop1.body at run
  obtain ⟨⟨o,cursor⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none =>
    cases Result.ok.inj run
    exact ⟨FIp_RangeNone.none_next iter cursor hn,rfl⟩
  | some k =>
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases run
#print axioms cont
#print axioms done
end AspisR1.FJf_CircleOuterBody
