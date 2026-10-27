import FJd_SourceFactor
import FJc_WeightArray
import FIo_RangeNext
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_PointBody
open Aeneas Aeneas.Std Result ControlFlow
open FJc_WeightQMBridge (SQ)
abbrev Factors := Array (Array (Array SQ 4#usize) 5#usize) 5#usize
abbrev Points := Array (Array SQ 10#usize) 3#usize
/-- Inverts ONE actual installed constructor body; the reference run is derived,
not supplied. The mutable-array continuation is the original returned closure. -/
theorem source (points : Points) (k : Usize) (iter cursor : FIo_RangeNext.Range)
    (factors next : Factors)
    (run : FIn_WeightsExtract.weights_new_loop0_loop0.body points k iter factors=
      ok (.cont (cursor,next))) :
    ∃ (d tau ia ib : Usize) (p : Array SQ 10#usize) (a b : SQ)
      (row : Array (Array SQ 4#usize) 5#usize)
      (back : Array (Array SQ 4#usize) 5#usize → Factors)
      (updated : Array (Array SQ 4#usize) 5#usize) (f0 f1 f2 f3 : SQ),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some d,cursor) ∧
      Array.index_usize FIn_WeightsExtract.TAU d=ok tau ∧
      ia=Usize.wrapping_sub 9#usize (Usize.wrapping_mul 2#usize tau) ∧
      ib=Usize.wrapping_sub 8#usize (Usize.wrapping_mul 2#usize tau) ∧
      Array.index_usize points k=ok p ∧
      Array.index_usize p ia=ok a ∧ Array.index_usize p ib=ok b ∧
      FJd_SourceFactor.reference a b=ok [f0,f1,f2,f3] ∧
      Array.index_mut_usize factors k=ok (row,back) ∧
      Array.update row d (Array.make 4#usize [f0,f1,f2,f3])=ok updated ∧
      next=back updated := by
  unfold FIn_WeightsExtract.weights_new_loop0_loop0.body at run
  obtain ⟨⟨o,cursor'⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none => cases run
  | some d =>
    obtain ⟨i,hi,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨i1,h1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨ia,hia,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨p,hp,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨i3,h3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨ib,hib,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨q,hq,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨q1,hq1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨f0,hf0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨f1,hf1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨f2,hf2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨f3,hf3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨⟨row,back⟩,hrow,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨updated,hupdated,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases Result.ok.inj run
    have e1 := Result.ok.inj h1
    have e3 := Result.ok.inj h3
    have ea := Result.ok.inj hia
    have eb := Result.ok.inj hib
    refine ⟨d,i,ia,ib,p,a,b,row,back,updated,f0,f1,f2,f3,hn,hi,?_,?_,hp,ha,hb,?_,hrow,hupdated,rfl⟩
    · exact ea.symm.trans (congrArg (Usize.wrapping_sub 9#usize) e1.symm)
    · exact eb.symm.trans (congrArg (Usize.wrapping_sub 8#usize) e3.symm)
    · simp only [FJd_SourceFactor.reference,hq,hq1,hf0,hf1,hf2,hf3,bind_tc_ok]
#print axioms source
end AspisR1.FJf_PointBody
end
