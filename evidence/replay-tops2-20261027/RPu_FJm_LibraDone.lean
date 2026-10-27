import RPu_FJm_LibraSomeCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_LibraDone
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NE NQ)
open FJm_LibraStages (Weights)

theorem finish (side : Usize) (low : NE) (i3 : Usize) (first2 first3 all : NE) (q4 q16 : NQ)
    (ap1 weights out : Weights) (cursor : FIo_RangeNext.Range)
    (run : FJm_LibraStages.finish side low i3 first2 first3 all q4 q16 ap1 weights cursor=ok (.done out)) : False := by
  unfold FJm_LibraStages.finish at run
  split at run
  all_goals
    repeat' first
    | (solve | cases run)
    | obtain ⟨value,returned,run⟩ := Port3_PushFrame.bind_success _ _ _ run

theorem value (ap0 ap1 : Weights) (extra : Array NQ 2#usize) (iter : FIo_RangeNext.Range)
    (weights out : Weights)
    (run : FIo_Native.weights.factored_s2_libra_weights_loop.body ap0 ap1 extra iter weights=ok (.done out)) :
    out=weights := by
  have original := run
  unfold FIo_Native.weights.factored_s2_libra_weights_loop.body at run
  obtain ⟨⟨o,cursor⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none=>exact (ControlFlow.done.inj (Result.ok.inj run)).symm
  | some side=>
    obtain ⟨base,high,q4,q16,low,i0,i1,i2,i3,t0,t1,t2,t3,first2,first3,all,
      hpowers,hlow,ht0,ht1,ht2,ht3,htotals,hfinish⟩ :=
      FJm_LibraSomeCut.reached ap0 ap1 extra iter cursor weights side (.done out) hn original
    exact False.elim (finish side low i3 first2 first3 all q4 q16 ap1 weights out cursor hfinish)
#print axioms finish
#print axioms value
end AspisR1.FJm_LibraDone
end
