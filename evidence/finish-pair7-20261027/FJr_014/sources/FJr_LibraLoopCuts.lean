import FJm_LibraDone
import FJm_LibraBodyCut
import FIp_RangeNone
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_LibraLoopCuts
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NE NQ)
open FJm_LibraStages (Weights)

theorem done_bound (ap0 ap1 : Weights) (extra : Array NQ 2#usize) (iter : FIo_RangeNext.Range)
    (weights out : Weights)
    (run : FIo_Native.weights.factored_s2_libra_weights_loop.body ap0 ap1 extra iter weights=ok (.done out)) :
    iter.end.val ≤ iter.start.val := by
  have original := run
  unfold FIo_Native.weights.factored_s2_libra_weights_loop.body at run
  obtain ⟨⟨o,cursor⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none=>exact FIp_RangeNone.none_next iter cursor hn
  | some side=>
    obtain ⟨base,high,q4,q16,low,i0,i1,i2,i3,t0,t1,t2,t3,first2,first3,all,
      hpowers,hlow,ht0,ht1,ht2,ht3,htotals,hfinish⟩ :=
      FJm_LibraSomeCut.reached ap0 ap1 extra iter cursor weights side (.done out) hn original
    exact False.elim (FJm_LibraDone.finish side low i3 first2 first3 all q4 q16 ap1 weights out cursor hfinish)

theorem head (ap0 ap1 : Weights) (extra : Array NQ 2#usize) (iter : FIo_RangeNext.Range)
    (weights out : Weights) (more : iter.start.val < iter.end.val)
    (run : FIo_Native.weights.factored_s2_libra_weights_loop iter ap0 ap1 extra weights=ok out) :
    ∃ (cursor : FIo_RangeNext.Range) (next : Weights),
      FIo_Native.weights.factored_s2_libra_weights_loop.body ap0 ap1 extra iter weights=ok (.cont (cursor,next)) ∧
      FIo_Native.weights.factored_s2_libra_weights_loop cursor ap0 ap1 extra next=ok out := by
  unfold FIo_Native.weights.factored_s2_libra_weights_loop at run
  rw [loop] at run
  cases hb : FIo_Native.weights.factored_s2_libra_weights_loop.body ap0 ap1 extra iter weights with
  | fail e=>simp only [hb] at run;cases run
  | div=>simp only [hb] at run;cases run
  | ok result=>
    simp only [hb] at run
    cases result with
    | done value=>have stop:=done_bound ap0 ap1 extra iter weights value hb;omega
    | cont next=>exact ⟨next.1,next.2,rfl,run⟩

theorem stopped (ap0 ap1 : Weights) (extra : Array NQ 2#usize) (iter : FIo_RangeNext.Range)
    (weights out : Weights) (stop : iter.end.val ≤ iter.start.val)
    (run : FIo_Native.weights.factored_s2_libra_weights_loop iter ap0 ap1 extra weights=ok out) :
    out=weights := by
  unfold FIo_Native.weights.factored_s2_libra_weights_loop at run
  rw [loop] at run
  cases hb : FIo_Native.weights.factored_s2_libra_weights_loop.body ap0 ap1 extra iter weights with
  | fail e=>simp only [hb] at run;cases run
  | div=>simp only [hb] at run;cases run
  | ok result=>
    simp only [hb] at run
    cases result with
    | done value=>
      cases Result.ok.inj run
      exact FJm_LibraDone.value ap0 ap1 extra iter weights out hb
    | cont next=>
      obtain ⟨side,cursor,base,high,q4,q16,low,i0,i1,i2,i3,t0,t1,t2,t3,first2,first3,all,
        hn,rest⟩ := FJm_LibraBodyCut.reached ap0 ap1 extra iter next.1 weights next.2 hb
      have more := (FIo_RangeNext.some_next iter cursor side hn).2.2.2
      omega

#print axioms done_bound
#print axioms head
#print axioms stopped
end AspisR1.FJr_LibraLoopCuts
end
