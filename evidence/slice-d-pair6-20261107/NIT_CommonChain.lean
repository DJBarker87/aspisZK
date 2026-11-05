import NIT_CommonInterpretation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_CommonChain
open Aeneas Aeneas.Std Result ControlFlow LPi_FieldValues NIT_Cuts NIT_FieldInterpretation NIT_PairComposition
abbrev row2 (w : W) := NHI_ScalarDomain.pick (NHI_ScalarDomain.pick w.factors 0 (by decide)) 2 (by decide)
abbrev row3 (w : W) := NHI_ScalarDomain.pick (NHI_ScalarDomain.pick w.factors 0 (by decide)) 3 (by decide)

theorem local_log (w : W) (hf : NHI_TensorOuterStep.Factors w)
 (j : Usize) (small : j.val<16) (before : CommonCells) (hc : NHI_CellCanon.array before) :
 ∃ l after,cutCommon (row2 w) (row3 w) j.val before l after ∧
 QMul l.lhs l.rhs l.reply ∧ NHI_CellCanon.array after := by
 let lhs := kpick (row2 w) (j.val%4)
 let rhs := kpick (row3 w) (j.val/4)
 have cl := NIT_CommonInterpretation.kpick_canonical (row2 w) (hf 0 (by decide) 2 (by decide)) _ (by change j.val%4<4;omega)
 have cr := NIT_CommonInterpretation.kpick_canonical (row3 w) (hf 0 (by decide) 3 (by decide)) _ (by change j.val/4<4;omega)
 obtain ⟨reply,run,canonical,value⟩ := LPi_TowerValues.qm_mul lhs rhs cl cr
 let l : Common := ⟨lhs,rhs,reply,1⟩
 let after := NIT_ArrayFrames.put before j.val reply
 have frame : ∀ k,k<16 → kpick after k=if k=j.val then reply else kpick before k := by
  intro k _
  exact NIT_ArrayFrames.pick_put FIo_Native.aspis_core.field.QM31.ZERO before j.val reply small k
 have update := NIT_LowInterpretation.update_model before j reply small
 exact ⟨l,after,⟨small,rfl,rfl,rfl,frame⟩,value,
  NHM_ArrayPreserve.canonical canonQ before after j reply hc canonical update⟩

inductive Trace (w : W) : Nat → NHX_CommonDomain.State → W×CommonCells → Prop
 | done (fuel : Nat) (s : NHX_CommonDomain.State) (stop : s.1.end.val ≤ s.1.start.val) :
   Trace w (fuel+1) s (w,s.2)
 | step (fuel : Nat) (s : NHX_CommonDomain.State) (out : W×CommonCells)
   (after : CommonCells) (l : Common) (last : s.1.end.val=16)
   (cut : cutCommon (row2 w) (row3 w) s.1.start.val s.2 l after)
   (law : QMul l.lhs l.rhs l.reply) (rest : NHI_RangeProgress.Range)
   (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1=ok (some s.1.start,rest))
   (tail : Trace w fuel (rest,after) out) : Trace w (fuel+1) s out

theorem interpreted (w : W) (hf : NHI_TensorOuterStep.Factors w) (fuel : Nat)
 (s : NHX_CommonDomain.State) (out : W×CommonCells) (trace : Trace w fuel s out) :
 NHI_CountedLoop.unroll (NHX_CommonDomain.body w) fuel s=ok out := by
 induction trace with
 | done fuel s stop =>
   have next := NHI_ForwardRange.done s.1 stop
   simp only [NHI_CountedLoop.unroll,NHX_CommonDomain.body,FIo_Native.weights.Weights.pair_loop1.body,next,bind_tc_ok]
   rfl
 | step fuel s out after l last cut law rest next tail ih =>
   obtain ⟨actual,body,hn,_,_⟩ := NIT_CommonInterpretation.step w hf s after l cut law last
   have same : actual=rest := congrArg Prod.snd (Result.ok.inj (hn.symm.trans next))
   rw [same] at body
   simp only [NHI_CountedLoop.unroll,body,bind_tc_ok,ih]

theorem trace_exists (w : W) (hf : NHI_TensorOuterStep.Factors w) (fuel : Nat)
 (s : NHX_CommonDomain.State) (last : s.1.end.val=16) (bound : s.1.start.val≤16)
 (hc : NHI_CellCanon.array s.2) (enough : 16-s.1.start.val<fuel) :
 ∃ out,Trace w fuel s out ∧ out.1=w ∧ NHI_CellCanon.array out.2 := by
 induction fuel generalizing s with
 | zero => omega
 | succ fuel ih =>
   by_cases active : s.1.start.val<16
   · obtain ⟨l,after,cut,law,canonical⟩ := local_log w hf s.1.start active s.2 hc
     obtain ⟨rest,body,next,he,inc⟩ := NIT_CommonInterpretation.step w hf s after l cut law last
     obtain ⟨out,tail,owner,co⟩ := ih (rest,after) he
      (by change rest.start.val≤16;omega) canonical (by change 16-rest.start.val<fuel;omega)
     exact ⟨out,.step fuel s out after l last cut law rest next tail,owner,co⟩
   · exact ⟨(w,s.2),.done fuel s (by omega),rfl,hc⟩

/-- Sixteen native one-step cuts plus the CLOSED field law, composed by finite
induction to the exact emitted loop; the SAME owner and full array are retained. -/
theorem complete (w : W) (hf : NHI_TensorOuterStep.Factors w) (cells : CommonCells)
 (hc : NHI_CellCanon.array cells) :
 ∃ out,Trace w 17 ({start:=0#usize,«end»:=16#usize},cells) out ∧
 FIo_Native.weights.Weights.pair_loop1 {start:=0#usize,«end»:=16#usize} w cells=ok out ∧
 out.1=w ∧ NHI_CellCanon.array out.2 := by
 obtain ⟨out,trace,owner,canonical⟩ := trace_exists w hf 17
  ({start:=0#usize,«end»:=16#usize},cells) rfl (by change (0:Nat)≤16;omega) hc
  (by change (16:Nat)-0<17;omega)
 refine ⟨out,trace,?_,owner,canonical⟩
 rw [NIG_CommonLoop.common_source]
 exact interpreted w hf 17 _ out trace

#print axioms local_log
#print axioms interpreted
#print axioms trace_exists
#print axioms complete
end AspisR1.NIT_CommonChain
