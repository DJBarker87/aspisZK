import NIT_LowStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_LowChain
open Aeneas Aeneas.Std Result ControlFlow LPi_FieldValues NIT_Cuts NIT_FieldInterpretation NIT_PairComposition

theorem local_log (ap0 ap1 : Powers) (h0 : canonical ap0) (h1 : canonical ap1)
 (i : Usize) (small : i.val<16) (before : LowCells) (hc : canonical before) :
 ∃ l after,cutLow ap0 ap1 i.val before l after ∧ EMul l.a l.b l.product ∧
 NIT_LowInterpretation.Scale l.scale_a l.scaled ∧ canonical after := by
 let lhs := epick ap0 (perm (i.val%4))
 let rhs := epick ap1 (perm (i.val/4))
 obtain ⟨product,run,cp,value⟩ := LPi_TowerValues.wide_mul lhs rhs
  (epick_canonical ap0 h0 _) (epick_canonical ap1 h1 _)
 obtain ⟨scaled,scale,cs,sv⟩ := NHX_LowScale.total product
 let l : Low := {a:=lhs,b:=rhs,product:=product,scale_a:=product,scaled:=scaled,
  scale_b:=134217728#u32,base_a:=536870912#u32,base_b:=536870912#u32,tags:=[0,1,2],count:=3}
 let after := NIT_ArrayFrames.put before i.val scaled
 have frame : ∀ k,k<16 → epick after k=if k=i.val then scaled else epick before k := by
  intro k _
  exact NIT_ArrayFrames.pick_put NHI_Scalar.zero before i.val scaled small k
 have update := NIT_LowInterpretation.update_model before i scaled small
 exact ⟨l,after,⟨small,h0,h1,hc,cp,cs,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,frame⟩,
  value,sv,NHM_ArrayPreserve.canonical canonE before after i scaled hc cs update⟩

inductive Trace (ap0 ap1 : Powers) : Nat → NHX_LowDomain.State → LowCells → Prop
 | done (fuel : Nat) (s : NHX_LowDomain.State) (stop : s.1.end.val ≤ s.1.start.val) :
   Trace ap0 ap1 (fuel+1) s s.2
 | step (fuel : Nat) (s : NHX_LowDomain.State) (out after : LowCells) (l : Low)
   (last : s.1.end.val=16) (cut : cutLow ap0 ap1 s.1.start.val s.2 l after)
   (law : EMul l.a l.b l.product) (scale : NIT_LowInterpretation.Scale l.scale_a l.scaled)
   (rest : NHI_RangeProgress.Range)
   (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1=ok (some s.1.start,rest))
   (tail : Trace ap0 ap1 fuel (rest,after) out) : Trace ap0 ap1 (fuel+1) s out

theorem interpreted (ap0 ap1 : Powers) (fuel : Nat) (s : NHX_LowDomain.State)
 (out : LowCells) (trace : Trace ap0 ap1 fuel s out) :
 NHI_CountedLoop.unroll (NHX_LowDomain.body ap0 ap1) fuel s=ok out := by
 induction trace with
 | done fuel s stop =>
   have next := NHI_ForwardRange.done s.1 stop
   simp only [NHI_CountedLoop.unroll,NHX_LowDomain.body,FIo_Native.weights.Weights.pair_loop15.body,next,bind_tc_ok]
   rfl
 | step fuel s out after l last cut law scale rest next tail ih =>
   obtain ⟨actual,body,hn,_,_,_⟩ := NIT_LowStep.step ap0 ap1 s after l cut law scale last
   have same : actual=rest := congrArg Prod.snd (Result.ok.inj (hn.symm.trans next))
   rw [same] at body
   simp only [NHI_CountedLoop.unroll,body,bind_tc_ok,ih]

theorem trace_exists (ap0 ap1 : Powers) (h0 : canonical ap0) (h1 : canonical ap1)
 (fuel : Nat) (s : NHX_LowDomain.State) (last : s.1.end.val=16)
 (bound : s.1.start.val≤16) (hc : canonical s.2) (enough : 16-s.1.start.val<fuel) :
 ∃ out,Trace ap0 ap1 fuel s out ∧ canonical out := by
 induction fuel generalizing s with
 | zero => omega
 | succ fuel ih =>
   by_cases active : s.1.start.val<16
   · obtain ⟨l,after,cut,law,scale,canonical⟩ := local_log ap0 ap1 h0 h1 s.1.start active s.2 hc
     obtain ⟨rest,body,next,he,inc,_⟩ := NIT_LowStep.step ap0 ap1 s after l cut law scale last
     obtain ⟨out,tail,co⟩ := ih (rest,after) he (by change rest.start.val≤16;omega)
      canonical (by change 16-rest.start.val<fuel;omega)
     exact ⟨out,.step fuel s out after l last cut law scale rest next tail,co⟩
   · exact ⟨s.2,.done fuel s (by omega),hc⟩

theorem complete (ap0 ap1 : Powers) (h0 : canonical ap0) (h1 : canonical ap1)
 (cells : LowCells) (hc : canonical cells) :
 ∃ out,Trace ap0 ap1 17 ({start:=0#usize,«end»:=16#usize},cells) out ∧
 FIo_Native.weights.Weights.pair_loop15 {start:=0#usize,«end»:=16#usize} ap0 ap1 cells=ok out ∧
 canonical out := by
 obtain ⟨out,trace,canonical⟩ := trace_exists ap0 ap1 h0 h1 17
  ({start:=0#usize,«end»:=16#usize},cells) rfl (by change (0:Nat)≤16;omega) hc
  (by change (16:Nat)-0<17;omega)
 refine ⟨out,trace,?_,canonical⟩
 rw [NIG_LowLoop.low_source]
 exact interpreted ap0 ap1 17 _ out trace

#print axioms local_log
#print axioms interpreted
#print axioms trace_exists
#print axioms complete
end AspisR1.NIT_LowChain
