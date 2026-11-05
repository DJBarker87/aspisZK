import NIT_LibraInterpretation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_LibraChain
open Aeneas Aeneas.Std Result ControlFlow LPi_FieldValues NIT_Cuts NIT_FieldInterpretation NIT_PairComposition

/-- Abort constructors terminate at the entered field call; no multiplication,
addition, subsequent iteration or invented Rust Err follows that prefix. -/
inductive Trace (f : Ref (Slice U8)) (libra : Powers) : Nat → NIG_LibraLoop.State → Result Parts → Prop
 | done (fuel : Nat) (s : NIG_LibraLoop.State) (stop : s.1.end.val ≤ s.1.start.val) :
   Trace f libra (fuel+1) s (ok s.2)
 | failed (fuel : Nat) (s : NIG_LibraLoop.State) (e : Error)
   (last : s.1.end.val=4) (active : s.1.start.val<4)
   (field : FIo_Native.weights.field f.value s.1.start=fail e) :
   Trace f libra (fuel+1) s (fail e)
 | diverged (fuel : Nat) (s : NIG_LibraLoop.State)
   (last : s.1.end.val=4) (active : s.1.start.val<4)
   (field : FIo_Native.weights.field f.value s.1.start=div) :
   Trace f libra (fuel+1) s div
 | step (fuel : Nat) (s : NIG_LibraLoop.State) (out : Result Parts) (after : Parts)
   (l : LibraLog) (last : s.1.end.val=4)
   (cut : cutLibraLog f libra s.1.start.val s.2 l after)
   (field : FIo_Native.weights.field f.value s.1.start=ok l.coefficient)
   (mulLaw : EMul l.mul_a l.mul_b l.product) (addLaw : EAdd l.add_a l.add_b l.reply)
   (rest : NHI_RangeProgress.Range)
   (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1=ok (some s.1.start,rest))
   (tail : Trace f libra fuel (rest,after) out) : Trace f libra (fuel+1) s out

def Post : Result Parts → Prop
 | .ok parts=>canonical parts | .fail _=>True | .div=>True

theorem field_failed (f : Ref (Slice U8)) (libra : Powers) (s : NIG_LibraLoop.State)
 (e : Error) (last : s.1.end.val=4) (active : s.1.start.val<4)
 (field : FIo_Native.weights.field f.value s.1.start=fail e) :
 NIG_LibraLoop.body f.value libra s=fail e := by
 obtain ⟨rest,next,_,_⟩ := NHI_ForwardRange.active s.1 (by omega)
 simp only [NIG_LibraLoop.body,next,bind_tc_ok]
 dsimp! only
 simp only [NIG_LibraLoop.window,epick_index s.2 4#usize (by decide),field,bind_tc_ok]
 rfl

theorem field_diverged (f : Ref (Slice U8)) (libra : Powers) (s : NIG_LibraLoop.State)
 (last : s.1.end.val=4) (active : s.1.start.val<4)
 (field : FIo_Native.weights.field f.value s.1.start=div) :
 NIG_LibraLoop.body f.value libra s=div := by
 obtain ⟨rest,next,_,_⟩ := NHI_ForwardRange.active s.1 (by omega)
 simp only [NIG_LibraLoop.body,next,bind_tc_ok]
 dsimp! only
 simp only [NIG_LibraLoop.window,epick_index s.2 4#usize (by decide),field,bind_tc_ok]
 rfl

theorem interpreted (f : Ref (Slice U8)) (libra : Powers) (fuel : Nat)
 (s : NIG_LibraLoop.State) (out : Result Parts) (trace : Trace f libra fuel s out) :
 NHI_CountedLoop.unroll (NIG_LibraLoop.body f.value libra) fuel s=out := by
 induction trace with
 | done fuel s stop =>
   have next := NHI_ForwardRange.done s.1 stop
   simp only [NHI_CountedLoop.unroll,NIG_LibraLoop.body,next,bind_tc_ok]
   rfl
 | failed fuel s e last active field =>
   rw [NHI_CountedLoop.unroll,field_failed f libra s e last active field]
   rfl
 | diverged fuel s last active field =>
   rw [NHI_CountedLoop.unroll,field_diverged f libra s last active field]
   rfl
 | step fuel s out after l last cut field mulLaw addLaw rest next tail ih =>
   obtain ⟨actual,body,hn,_,_,_⟩ := NIT_LibraInterpretation.step f libra s after l cut field mulLaw addLaw last
   have same : actual=rest := congrArg Prod.snd (Result.ok.inj (hn.symm.trans next))
   rw [same] at body
   simp only [NHI_CountedLoop.unroll,body,bind_tc_ok,ih]

theorem trace_exists (f : Ref (Slice U8)) (size : f.value.val.length=2048)
 (libra : Powers) (cl : canonical libra) (fuel : Nat) (s : NIG_LibraLoop.State)
 (last : s.1.end.val=4) (bound : s.1.start.val≤4) (cb : canonical s.2)
 (enough : 4-s.1.start.val<fuel) : ∃ out,Trace f libra fuel s out ∧ Post out := by
 induction fuel generalizing s with
 | zero => omega
 | succ fuel ih =>
   by_cases active : s.1.start.val<4
   · cases field : FIo_Native.weights.field f.value s.1.start with
     | fail e => exact ⟨fail e,.failed fuel s e last active field,True.intro⟩
     | div => exact ⟨div,.diverged fuel s last active field,True.intro⟩
     | ok coefficient =>
       obtain ⟨l,after,cut,coefficient_same,mulLaw,addLaw,canonical⟩ :=
        NIT_LibraInterpretation.local_log f size libra cl s.1.start active s.2 cb coefficient field
       have nativeField : FIo_Native.weights.field f.value s.1.start=ok l.coefficient := by
        rw [coefficient_same];exact field
       obtain ⟨rest,body,next,he,inc,_⟩ := NIT_LibraInterpretation.step f libra s after l cut nativeField mulLaw addLaw last
       obtain ⟨out,tail,post⟩ := ih (rest,after) he (by change rest.start.val≤4;omega)
        canonical (by change 4-rest.start.val<fuel;omega)
       exact ⟨out,.step fuel s out after l last cut nativeField mulLaw addLaw rest next tail,post⟩
   · exact ⟨ok s.2,.done fuel s (by omega),cb⟩

/-- Full Result of all four iterations, including outer fail/div prefixes;
all returning products/additions are CLOSED-packet instantiations. -/
theorem complete (f : Ref (Slice U8)) (size : f.value.val.length=2048)
 (libra : Powers) (cl : canonical libra) (parts : Parts) (cp : canonical parts) :
 ∃ out,Trace f libra 5 ({start:=0#usize,«end»:=4#usize},parts) out ∧
 FIo_Native.weights.Weights.pair_loop16 {start:=0#usize,«end»:=4#usize}
  f.value parts libra=out ∧ Post out := by
 obtain ⟨out,trace,post⟩ := trace_exists f size libra cl 5
  ({start:=0#usize,«end»:=4#usize},parts) rfl (by change (0:Nat)≤4;omega) cp
  (by change (4:Nat)-0<5;omega)
 refine ⟨out,trace,?_,post⟩
 rw [NIG_LibraLoop.source]
 exact interpreted f libra 5 _ out trace

#print axioms field_failed
#print axioms field_diverged
#print axioms interpreted
#print axioms trace_exists
#print axioms complete
end AspisR1.NIT_LibraChain
