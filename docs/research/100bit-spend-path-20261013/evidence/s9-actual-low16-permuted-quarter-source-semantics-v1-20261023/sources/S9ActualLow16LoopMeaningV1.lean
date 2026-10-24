import S9ActualLow16BodyMeaningV1
import S9NativeArrayCanonicalV1
import S9StatementSourceLoopFactsV1
import S9LoopInvariantPropertyV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualLow16LoopMeaningV1
open AspisR1S9ActualLow16BodyTraceV1
open AspisR1S9ActualLow16BodyMeaningV1
open AspisR1S9NativeWideDecodedArithmeticV1 (decode Canonical)
open AspisR1S9FactorArrayEntryV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1 (next_some_progress index_success_bound)
open AspisR1S9StatementSourceLoopFactsV1 (next_none_stop)

def Prefix (ap0 ap1 : Powers) (upto : Nat) (low : Low) : Prop :=
  ∀ (j : Usize) (hj : j.val<16), j.val<upto →
    Canonical (atN low j hj) ∧ decode (atN low j hj)=expectedLow ap0 ap1 j.val

theorem prefix_write (ap0 ap1 : Powers) (low lowNext : Low) (s : Usize) (value : W)
    (hs : s.val<16) (hp : Prefix ap0 ap1 s.val low)
    (hc : Canonical value) (hv : decode value=expectedLow ap0 ap1 s.val)
    (hu : Array.update low s value=.ok lowNext) : Prefix ap0 ap1 (s.val+1) lowNext := by
  have he := accepted_update_eq_set low s hs value lowNext hu
  subst lowNext
  intro j hj hlt
  rw [atN_set low s j value hs hj]
  by_cases hjs : j.val=s.val
  · rw [if_pos hjs]
    exact ⟨hc,hjs.symm ▸ hv⟩
  · rw [if_neg hjs]
    exact hp j hj (by omega)

theorem low_body_done (ap0 ap1 : Powers) (it : Iter) (low out : Low)
    (h : weights.Weights.pair_loop15.body ap0 ap1 it low=.ok (.done out)) :
    out=low ∧ ∃ itNext,core.iter.range.IteratorRange.next core.iter.range.StepUsize it=.ok (none,itNext) := by
  rcases low_body_success_trace ap0 ap1 it low _ h with hd | hc
  · obtain ⟨itNext,hn,he⟩ := hd
    exact ⟨ControlFlow.done.inj he,itNext,hn⟩
  · obtain ⟨s,itNext,lo,pi,hi,pj,x,y,product,value,m,next,
      hn,hl,hpi,hx,hh,hpj,hy,hprod,hm,hvalue,hu,he⟩ := hc
    cases he

/-- All16 source cells are overwritten, with the exact PERM/QUARTER² formula.
The initial low buffer is arbitrary; no initial meaning/canonicality is used. -/
theorem actual_low_loop_success (ap0 ap1 : Powers) (it : Iter) (low out : Low)
    (hp0 : GoodPowers ap0) (hp1 : GoodPowers ap1)
    (hstart : it.start.val=0) (hend : it.end.val=16)
    (h : weights.Weights.pair_loop15 it ap0 ap1 low=.ok out) :
    Prefix ap0 ap1 16 out ∧ AspisR1S9NativeArrayCanonicalV1.ReadsCanonical out := by
  let step : State → Result (ControlFlow State Low) :=
    fun s => weights.Weights.pair_loop15.body ap0 ap1 s.1 s.2
  let measure : State → Nat := fun s => s.1.end.val-s.1.start.val
  let inv : State → Prop := fun s => s.1.end.val=16 ∧ s.1.start.val≤16 ∧ Prefix ap0 ap1 s.1.start.val s.2
  let post : Low → Prop := fun a => Prefix ap0 ap1 16 a
  have hd : ∀ s a,inv s → step s=.ok (.done a) → post a := by
    rintro ⟨iter,buf⟩ a hi hb
    change iter.end.val=16 ∧ iter.start.val≤16 ∧ Prefix ap0 ap1 iter.start.val buf at hi
    obtain ⟨ha,itNext,hn⟩ := low_body_done ap0 ap1 iter buf a hb
    have hstop := next_none_stop iter itNext hn
    have hfull : iter.start.val=16 := by omega
    subst a
    change Prefix ap0 ap1 16 buf
    exact hfull ▸ hi.2.2
  have hc : ∀ s s',inv s → step s=.ok (.cont s') → inv s' := by
    rintro ⟨iter,buf⟩ ⟨itNext,bufNext⟩ hi hb
    change iter.end.val=16 ∧ iter.start.val≤16 ∧ Prefix ap0 ap1 iter.start.val buf at hi
    obtain ⟨j,value,hn,hu,hvalue,hmeaning⟩ := low_body_cont_meaning ap0 ap1 iter itNext buf bufNext hp0 hp1 hb
    obtain ⟨hlt,hj,hs,he⟩ := next_some_progress iter itNext j hn
    have hjval : j.val=iter.start.val := congrArg UScalar.val hj
    have hbound : j.val<16 := by omega
    have hprefix : Prefix ap0 ap1 j.val buf := hjval.symm ▸ hi.2.2
    have hnew := prefix_write ap0 ap1 buf bufNext j value hbound hprefix hvalue hmeaning hu
    change itNext.end.val=16 ∧ itNext.start.val≤16 ∧ Prefix ap0 ap1 itNext.start.val bufNext
    refine ⟨?_,by omega,?_⟩
    · rw [he]; exact hi.1
    · have heq : itNext.start.val=j.val+1 := by omega
      exact heq.symm ▸ hnew
  have hdec : ∀ s s',step s=.ok (.cont s') → measure s'<measure s := by
    rintro ⟨iter,buf⟩ ⟨itNext,bufNext⟩ hb
    obtain ⟨j,value,hn,hu,hvalue,hmeaning⟩ := low_body_cont_meaning ap0 ap1 iter itNext buf bufNext hp0 hp1 hb
    obtain ⟨hlt,hj,hs,he⟩ := next_some_progress iter itNext j hn
    dsimp only [measure]
    have hev : itNext.end.val=iter.end.val := congrArg UScalar.val he
    omega
  have hinit : inv (it,low) := by
    change it.end.val=16 ∧ it.start.val≤16 ∧ Prefix ap0 ap1 it.start.val low
    refine ⟨hend,by omega,?_⟩
    intro j hj hlt
    omega
  have hrun : Aeneas.Std.loop step (it,low)=.ok out := h
  have hmeaning := AspisR1S9LoopInvariantPropertyV1.loop_invariant_property step measure inv post
    hd hc hdec (it,low) out hinit hrun
  refine ⟨hmeaning,?_⟩
  intro j value hread
  have hj := index_success_bound out j value hread
  have he := accepted_index_eq_atN out j hj value hread
  rw [he]
  exact (hmeaning j hj hj).1

theorem actual_shared_low_loop_success (ap0 ap1 : Powers) (it : Iter) (low out : Low)
    (hp0 : GoodPowers ap0) (hp1 : GoodPowers ap1)
    (hstart : it.start.val=0) (hend : it.end.val=16)
    (h : weights.Weights.pair_loop7 it ap0 ap1 low=.ok out) :
    Prefix ap0 ap1 16 out ∧ AspisR1S9NativeArrayCanonicalV1.ReadsCanonical out := by
  rw [shared_low_eq] at h
  exact actual_low_loop_success ap0 ap1 it low out hp0 hp1 hstart hend h

#print axioms prefix_write
#print axioms low_body_done
#print axioms actual_low_loop_success
#print axioms actual_shared_low_loop_success
end AspisR1S9ActualLow16LoopMeaningV1
