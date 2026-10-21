import S4FourDotsP6ArrayOperationV1
import S4FirstTailReadTotalRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1P6ArrayForwardRootV1
open AspisR1FromFnP6 (statefulFromFnRun)
open AspisR1FromFnP6Generated

theorem stateful_run_forward {S A : Type}
    (step : S→Nat→Result (A×S)) (N : Nat) (I : S→Nat→Prop) (V : A→Prop)
    (hstep : ∀ s i, i<N → I s i → ∃ value next,
      step s i=.ok (value,next) ∧ V value ∧ I next (i+1))
    (count start : Nat) (state : S) (hbudget : start+count≤N) (hstate : I state start) :
    ∃ values final, statefulFromFnRun step count start state=.ok (values,final) ∧
      values.length=count ∧ (∀ x∈values,V x) ∧ I final (start+count) := by
  induction count generalizing start state with
  | zero =>
    refine ⟨[],state,rfl,rfl,?_,?_⟩
    · intro x hx; cases hx
    · simpa only [Nat.add_zero] using hstate
  | succ count ih =>
    obtain ⟨value,next,hs,hv,hi⟩ := hstep state start (by omega) hstate
    obtain ⟨values,final,hr,hlen,hvals,hfinal⟩ := ih (start+1) next (by omega) hi
    refine ⟨value::values,final,?_,by simp only [List.length_cons,hlen],?_,?_⟩
    · simp only [statefulFromFnRun,hs,bind_tc_ok]
      change (do
        let (tail,last) ← statefulFromFnRun step count (start+1) next
        .ok (value::tail,last)) = .ok (value::values,final)
      rw [hr,bind_tc_ok]
    · intro x hx
      rcases List.mem_cons.mp hx with h | h
      · subst x; exact hv
      · exact hvals x h
    · have heq : start+(count+1)=start+1+count := by omega
      rw [heq]
      exact hfinal

/-- Forward totality of the retained P6 model from total bounded callback
transitions. This theorem does not establish Rust MaybeUninit correspondence. -/
theorem array_from_fn_forward {T F : Type}
    (N : Usize) (callback : core.ops.function.FnMut F Usize T)
    (I : F→Nat→Prop) (V : T→Prop) (initial : F)
    (hN : N.val<1024) (hinit : I initial 0)
    (hcallback : ∀ f i, i.val<N.val → I f i.val → ∃ value next,
      callback.call_mut f i=.ok (value,next) ∧ V value ∧ I next (i.val+1)) :
    ∃ values : Array T N, arrayFromFnP6 N callback initial=.ok values ∧
      (∀ x∈values.val,V x) := by
  let J : (F×Usize)→Nat→Prop := fun s n => s.2.val=n ∧ I s.1 n
  have hs : ∀ s i, i<N.val → J s i → ∃ value next,
      fnMutStep callback s i=.ok (value,next) ∧ V value ∧ J next (i+1) := by
    intro s i hi hsi
    obtain ⟨value,next,hc,hv,hI⟩ := hcallback s.1 s.2 (by rw [hsi.1]; exact hi)
      (by rw [hsi.1]; exact hsi.2)
    obtain ⟨index,ha,hav⟩ := AspisR1FastDotsFirstTailReadTotalRootV1.small_checked_add s.2 1#usize
      (by change s.2.val+1<1024; omega)
    have hindex : index.val=i+1 := by change index.val=s.2.val+1 at hav; omega
    refine ⟨value,(next,index),?_,hv,?_,?_⟩
    · simp only [fnMutStep,hc,bind_tc_ok,ha]
      rfl
    · exact hindex
    · simpa only [hsi.1] using hI
  obtain ⟨items,final,hr,hlen,hvals,_⟩ := stateful_run_forward (fnMutStep callback) N.val J V hs
    N.val 0 (initial,0#usize) (by omega) ⟨rfl,hinit⟩
  have hlen' : items.length=N.val := by simpa only [Nat.zero_add] using hlen
  let values : Array T N := ⟨items,hlen'⟩
  refine ⟨values,?_,hvals⟩
  simp only [arrayFromFnP6,core.array.from_fn_model,core.array.from_fn_trace_model,
    packArrayState,hr,dif_pos hlen',bind_tc_ok]
  rfl

#print axioms stateful_run_forward
#print axioms array_from_fn_forward
end AspisR1P6ArrayForwardRootV1
