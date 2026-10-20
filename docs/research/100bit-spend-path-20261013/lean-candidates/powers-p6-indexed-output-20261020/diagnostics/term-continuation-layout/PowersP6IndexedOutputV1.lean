import S3PowersCanonicalTraceV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PowersP6IndexedOutputV1
open AspisR1PowersConcreteMul AspisR1PowersExactProduct
open AspisR1FromFnP6 AspisR1S3PowersCanonicalTraceV1

theorem powerStep_output_exact {N : Usize}
    (x : CallbackWide) (index : Nat) (state : PowerState N)
    (value : CallbackWide) (next : PowerState N)
    (hstate : powerStateOK x state index)
    (hstep : powerStep state index=ok (value,next)) :
    decode value=decode x^index := by
  rcases hstate with ⟨hsx,hp,hx,hpower⟩
  have hpower' : decode state.1=decode state.2^index := by rw [hsx]; exact hpower
  unfold powerStep at hstep
  have h := powers_callback_success_power_invariant state.1 state.2 value next
    hp hx 0#usize index hpower' hstep
  simpa only [hsx] using h.2.1

theorem powersTrace_indexed_output {N : Usize}
    (x : CallbackWide) {count start : Nat} {initial final : PowerState N}
    {values : List CallbackWide}
    (htrace : StatefulFromFnTrace powerStep count start initial values final)
    (hinitial : powerStateOK x initial start) :
    ∀ index : Nat,index<count → ∃ value,
      values[index]?=some value ∧ Canonical value ∧ decode value=decode x^(start+index) := by
  revert hinitial
  induction htrace with
  | done start state =>
    intro hs index hi
    omega
  | @call count start state state' final value values hcall htail ih =>
    intro hs index hi
    have hnext := powerStep_preserves x start state value state' hs hcall
    cases index with
    | zero =>
      exact ⟨value,rfl,hnext.1,by simpa only [Nat.add_zero] using
        powerStep_output_exact x start state value state' hs hcall⟩
    | succ index =>
      obtain ⟨actual,hread,hcanonical,hdecode⟩ := ih hnext.2 index (by omega)
      refine ⟨actual,?_,hcanonical,?_⟩
      · simpa only [List.getElem?_cons_succ] using hread
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hdecode

theorem powersN_model_success_indexed {N : Usize} (x : CallbackWide)
    (values : List CallbackWide) (final : PowerState N) (hx : Canonical x)
    (hrun : statefulFromFnRun powerStep N.val 0
      (AspisR1CurrentPowers.field.WideExact.ONE,x)=ok (values,final)) :
    ∀ index : Nat,index<N.val → ∃ value,
      values[index]?=some value ∧ Canonical value ∧ decode value=decode x^index := by
  have ht := (statefulFromFnRun_success_iff_trace powerStep N.val 0
    (AspisR1CurrentPowers.field.WideExact.ONE,x) values final).mp hrun
  simpa only [Nat.zero_add] using
    powersTrace_indexed_output x ht (powers_initial_stateOK x hx)

theorem powersN_model_total_indexed {N : Usize} (x : CallbackWide) (hx : Canonical x) :
    ∃ values final,
      statefulFromFnRun powerStep N.val 0
        (AspisR1CurrentPowers.field.WideExact.ONE,x)=ok (values,final) ∧
      values.length=N.val ∧
      (∀ index : Nat,index<N.val → ∃ value,
        values[index]?=some value ∧ Canonical value ∧ decode value=decode x^index) ∧
      powerStateOK (N := N) x final N.val := by
  obtain ⟨values,final,hrun,hlen,hcanonical,hfinal⟩ := powersN_model_total (N := N) x hx
  exact ⟨values,final,hrun,hlen,powersN_model_success_indexed x values final hx hrun,hfinal⟩

#print axioms powerStep_output_exact
#print axioms powersTrace_indexed_output
#print axioms powersN_model_success_indexed
#print axioms powersN_model_total_indexed
end AspisR1PowersP6IndexedOutputV1
