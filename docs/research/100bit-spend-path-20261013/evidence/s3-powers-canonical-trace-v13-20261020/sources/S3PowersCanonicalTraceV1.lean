import StatefulArrayFromFnModelV1
import CurrentPowersCallbackInvariant

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1S3PowersCanonicalTraceV1

open AspisR1PowersConcreteMul
open AspisR1PowersExactProduct
open AspisR1FromFnP6

abbrev PowerState (N : Usize) :=
  AspisR1CurrentPowers.weights.powers.closure N

def powerStateOK {N : Usize} (x : CallbackWide) (state : PowerState N)
    (index : Nat) : Prop :=
  state.2 = x ∧ Canonical state.1 ∧ Canonical state.2 ∧
    AspisR1PowersExactProduct.decode state.1 =
      AspisR1PowersExactProduct.decode x ^ index

theorem one_canonical : Canonical AspisR1CurrentPowers.field.WideExact.ONE := by
  norm_num [AspisR1PowersConcreteMul.Canonical,
    AspisR1PowersConcreteMul.toWide, AspisR1PowersConcreteMul.toQM,
    AspisR1CurrentWideMul.CanonicalWide,
    AspisR1CurrentWideMul.CanonicalQM,
    AspisR1CurrentWideMul.CanonicalCM,
    AspisR1.ExtractedCurrentTowerAdd.CanonicalQM,
    AspisR1.ExtractedCurrentTowerAdd.CanonicalCM,
    AspisR1.ExtractedCurrentTowerAdd.P,
    AspisR1.ExtractedCurrentM31AddSub.P,
    AspisR1CurrentPowers.field.WideExact.ONE,
    AspisR1CurrentPowers.field.QM31.ONE,
    AspisR1CurrentPowers.field.QM31.ZERO]

theorem one_decode : AspisR1PowersExactProduct.decode
    AspisR1CurrentPowers.field.WideExact.ONE = 1 := by
  apply QuadraticAlgebra.ext
  all_goals apply QuadraticAlgebra.ext
  all_goals apply QuadraticAlgebra.ext
  all_goals norm_num [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
    QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero,
    AspisR1PowersExactProduct.decode,
    AspisR1PowersExactProduct.toFull, AspisR1PowersExactProduct.toFullQM,
    AspisR1CurrentWide.Proof.decodeWide, AspisR1CurrentWide.Proof.decodeQM,
    AspisR1CurrentWide.Proof.toQM, AspisR1CurrentWide.Proof.toCM,
    AspisR1.ExtractedCurrentQM31Exact.decode,
    AspisR1CurrentPowers.field.WideExact.ONE,
    AspisR1CurrentPowers.field.QM31.ONE,
    AspisR1CurrentPowers.field.QM31.ZERO]

theorem powers_initial_stateOK {N : Usize} (x : CallbackWide)
    (hx : Canonical x) :
    powerStateOK (N := N) x (AspisR1CurrentPowers.field.WideExact.ONE, x) 0 := by
  refine ⟨rfl, one_canonical, hx, ?_⟩
  rw [one_decode, pow_zero]

def powerStep {N : Usize} (state : PowerState N) (_index : Nat) :
    Result (CallbackWide × PowerState N) :=
  AspisR1CurrentPowers.weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once
    sourceMul state 0#usize

/-- The generated FnMut ABI returns a state transformer (`back`); this is the
state-threading operation consumed by the P6 from_fn model. -/
def powerFnMutCall {N : Usize} (state : PowerState N) (i : Usize) :
    Result (CallbackWide × PowerState N) := do
  let (value, state1, back) ←
    AspisR1CurrentPowers.weights.powers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      sourceMul state i
  ok (value, back state1)

theorem generatedFnMut_eq_callOnce {N : Usize} (state : PowerState N) (i : Usize) :
    powerFnMutCall state i =
      AspisR1CurrentPowers.weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once
        sourceMul state i := by
  rcases state with ⟨p, x⟩
  cases hm : sourceMul p x with
  | fail e =>
      simp [powerFnMutCall,
        AspisR1CurrentPowers.weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once,
        AspisR1CurrentPowers.weights.powers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut, hm]
  | div =>
      simp [powerFnMutCall,
        AspisR1CurrentPowers.weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once,
        AspisR1CurrentPowers.weights.powers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut, hm]
  | ok product =>
      simp [powerFnMutCall,
        AspisR1CurrentPowers.weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once,
        AspisR1CurrentPowers.weights.powers.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut, hm]

theorem powerStep_eq_generatedFnMut {N : Usize} (state : PowerState N)
    (index : Nat) : powerStep state index = powerFnMutCall state 0#usize := by
  unfold powerStep
  exact (generatedFnMut_eq_callOnce state 0#usize).symm

theorem powerStep_preserves {N : Usize}
    (x : CallbackWide) (index : Nat) (state : PowerState N)
    (value : CallbackWide) (next : PowerState N)
    (hstate : powerStateOK x state index)
    (hstep : powerStep state index = .ok (value, next)) :
    Canonical value ∧ powerStateOK x next (index + 1) := by
  rcases hstate with ⟨hsx, hp, hx, hpower⟩
  have hcall := AspisR1CurrentPowers.call_once_index_independent
    sourceMul state 0#usize 0#usize
  have hcallValue :
      AspisR1CurrentPowers.weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once
      sourceMul state 0#usize = .ok (value, next) := by
    unfold powerStep at hstep
    exact hcall.symm.trans hstep
  have hpower' : AspisR1PowersExactProduct.decode state.1 =
      AspisR1PowersExactProduct.decode state.2 ^ index := by
    rw [hsx]
    exact hpower
  obtain ⟨hv, hval, hnextx, hnextcan, hnextpow⟩ :=
    AspisR1PowersExactProduct.powers_callback_success_power_invariant
      (state.1) (state.2) value next hp hx 0#usize index hpower' hcallValue
  have hx' : Canonical x := by
    rw [← hsx]
    exact hx
  refine ⟨hv, ?_⟩
  refine ⟨?_, hnextcan, ?_, ?_⟩
  · exact hnextx.trans hsx
  · rw [hnextx, hsx]
    exact hx'
  · rw [hsx] at hnextpow
    exact hnextpow

theorem powersTrace_canonical {N : Usize}
    (x : CallbackWide) (count start : Nat) (initial final : PowerState N)
    (values : List CallbackWide)
    (hinitial : powerStateOK x initial start)
    (htrace : StatefulFromFnTrace powerStep count start initial values final) :
    (∀ value, value ∈ values → Canonical value) ∧
      powerStateOK x final (start + count) := by
  exact statefulFromFnTrace_preserves (powerStateOK x) Canonical
    (by
      intro state index value next hstate hstep
      exact powerStep_preserves x index state value next hstate hstep)
    hinitial htrace

theorem powersRun_canonical {N : Usize}
    (x : CallbackWide) (count start : Nat) (initial final : PowerState N)
    (values : List CallbackWide)
    (hinitial : powerStateOK x initial start)
    (hrun : statefulFromFnRun powerStep count start initial = .ok (values, final)) :
    (∀ value, value ∈ values → Canonical value) ∧
      powerStateOK x final (start + count) := by
  have htrace := (statefulFromFnRun_success_iff_trace powerStep
    count start initial values final).mp hrun
  exact powersTrace_canonical x count start initial final values hinitial htrace

/-- Concrete result shape for the `N`-step `weights::powers` callback model. -/
theorem powersN_model_success {N : Usize} (x : CallbackWide)
    (values : List CallbackWide) (final : PowerState N)
    (hx : Canonical x)
    (hrun : statefulFromFnRun powerStep N.val 0
      (AspisR1CurrentPowers.field.WideExact.ONE, x) = .ok (values, final)) :
    values.length = N.val ∧ (∀ value, value ∈ values → Canonical value) ∧
      powerStateOK (N := N) x final N.val := by
  have htrace := (statefulFromFnRun_success_iff_trace powerStep
    N.val 0 (AspisR1CurrentPowers.field.WideExact.ONE, x) values final).mp hrun
  have hlength := statefulFromFnTrace_length htrace
  obtain ⟨hvalues, hfinal⟩ := powersTrace_canonical x N.val 0
    (AspisR1CurrentPowers.field.WideExact.ONE, x) final values
    (powers_initial_stateOK x hx) htrace
  exact ⟨hlength, hvalues, by simpa using hfinal⟩

/-- Canonical input makes every finite stateful powers model run succeed. -/
theorem powerRun_total_from_state {N : Usize} (x : CallbackWide) :
    ∀ (count start : Nat) (state : PowerState N),
      powerStateOK x state start →
      ∃ values final,
        statefulFromFnRun powerStep count start state = .ok (values, final) ∧
        (∀ value, value ∈ values → Canonical value) ∧
        powerStateOK x final (start + count) := by
  intro count
  induction count with
  | zero =>
      intro start state hstate
      exact ⟨[], state, by simp [statefulFromFnRun], by simp, hstate⟩
  | succ count ih =>
      intro start state hstate
      rcases hstate with ⟨hsx, hp, hx, hpower⟩
      have hstate' : powerStateOK x state start := ⟨hsx, hp, hx, hpower⟩
      obtain ⟨nextP, hnextCan, hnextPow, hcall⟩ :=
        AspisR1PowersExactProduct.powers_callback_total_exact
          state.1 state.2 hp hx 0#usize
      have hstep : powerStep state start = .ok (state.1, (nextP, state.2)) := by
        unfold powerStep
        exact hcall
      obtain ⟨hvalue, hnextState⟩ :=
        powerStep_preserves x start state state.1 (nextP, state.2) hstate' hstep
      obtain ⟨values, final, hrun, hall, hfinal⟩ :=
        ih (start + 1) (nextP, state.2) hnextState
      refine ⟨state.1 :: values, final, ?_, ?_, ?_⟩
      · simp [statefulFromFnRun, hstep, hrun]
      · intro value hv
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact hvalue
        · exact hall value hv
      · have hidx : start + 1 + count = start + (count + 1) := by omega
        rw [← hidx]
        exact hfinal

theorem powersN_model_total {N : Usize} (x : CallbackWide)
    (hx : Canonical x) :
    ∃ values final,
      statefulFromFnRun powerStep N.val 0
        (AspisR1CurrentPowers.field.WideExact.ONE, x) = .ok (values, final) ∧
      values.length = N.val ∧
      (∀ value, value ∈ values → Canonical value) ∧
      powerStateOK (N := N) x final N.val := by
  obtain ⟨values, final, hrun, hall, hfinal⟩ :=
    powerRun_total_from_state x N.val 0
      (AspisR1CurrentPowers.field.WideExact.ONE, x)
      (powers_initial_stateOK x hx)
  obtain ⟨hlen, hall', hfinal'⟩ := powersN_model_success x values final hx hrun
  exact ⟨values, final, hrun, hlen, hall, by simpa using hfinal⟩

#print axioms powerStep_preserves
#print axioms powersTrace_canonical
#print axioms powersRun_canonical
#print axioms one_canonical
#print axioms one_decode
#print axioms powers_initial_stateOK
#print axioms powersN_model_success
#print axioms powerRun_total_from_state
#print axioms powersN_model_total
#print axioms powerStep_eq_generatedFnMut
#print axioms generatedFnMut_eq_callOnce

end AspisR1S3PowersCanonicalTraceV1
