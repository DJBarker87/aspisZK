import S3ActualFieldOpsComplete
import CurrentWideMulM31V13
import PowersP6IndexedOutputV1
import S3PowersCanonicalTraceV1
import S4FromFnP6GeneratedInterface

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1S3PowersLowEntryCanonicalV1

open AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete
open AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete

/-- Scale in the shared, source-pinned current wide-field owner, then transport
back to the generated S3 field carrier. -/
def mulM31 (x : S) (s : AspisR1CurrentWide.field.M31) : Result S := do
  let z ← AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31 (toE x) s
  .ok (fromE z)

theorem mulM31_success_canonical (x z : S) (s : AspisR1CurrentWide.field.M31)
    (hx : Canonical x) (h : mulM31 x s = .ok z) : Canonical z := by
  unfold mulM31 at h
  cases hm : AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31 (toE x) s with
  | fail e => simp only [hm, bind_tc_fail] at h; cases h
  | div => simp only [hm, bind_tc_div] at h; cases h
  | ok y =>
      simp only [hm, bind_tc_ok] at h
      have hz : fromE y = z := Result.ok.inj h
      subst z
      have hwide := AspisR1CurrentWide.Proof.wide_mul_m31_success
        (toE x) y s hx hm
      simpa only [Canonical, to_from] using hwide.1

/-- The two products in the generated low-array callback, with its final
M31 scaling represented by the pinned current wide operation. -/
def lowEntry (x y : S) (s : AspisR1CurrentWide.field.M31) : Result S := do
  let product ← mul x y
  mulM31 product s

theorem lowEntry_success_canonical (x y z : S)
    (s : AspisR1CurrentWide.field.M31)
    (hx : Canonical x) (hy : Canonical y)
    (h : lowEntry x y s = .ok z) : Canonical z := by
  unfold lowEntry at h
  cases hm : mul x y with
  | fail e => simp only [hm, bind_tc_fail] at h; cases h
  | div => simp only [hm, bind_tc_div] at h; cases h
  | ok product =>
      simp only [hm, bind_tc_ok] at h
      obtain ⟨product', hp, hcan, _hdecode⟩ := mul_total_exact x y hx hy
      have heq : product' = product := Result.ok.inj (hp.symm.trans hm)
      subst product'
      exact mulM31_success_canonical product z s hcan h

/-- The powers carrier and S3 carrier share the same eight-coordinate wide
representation. This adapter transports canonicality without identifying the
nominal generated types. -/
def powerToS (x : AspisR1PowersConcreteMul.CallbackWide) : S :=
  fromE (AspisR1PowersExactProduct.toFull x)

theorem powerToS_canonical (x : AspisR1PowersConcreteMul.CallbackWide)
    (hx : AspisR1PowersConcreteMul.Canonical x) :
    Canonical (powerToS x) := by
  change AspisR1CurrentWide.Proof.CanonicalWide
    (toE (fromE (AspisR1PowersExactProduct.toFull x)))
  rw [to_from]
  have hx' : AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1PowersExactProduct.toFull x) := hx
  exact hx'

theorem selected_low_entry_success_canonical
    (x y : AspisR1PowersConcreteMul.CallbackWide) (z : S)
    (s : AspisR1CurrentWide.field.M31)
    (hx : AspisR1PowersConcreteMul.Canonical x)
    (hy : AspisR1PowersConcreteMul.Canonical y)
    (h : lowEntry (powerToS x) (powerToS y) s = .ok z) : Canonical z := by
  exact lowEntry_success_canonical (powerToS x) (powerToS y) z s
    (powerToS_canonical x hx) (powerToS_canonical y hy) h

abbrev LowInputs := List AspisR1PowersConcreteMul.CallbackWide ×
  List AspisR1PowersConcreteMul.CallbackWide

def callbackCanonical (xs : List AspisR1PowersConcreteMul.CallbackWide) : Prop :=
  ∀ i, i < 4 → ∃ x, xs[i]? = some x ∧ AspisR1PowersConcreteMul.Canonical x

def lowInputsCanonical (state : LowInputs) : Prop :=
  state.1.length = 4 ∧ state.2.length = 4 ∧
    callbackCanonical state.1 ∧ callbackCanonical state.2

def lowPerm (i : Nat) : Nat :=
  if i % 4 = 0 then 0 else if i % 4 = 1 then 3 else
  if i % 4 = 2 then 2 else 1

theorem lowPerm_lt4 (i : Nat) : lowPerm i < 4 := by
  unfold lowPerm
  split_ifs <;> omega

theorem list_getD_canonical {xs : List AspisR1PowersConcreteMul.CallbackWide}
    (hxs : callbackCanonical xs) (i : Nat) (hi : i < 4) :
    AspisR1PowersConcreteMul.Canonical
      (xs.getD i AspisR1CurrentPowers.field.WideExact.ONE) := by
  obtain ⟨x, hx, hcan⟩ := hxs i hi
  have hget : xs.getD i AspisR1CurrentPowers.field.WideExact.ONE = x := by
    simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]
  rw [hget]
  exact hcan

/-- One operational low-array callback step. The state is the two canonical
four-power lists; its output formula uses the source permutation `[0,3,2,1]`
on each axis. The actual Rust `from_fn` traversal remains a separate P6
standard-library boundary. -/
def lowStep (s : AspisR1CurrentWide.field.M31) (state : LowInputs) (_index : Nat) :
    Result (S × LowInputs) := do
  let x := state.1.getD (lowPerm (_index % 4))
    AspisR1CurrentPowers.field.WideExact.ONE
  let y := state.2.getD (lowPerm (_index / 4))
    AspisR1CurrentPowers.field.WideExact.ONE
  let value ← lowEntry (powerToS x) (powerToS y) s
  .ok (value, state)

theorem lowStep_success_preserves {s : AspisR1CurrentWide.field.M31}
    {state : LowInputs} {index : Nat} {value : S} {next : LowInputs}
    (hstate : lowInputsCanonical state)
    (hstep : lowStep s state index = .ok (value, next)) :
    Canonical value ∧ lowInputsCanonical next := by
  rcases hstate with ⟨hleftLen, hrightLen, hleftCan, hrightCan⟩
  unfold lowStep at hstep
  cases he : lowEntry
      (powerToS (state.1.getD (lowPerm (index % 4))
        AspisR1CurrentPowers.field.WideExact.ONE))
      (powerToS (state.2.getD (lowPerm (index / 4))
        AspisR1CurrentPowers.field.WideExact.ONE)) s with
  | fail e => simp only [he, bind_tc_fail] at hstep; cases hstep
  | div => simp only [he, bind_tc_div] at hstep; cases hstep
  | ok out =>
      simp only [he, bind_tc_ok] at hstep
      have hp := Result.ok.inj hstep
      rcases Prod.mk.inj hp with ⟨hout, hnext⟩
      subst value
      subst next
      apply And.intro
      · have hx : AspisR1PowersConcreteMul.Canonical
            (state.1.getD (lowPerm (index % 4))
              AspisR1CurrentPowers.field.WideExact.ONE) :=
          list_getD_canonical (xs := state.1) hleftCan
            (lowPerm (index % 4)) (lowPerm_lt4 (index % 4))
        have hy : AspisR1PowersConcreteMul.Canonical
            (state.2.getD (lowPerm (index / 4))
              AspisR1CurrentPowers.field.WideExact.ONE) :=
          list_getD_canonical (xs := state.2) hrightCan
            (lowPerm (index / 4)) (lowPerm_lt4 (index / 4))
        exact selected_low_entry_success_canonical
          (state.1.getD (lowPerm (index % 4)) AspisR1CurrentPowers.field.WideExact.ONE)
          (state.2.getD (lowPerm (index / 4)) AspisR1CurrentPowers.field.WideExact.ONE)
          out s hx hy he
      · exact ⟨hleftLen, hrightLen, hleftCan, hrightCan⟩

theorem lowRun_success_canonical {s : AspisR1CurrentWide.field.M31}
    (state : LowInputs) (values : List S) (final : LowInputs)
    (hstate : lowInputsCanonical state)
    (hrun : AspisR1FromFnP6.statefulFromFnRun (lowStep s) 16 0 state =
      .ok (values, final)) :
    (∀ value, value ∈ values → Canonical value) ∧ lowInputsCanonical final := by
  have htrace := (AspisR1FromFnP6.statefulFromFnRun_success_iff_trace
    (lowStep s) 16 0 state values final).mp hrun
  exact AspisR1FromFnP6.statefulFromFnTrace_preserves
    (fun st _ => lowInputsCanonical st) Canonical
    (by
      intro st i value next hs hstep
      exact lowStep_success_preserves hs hstep)
    hstate htrace

theorem powerList_callbackCanonical (x : AspisR1PowersConcreteMul.CallbackWide)
    (values : List AspisR1PowersConcreteMul.CallbackWide)
    (final : AspisR1S3PowersCanonicalTraceV1.PowerState (4#usize))
    (hx : AspisR1PowersConcreteMul.Canonical x)
    (hrun : AspisR1FromFnP6.statefulFromFnRun
      (AspisR1S3PowersCanonicalTraceV1.powerStep (N := 4#usize))
      (4#usize).val 0
      (AspisR1CurrentPowers.field.WideExact.ONE, x) = .ok (values, final)) :
    callbackCanonical values := by
  intro i hi
  have hfour : (4#usize).val = 4 := by decide
  have hi' : i < (4#usize).val := by simpa [hfour] using hi
  obtain ⟨value, hvalue, hcanonical, _hdecode⟩ :=
    AspisR1PowersP6IndexedOutputV1.powersN_model_success_indexed
      (N := 4#usize) x values final hx hrun i hi'
  exact ⟨value, hvalue, hcanonical⟩

theorem p6PowerPair_lowInputsCanonical
    (x0 x1 : AspisR1PowersConcreteMul.CallbackWide)
    (values0 values1 : List AspisR1PowersConcreteMul.CallbackWide)
    (final0 final1 : AspisR1S3PowersCanonicalTraceV1.PowerState (4#usize))
    (hx0 : AspisR1PowersConcreteMul.Canonical x0)
    (hx1 : AspisR1PowersConcreteMul.Canonical x1)
    (hrun0 : AspisR1FromFnP6.statefulFromFnRun
      (AspisR1S3PowersCanonicalTraceV1.powerStep (N := 4#usize))
      (4#usize).val 0
      (AspisR1CurrentPowers.field.WideExact.ONE, x0) = .ok (values0, final0))
    (hrun1 : AspisR1FromFnP6.statefulFromFnRun
      (AspisR1S3PowersCanonicalTraceV1.powerStep (N := 4#usize))
      (4#usize).val 0
      (AspisR1CurrentPowers.field.WideExact.ONE, x1) = .ok (values1, final1)) :
    lowInputsCanonical (values0, values1) := by
  have htrace0 := (AspisR1FromFnP6.statefulFromFnRun_success_iff_trace
    (AspisR1S3PowersCanonicalTraceV1.powerStep (N := 4#usize))
    (4#usize).val 0 (AspisR1CurrentPowers.field.WideExact.ONE, x0)
    values0 final0).mp hrun0
  have htrace1 := (AspisR1FromFnP6.statefulFromFnRun_success_iff_trace
    (AspisR1S3PowersCanonicalTraceV1.powerStep (N := 4#usize))
    (4#usize).val 0 (AspisR1CurrentPowers.field.WideExact.ONE, x1)
    values1 final1).mp hrun1
  have hlen0 := AspisR1FromFnP6.statefulFromFnTrace_length htrace0
  have hlen1 := AspisR1FromFnP6.statefulFromFnTrace_length htrace1
  have hfour : (4#usize).val = 4 := by decide
  constructor
  · simpa [hfour] using hlen0
  constructor
  · simpa [hfour] using hlen1
  exact ⟨powerList_callbackCanonical x0 values0 final0 hx0 hrun0,
    powerList_callbackCanonical x1 values1 final1 hx1 hrun1⟩

def generatedPowerCallback (N : Usize) :
    core.ops.function.FnMut
      (AspisR1CurrentPowers.weights.powers.closure N) Usize
      AspisR1CurrentPowers.field.WideExact := {
  FnOnceInst := {
    call_once := fun state i => do
      let (value, _) ← AspisR1S3PowersCanonicalTraceV1.powerFnMutCall state i
      .ok value
  }
  call_mut := AspisR1S3PowersCanonicalTraceV1.powerFnMutCall
}

def powerP6StateOK {N : Usize} (x : AspisR1PowersConcreteMul.CallbackWide)
    (state : AspisR1S3PowersCanonicalTraceV1.PowerState N × Usize)
    (_index : Nat) : Prop :=
  ∃ exponent : Nat,
    AspisR1S3PowersCanonicalTraceV1.powerStateOK x state.1 exponent

theorem powerP6FnMutStep_success_preserves {N : Usize}
    (x : AspisR1PowersConcreteMul.CallbackWide)
    (state : AspisR1S3PowersCanonicalTraceV1.PowerState N × Usize)
    (index : Nat) (value : AspisR1PowersConcreteMul.CallbackWide)
    (next : (AspisR1S3PowersCanonicalTraceV1.PowerState N × Usize))
    (hstate : powerP6StateOK x state index)
    (hstep : AspisR1FromFnP6Generated.fnMutStep
      (generatedPowerCallback N) state index = .ok (value,next)) :
    AspisR1PowersConcreteMul.Canonical value ∧
      powerP6StateOK x next (index + 1) := by
  rcases state with ⟨closureState, cursor⟩
  rcases closureState with ⟨p, base⟩
  obtain ⟨exponent, hpowerState⟩ := hstate
  rcases hpowerState with ⟨hbase, hp, hbaseCan, hpower⟩
  change base = x at hbase
  change AspisR1PowersConcreteMul.Canonical p at hp
  change AspisR1PowersConcreteMul.Canonical base at hbaseCan
  change AspisR1PowersExactProduct.decode p =
    AspisR1PowersExactProduct.decode x ^ exponent at hpower
  have hcallRaw :
      (generatedPowerCallback N).call_mut (p,base) cursor = .ok (value,next.1) := by
    unfold AspisR1FromFnP6Generated.fnMutStep at hstep
    cases hc : (generatedPowerCallback N).call_mut (p,base) cursor with
    | fail e => simp only [hc, bind_tc_fail] at hstep; cases hstep
    | div => simp only [hc, bind_tc_div] at hstep; cases hstep
    | ok pair =>
        rcases pair with ⟨v, closureNext⟩
        cases hadd : cursor + 1#usize with
        | fail e => simp only [hc, bind_tc_ok, hadd, bind_tc_fail] at hstep; cases hstep
        | div => simp only [hc, bind_tc_ok, hadd, bind_tc_div] at hstep; cases hstep
        | ok cursorNext =>
            simp only [hc, bind_tc_ok, hadd, bind_tc_ok] at hstep
            have hp := Result.ok.inj hstep
            rcases Prod.mk.inj hp with ⟨hv, hnext⟩
            cases hv
            cases hnext
            rfl
  have hmut : AspisR1S3PowersCanonicalTraceV1.powerFnMutCall
      (p,base) cursor = .ok (value,next.1) := by
    exact hcallRaw
  have honce : AspisR1CurrentPowers.weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once
        AspisR1PowersConcreteMul.sourceMul (p,base) cursor = .ok (value,next.1) := by
    have hmutEq := AspisR1S3PowersCanonicalTraceV1.generatedFnMut_eq_callOnce
      (N := N) (p,base) cursor
    exact hmutEq.symm.trans hmut
  have hpowerBase : AspisR1PowersExactProduct.decode p =
      AspisR1PowersExactProduct.decode base ^ exponent := by
    rw [hbase]
    exact hpower
  obtain ⟨hvalue, _hvalueDecode, hbaseNext, hnextCan, hnextPower⟩ :=
    AspisR1PowersExactProduct.powers_callback_success_power_invariant
      p base value next.1 hp hbaseCan cursor exponent hpowerBase honce
  refine ⟨?_, ?_⟩
  · simpa only [hvalue] using hp
  · refine ⟨exponent + 1, ?_⟩
    have hnextBase : next.1.2 = x := hbaseNext.trans hbase
    refine ⟨hnextBase, hnextCan, ?_, ?_⟩
    · have houterBaseCan : AspisR1PowersConcreteMul.Canonical x := by
        simpa only [hbase] using hbaseCan
      simpa only [hnextBase] using houterBaseCan
    · simpa only [hbase] using hnextPower

theorem p6_generated_powers_array_success_canonical {N : Usize}
    (x : AspisR1PowersConcreteMul.CallbackWide)
    (values : Aeneas.Std.Array AspisR1PowersConcreteMul.CallbackWide N)
    (final : AspisR1S3PowersCanonicalTraceV1.PowerState N × Usize)
    (hx : AspisR1PowersConcreteMul.Canonical x)
    (hrun : AspisR1FromFnP6Generated.core.array.from_fn_model N
      (generatedPowerCallback N)
      (AspisR1CurrentPowers.field.WideExact.ONE,x) = .ok (values,final)) :
    ∀ value, value ∈ values.val → AspisR1PowersConcreteMul.Canonical value := by
  have htrace := AspisR1FromFnP6Generated.core_array_from_fn_model_success_trace
    N (generatedPowerCallback N) (AspisR1CurrentPowers.field.WideExact.ONE,x) hrun
  have hinitial : powerP6StateOK (N := N) x
      ((AspisR1CurrentPowers.field.WideExact.ONE,x),0#usize) 0 := by
    exact ⟨0, AspisR1S3PowersCanonicalTraceV1.powers_initial_stateOK x hx⟩
  exact (AspisR1FromFnP6.statefulFromFnTrace_preserves
      (powerP6StateOK x) AspisR1PowersConcreteMul.Canonical
      (by
        intro state index value next hstate hstep
        exact powerP6FnMutStep_success_preserves x state index value next hstate hstep)
      hinitial htrace).1

#print axioms mulM31_success_canonical
#print axioms lowEntry_success_canonical
#print axioms powerToS_canonical
#print axioms selected_low_entry_success_canonical
#print axioms lowStep_success_preserves
#print axioms lowRun_success_canonical
#print axioms powerList_callbackCanonical
#print axioms p6PowerPair_lowInputsCanonical
#print axioms powerP6FnMutStep_success_preserves
#print axioms p6_generated_powers_array_success_canonical

end AspisR1S3PowersLowEntryCanonicalV1
