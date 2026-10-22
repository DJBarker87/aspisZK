import S3PowersLowActualCanonicalV1
import PowersP6GeneratedTotalV1
import CurrentWideMulM31V13
import CurrentWideQMMulM31V5

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1S3PowersLowTotalV1

open AspisR1S3PowersLowActualCanonicalV1
open AspisR1S3PowersLowEntryCanonicalV1
open AspisR1S3PowersCanonicalTraceV1
open AspisR1PowersP6GeneratedTotalV1
open AspisR1FromFnP6 AspisR1FromFnP6Generated

/-- For canonical bases, the exact generated FnMut callback has a successful
P6 array run. This lifts the existing total `powerStep` trace through the
checked generated callback ABI and does not assume a successful array run. -/
theorem generated_power_array_total {N : Usize}
    (x : AspisR1PowersConcreteMul.CallbackWide)
    (hx : AspisR1PowersConcreteMul.Canonical x) :
    ∃ values final,
      core.array.from_fn_model N (generatedPowerCallback N)
        (AspisR1CurrentPowers.field.WideExact.ONE, x) = .ok (values, final) := by
  obtain ⟨items, powerFinal, hrun, hlen, _hall, _hfinal⟩ :=
    powersN_model_total (N := N) x hx
  have hbase := (statefulFromFnRun_success_iff_trace powerStep N.val 0
    (AspisR1CurrentPowers.field.WideExact.ONE, x) items powerFinal).mp hrun
  have hbound : 0 + N.val ≤ Usize.max := by scalar_tac
  obtain ⟨cursor, htrace⟩ := generated_trace_lifts
    (generatedPowerCallback N) (by intro state i; rfl)
    hbase (0#usize) rfl hbound
  have hrunGenerated := (statefulFromFnRun_success_iff_trace
    (fnMutStep (generatedPowerCallback N)) N.val 0
    ((AspisR1CurrentPowers.field.WideExact.ONE, x), 0#usize)
    items (powerFinal, cursor)).mpr htrace
  have htraceRun : core.array.from_fn_trace_model N (generatedPowerCallback N)
      (AspisR1CurrentPowers.field.WideExact.ONE, x) =
      .ok (items, (powerFinal, cursor)) := by
    simpa only [core.array.from_fn_trace_model] using hrunGenerated
  let arr : Array AspisR1PowersConcreteMul.CallbackWide N := ⟨items, hlen⟩
  have hmodel : core.array.from_fn_model N (generatedPowerCallback N)
      (AspisR1CurrentPowers.field.WideExact.ONE, x) = .ok (arr, (powerFinal, cursor)) := by
    unfold core.array.from_fn_model
    simp only [htraceRun, packArrayState, dif_pos hlen]
    rfl
  exact ⟨arr, (powerFinal, cursor), hmodel⟩

private theorem qm_mul_m31_total (x : AspisR1CurrentWide.field.QM31)
    (s : AspisR1CurrentWide.field.M31) :
    ∃ z, AspisR1CurrentWide.field.QM31.mul_m31 x s = .ok z := by
  let old := AspisR1CurrentWide.Proof.toQM x
  obtain ⟨a,ha,_,_⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod old.c0.a s
  obtain ⟨b,hb,_,_⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod old.c0.b s
  obtain ⟨c,hc,_,_⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod old.c1.a s
  obtain ⟨d,hd,_,_⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod old.c1.b s
  let out : AspisR1CurrentWide.field.QM31 := ⟨⟨a,b⟩,⟨c,d⟩⟩
  have haNew : AspisR1CurrentWide.field.M31.mul x.c0.a s = .ok a := by
    rw [AspisR1CurrentWide.Proof.m31_mul_same]
    exact ha
  have hbNew : AspisR1CurrentWide.field.M31.mul x.c0.b s = .ok b := by
    rw [AspisR1CurrentWide.Proof.m31_mul_same]
    exact hb
  have hcNew : AspisR1CurrentWide.field.M31.mul x.c1.a s = .ok c := by
    rw [AspisR1CurrentWide.Proof.m31_mul_same]
    exact hc
  have hdNew : AspisR1CurrentWide.field.M31.mul x.c1.b s = .ok d := by
    rw [AspisR1CurrentWide.Proof.m31_mul_same]
    exact hd
  refine ⟨out, ?_⟩
  simp [AspisR1CurrentWide.field.QM31.mul_m31,
    AspisR1CurrentWide.field.CM31.mul_m31, haNew, hbNew, hcNew, hdNew]
  rfl

theorem wide_mul_m31_total (x : AspisR1CurrentWide.field.wide_exact.WideExact)
    (s : AspisR1CurrentWide.field.M31) :
    ∃ z, AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31 x s = .ok z := by
  have hden : AspisR1CurrentWide.field.P.val ≠ 0 := by
    norm_num [AspisR1CurrentWide.field.P]
  obtain ⟨i,hi,_hival⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (UScalar.rem_spec s hden)
  obtain ⟨q,hq⟩ := qm_mul_m31_total x.c0 i
  obtain ⟨q1,hq1⟩ := qm_mul_m31_total x.c1 i
  refine ⟨⟨q,q1⟩, ?_⟩
  unfold AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31
  simp [hi,hq,hq1]

theorem low_m31_total (x : AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.S)
    (s : AspisR1CurrentWide.field.M31) :
    ∃ z, AspisR1S3PowersLowEntryCanonicalV1.mulM31 x s = .ok z := by
  obtain ⟨out,hout⟩ := wide_mul_m31_total
    (AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.toE x) s
  refine ⟨AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.fromE out, ?_⟩
  unfold AspisR1S3PowersLowEntryCanonicalV1.mulM31
  rw [hout]
  rfl

theorem low_entry_total
    (x y : AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.S)
    (s : AspisR1CurrentWide.field.M31)
    (hx : AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.Canonical x)
    (hy : AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.Canonical y) :
    ∃ z, AspisR1S3PowersLowEntryCanonicalV1.lowEntry x y s = .ok z := by
  obtain ⟨product,hproduct,hcan,_hvalue⟩ :=
    AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.mul_total_exact x y hx hy
  obtain ⟨z,hz⟩ := low_m31_total product s
  refine ⟨z, ?_⟩
  change (do
    let product ← (AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.mul x y)
    AspisR1S3PowersLowEntryCanonicalV1.mulM31 product s) = .ok z
  rw [hproduct]
  simp only [bind_tc_ok, hz]


theorem low_step_total
    (s : AspisR1CurrentWide.field.M31)
    (state : AspisR1S3PowersLowEntryCanonicalV1.LowInputs)
    (index : Nat)
    (hstate : AspisR1S3PowersLowEntryCanonicalV1.lowInputsCanonical state) :
    ∃ value, AspisR1S3PowersLowEntryCanonicalV1.lowStep s state index =
      .ok (value, state) := by
  rcases hstate with ⟨_hlen0,_hlen1,hcan0,hcan1⟩
  let ix := AspisR1S3PowersLowEntryCanonicalV1.lowPerm (index % 4)
  let iy := AspisR1S3PowersLowEntryCanonicalV1.lowPerm (index / 4)
  have hx : AspisR1PowersConcreteMul.Canonical
      (state.1.getD ix AspisR1CurrentPowers.field.WideExact.ONE) :=
    AspisR1S3PowersLowEntryCanonicalV1.list_getD_canonical hcan0 ix
      (AspisR1S3PowersLowEntryCanonicalV1.lowPerm_lt4 (index % 4))
  have hy : AspisR1PowersConcreteMul.Canonical
      (state.2.getD iy AspisR1CurrentPowers.field.WideExact.ONE) :=
    AspisR1S3PowersLowEntryCanonicalV1.list_getD_canonical hcan1 iy
      (AspisR1S3PowersLowEntryCanonicalV1.lowPerm_lt4 (index / 4))
  obtain ⟨value,hvalue⟩ := low_entry_total
    (AspisR1S3PowersLowEntryCanonicalV1.powerToS
      (state.1.getD ix AspisR1CurrentPowers.field.WideExact.ONE))
    (AspisR1S3PowersLowEntryCanonicalV1.powerToS
      (state.2.getD iy AspisR1CurrentPowers.field.WideExact.ONE)) s
    (AspisR1S3PowersLowEntryCanonicalV1.powerToS_canonical _ hx)
    (AspisR1S3PowersLowEntryCanonicalV1.powerToS_canonical _ hy)
  refine ⟨value,?_⟩
  change (do
    let value ← AspisR1S3PowersLowEntryCanonicalV1.lowEntry
      (AspisR1S3PowersLowEntryCanonicalV1.powerToS
        (state.1.getD ix AspisR1CurrentPowers.field.WideExact.ONE))
      (AspisR1S3PowersLowEntryCanonicalV1.powerToS
        (state.2.getD iy AspisR1CurrentPowers.field.WideExact.ONE)) s
    .ok (value,state)) = .ok (value,state)
  rw [hvalue]
  simp only [bind_tc_ok]

private theorem low_trace_total
    (s : AspisR1CurrentWide.field.M31) :
    ∀ (count start : Nat) (state : AspisR1S3PowersLowEntryCanonicalV1.LowInputs),
      AspisR1S3PowersLowEntryCanonicalV1.lowInputsCanonical state →
      ∃ values final,
        AspisR1FromFnP6.StatefulFromFnTrace
          (AspisR1S3PowersLowEntryCanonicalV1.lowStep s)
          count start state values final ∧
        (∀ value, value ∈ values →
          AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.Canonical value) ∧
        AspisR1S3PowersLowEntryCanonicalV1.lowInputsCanonical final := by
  intro count
  induction count with
  | zero =>
      intro start state hstate
      exact ⟨[],state,.done start state,by simp,hstate⟩
  | succ count ih =>
      intro start state hstate
      obtain ⟨value,hstep⟩ := low_step_total s state start hstate
      obtain ⟨values,final,htrace,hvalues,hfinal⟩ := ih (start+1) state hstate
      refine ⟨value::values,final,.call hstep htrace,?_,hfinal⟩
      intro v hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact (AspisR1S3PowersLowEntryCanonicalV1.lowStep_success_preserves
          hstate hstep).1
      · exact hvalues v hv

theorem generated_low_trace_lifts
    (s : AspisR1CurrentWide.field.M31)
    {count start : Nat}
    {initial final : AspisR1S3PowersLowEntryCanonicalV1.LowInputs}
    {values : List AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.S}
    (htrace : AspisR1FromFnP6.StatefulFromFnTrace
      (AspisR1S3PowersLowEntryCanonicalV1.lowStep s)
      count start initial values final) :
    ∀ cursor : Usize, cursor.val=start → start+count ≤ Usize.max →
      ∃ finalCursor,
        AspisR1FromFnP6.StatefulFromFnTrace
          (AspisR1FromFnP6Generated.fnMutStep
            (AspisR1S3PowersLowActualCanonicalV1.generatedLowCallback s))
          count start (initial,cursor) values (final,finalCursor) := by
  induction htrace with
  | done start state =>
      intro cursor hcursor _
      have hstart : start = cursor.val := hcursor.symm
      subst start
      have hdone : AspisR1FromFnP6.StatefulFromFnTrace
          (AspisR1FromFnP6Generated.fnMutStep
            (AspisR1S3PowersLowActualCanonicalV1.generatedLowCallback s))
          0 cursor.val (state,cursor) [] (state,cursor) :=
        .done cursor.val (state,cursor)
      exact ⟨cursor,hdone⟩
  | @call count start state state' final value values hstep htail ih =>
      intro cursor hcursor hbound
      have hone : (1#usize).val=1 := by decide
      obtain ⟨cursor',hnext,hnextval⟩ :=
        Aeneas.Std.WP.spec_imp_exists
          (Usize.add_spec (x := cursor) (y := 1#usize) (by rw [hone]; omega))
      have hc' : cursor'.val=start+1 := by rw [hone] at hnextval; omega
      have hgen : AspisR1FromFnP6Generated.fnMutStep
          (AspisR1S3PowersLowActualCanonicalV1.generatedLowCallback s)
          (state,cursor) start = .ok (value,(state',cursor')) := by
        unfold AspisR1FromFnP6Generated.fnMutStep
          AspisR1S3PowersLowActualCanonicalV1.generatedLowCallback
        simp only [hcursor,hstep,hnext]
        rfl
      obtain ⟨finalCursor,hfinal⟩ := ih cursor' hc' (by omega)
      exact ⟨finalCursor,.call hgen hfinal⟩

theorem generated_low_array_total
    (s : AspisR1CurrentWide.field.M31)
    (inputs : AspisR1S3PowersLowEntryCanonicalV1.LowInputs)
    (hinputs : AspisR1S3PowersLowEntryCanonicalV1.lowInputsCanonical inputs) :
    ∃ values final,
      core.array.from_fn_model (16#usize)
        (AspisR1S3PowersLowActualCanonicalV1.generatedLowCallback s) inputs =
        .ok (values,final) := by
  obtain ⟨items,final,htrace,_hvalues,hfinal⟩ := low_trace_total s 16 0 inputs hinputs
  have hbound : 0+16 ≤ Usize.max := by scalar_tac
  obtain ⟨cursor,hgenerated⟩ := generated_low_trace_lifts s htrace
    (0#usize) (by decide) hbound
  have hrun := (AspisR1FromFnP6.statefulFromFnRun_success_iff_trace
    (AspisR1FromFnP6Generated.fnMutStep
      (AspisR1S3PowersLowActualCanonicalV1.generatedLowCallback s))
    16 0 (inputs,0#usize) items (final,cursor)).mpr hgenerated
  have hlen : items.length=16 :=
    AspisR1FromFnP6.statefulFromFnTrace_length hgenerated
  have hN : (16#usize).val=16 := by decide
  have htraceRun : core.array.from_fn_trace_model (16#usize)
      (AspisR1S3PowersLowActualCanonicalV1.generatedLowCallback s) inputs =
      .ok (items,(final,cursor)) := by
    simpa only [core.array.from_fn_trace_model,hN] using hrun
  have hlenU : items.length=(16#usize).val := by simpa using hlen
  let arr : Array AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.S
      (16#usize) := ⟨items,hlenU⟩
  have hmodel : core.array.from_fn_model (16#usize)
      (AspisR1S3PowersLowActualCanonicalV1.generatedLowCallback s) inputs =
      .ok (arr,(final,cursor)) := by
    unfold core.array.from_fn_model
    simp only [htraceRun,AspisR1FromFnP6Generated.packArrayState,dif_pos hlenU]
    rfl
  exact ⟨arr,(final,cursor),hmodel⟩


theorem p6_total_canonical_low
    (x0 x1 : AspisR1PowersConcreteMul.CallbackWide)
    (hx0 : AspisR1PowersConcreteMul.Canonical x0)
    (hx1 : AspisR1PowersConcreteMul.Canonical x1)
    (s : AspisR1CurrentWide.field.M31) :
    ∃ (powers0 powers1 : Aeneas.Std.Array AspisR1PowersConcreteMul.CallbackWide (4#usize))
      (low : Aeneas.Std.Array AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.S (16#usize))
      (powerFinal0 powerFinal1 : AspisR1S3PowersCanonicalTraceV1.PowerState (4#usize) × Usize)
      (lowFinal : AspisR1S3PowersLowEntryCanonicalV1.LowInputs × Usize),
      core.array.from_fn_model (4#usize) (generatedPowerCallback (4#usize))
        (AspisR1CurrentPowers.field.WideExact.ONE,x0) = .ok (powers0,powerFinal0) ∧
      core.array.from_fn_model (4#usize) (generatedPowerCallback (4#usize))
        (AspisR1CurrentPowers.field.WideExact.ONE,x1) = .ok (powers1,powerFinal1) ∧
      core.array.from_fn_model (16#usize)
        (AspisR1S3PowersLowActualCanonicalV1.generatedLowCallback s)
        (powers0.val,powers1.val) = .ok (low,lowFinal) ∧
      AspisR1GroupedPairActualFieldOpsV3.ActualLoop1.CanonicalLow low := by
  obtain ⟨powers0,powerFinal0,hrun0⟩ := generated_power_array_total
    (N := 4#usize) x0 hx0
  obtain ⟨powers1,powerFinal1,hrun1⟩ := generated_power_array_total
    (N := 4#usize) x1 hx1
  have hcan0 := AspisR1S3PowersLowEntryCanonicalV1.p6_generated_powers_array_success_canonical
    x0 powers0 powerFinal0 hx0 hrun0
  have hcan1 := AspisR1S3PowersLowEntryCanonicalV1.p6_generated_powers_array_success_canonical
    x1 powers1 powerFinal1 hx1 hrun1
  have htrace0 := AspisR1FromFnP6Generated.core_array_from_fn_model_success_trace
    (4#usize) (generatedPowerCallback (4#usize))
    (AspisR1CurrentPowers.field.WideExact.ONE,x0) hrun0
  have htrace1 := AspisR1FromFnP6Generated.core_array_from_fn_model_success_trace
    (4#usize) (generatedPowerCallback (4#usize))
    (AspisR1CurrentPowers.field.WideExact.ONE,x1) hrun1
  have hlen0 : powers0.val.length=4 := by
    have h := AspisR1FromFnP6.statefulFromFnTrace_length htrace0
    have hn : (4#usize).val=4 := by decide
    simpa [hn] using h
  have hlen1 : powers1.val.length=4 := by
    have h := AspisR1FromFnP6.statefulFromFnTrace_length htrace1
    have hn : (4#usize).val=4 := by decide
    simpa [hn] using h
  have hlist0 : AspisR1S3PowersLowEntryCanonicalV1.callbackCanonical powers0.val := by
    intro i hi
    have hi' : i<powers0.val.length := by omega
    let value := powers0.val[i]'hi'
    have hmem : value ∈ powers0.val := List.getElem_mem (l := powers0.val) (n := i) hi'
    exact ⟨value,List.getElem?_eq_getElem hi',hcan0 value hmem⟩
  have hlist1 : AspisR1S3PowersLowEntryCanonicalV1.callbackCanonical powers1.val := by
    intro i hi
    have hi' : i<powers1.val.length := by omega
    let value := powers1.val[i]'hi'
    have hmem : value ∈ powers1.val := List.getElem_mem (l := powers1.val) (n := i) hi'
    exact ⟨value,List.getElem?_eq_getElem hi',hcan1 value hmem⟩
  have hinputs : AspisR1S3PowersLowEntryCanonicalV1.lowInputsCanonical
      (powers0.val,powers1.val) := ⟨hlen0,hlen1,hlist0,hlist1⟩
  obtain ⟨low,lowFinal,hlow⟩ := generated_low_array_total s
    (powers0.val,powers1.val) hinputs
  have hcanonical := AspisR1S3PowersLowActualCanonicalV1.p6_generated_power_arrays_to_canonical_low
    x0 x1 powers0 powers1 powerFinal0 powerFinal1 s low lowFinal hx0 hx1 hrun0 hrun1 hlow
  exact ⟨powers0,powers1,low,powerFinal0,powerFinal1,lowFinal,
    hrun0,hrun1,hlow,hcanonical⟩

#print axioms generated_power_array_total
#print axioms wide_mul_m31_total
#print axioms low_entry_total
#print axioms low_step_total
#print axioms generated_low_trace_lifts
#print axioms generated_low_array_total
#print axioms p6_total_canonical_low

end AspisR1S3PowersLowTotalV1
