import S3PairLowCallOpsAdapterV1
import S3PairLowCallReadFactsV1
import S3PairLowCallPremisesV1
import S3PairLowCallProjectedStepRootV1
import S3PairLowCallClosurePreservationV1
import S3PowersLowTotalV1

open Aeneas Aeneas.Std Result WP
set_option autoImplicit false

namespace AspisR1PairLowCallCut

open AspisR1S3PowersLowEntryCanonicalV1
open AspisR1S3PowersLowActualCanonicalV1
open AspisR1S3PowersLowTotalV1
open AspisR1FromFnP6
open AspisR1FromFnP6Generated

private theorem actual_call_projection_of_bound
    (s : field.M31) (hscale : actualFieldOps.m31Mul weights.QUARTER weights.QUARTER = .ok s)
    (c : weights.s2_twofold_low_array.closure) (i : Usize) (hi : i.val < 16) :
    (do
      let (value, next) ←
        weights.s2_twofold_low_array.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
          actualFieldOps c i
      .ok (toActualS value, closureToLowInputs next)) =
      lowStep s (closureToLowInputs c) i.val := by
  obtain ⟨r,d,p,q,x,y,hmod,hdiv,hpermL,hpermR,hreadL,hreadR,
      hr,hd,hp,hq,hleft,hright⟩ := actual_pair_callback_reads c i hi
  exact projected_call_mut_eq_lowStep_of_reads c i r d p q x y s
    hmod hdiv hpermL hpermR hreadL hreadR hr hd hp hq hleft hright hscale

private theorem actual_step_of_model_step
    (s : field.M31)
    (hscale : actualFieldOps.m31Mul weights.QUARTER weights.QUARTER = .ok s)
    (c : weights.s2_twofold_low_array.closure) (state : AspisR1S3PowersLowEntryCanonicalV1.LowInputs)
    (cursor : Usize) (index : Nat)
    (value : ActualS) (nextState : AspisR1S3PowersLowEntryCanonicalV1.LowInputs) (nextCursor : Usize)
    (hrel : state = closureToLowInputs c)
    (hcursor : cursor.val = index) (hbound : index < 16)
    (hmodel : fnMutStep (generatedLowCallback s) (state,cursor) index =
      .ok (value,(nextState,nextCursor))) :
    ∃ raw nextClosure,
      fnMutStep
        (weights.s2_twofold_low_array.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
          actualFieldOps)
        (c,cursor) index = .ok (raw,(nextClosure,nextCursor)) ∧
      toActualS raw = value ∧ closureToLowInputs nextClosure = nextState ∧
      nextCursor.val = index + 1 := by
  unfold fnMutStep generatedLowCallback at hmodel
  cases hlow : lowStep s state cursor.val with
  | fail e => simp only [hlow, bind_tc_fail] at hmodel; cases hmodel
  | div => simp only [hlow, bind_tc_div] at hmodel; cases hmodel
  | ok pair =>
      rcases pair with ⟨modelValue, modelState⟩
      cases hinc : cursor + 1#usize with
      | fail e => simp only [hlow, bind_tc_ok, hinc, bind_tc_fail] at hmodel; cases hmodel
      | div => simp only [hlow, bind_tc_ok, hinc, bind_tc_div] at hmodel; cases hmodel
      | ok modelCursor =>
          simp only [hlow, bind_tc_ok, hinc, bind_tc_ok] at hmodel
          have hone : (1#usize).val = 1 := by decide
          have hmax : 16 ≤ Usize.max := by scalar_tac
          obtain ⟨cursorSpec,haddSpec,hvalSpec⟩ :=
            WP.spec_imp_exists
              (Usize.add_spec (x := cursor) (y := 1#usize)
                (by have haddbound : cursor.val + (1#usize).val ≤ Usize.max := by
                      rw [hone]; omega
                    exact haddbound))
          have hcursorEq : modelCursor = cursorSpec :=
            Result.ok.inj (hinc.symm.trans haddSpec)
          have hcursorValNext : modelCursor.val = index + 1 := by
            rw [hcursorEq,hvalSpec,hone,hcursor]
          have hp := Result.ok.inj hmodel
          rcases Prod.mk.inj hp with ⟨hv, hs⟩
          cases hv
          cases hs
          have hlowSource : lowStep s (closureToLowInputs c) cursor.val =
              .ok (value,nextState) := by
            rw [← hrel]
            exact hlow
          have hproj := actual_call_projection_of_bound s hscale
            c cursor (by rw [hcursor]; exact hbound)
          cases hcall :
              weights.s2_twofold_low_array.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
                actualFieldOps c cursor with
          | fail e =>
              have hproj' := hproj
              simp only [hcall, bind_tc_fail] at hproj'
              rw [hlowSource] at hproj'
              cases hproj'
          | div =>
              have hproj' := hproj
              simp only [hcall, bind_tc_div] at hproj'
              rw [hlowSource] at hproj'
              cases hproj'
          | ok pair =>
              rcases pair with ⟨raw,nextClosure⟩
              have hproj' := hproj
              simp only [hcall, bind_tc_ok] at hproj'
              rw [hlowSource] at hproj'
              have hout := Result.ok.inj hproj'
              rcases Prod.mk.inj hout with ⟨hraw,hstate⟩
              refine ⟨raw,nextClosure,?_,hraw,hstate,hcursorValNext⟩
              change (do
                let (v, next) ←
                  weights.s2_twofold_low_array.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
                    actualFieldOps c cursor
                let i' ← cursor + 1#usize
                .ok (v,(next,i'))) = .ok (raw,(nextClosure,nextCursor))
              rw [hcall,hinc]
              rfl

private theorem lift_low_fnMut_trace
    (s : field.M31)
    (hscale : actualFieldOps.m31Mul weights.QUARTER weights.QUARTER = .ok s)
    {count start : Nat} {state final : AspisR1S3PowersLowEntryCanonicalV1.LowInputs × Usize}
    {modelValues : List ActualS}
    (htrace : StatefulFromFnTrace (fnMutStep (generatedLowCallback s))
      count start state modelValues final) :
    ∀ (c : weights.s2_twofold_low_array.closure) (cursor : Usize),
      state.1 = closureToLowInputs c → state.2 = cursor → cursor.val = start →
      start + count ≤ 16 →
      ∃ (actualValues : List field.WideExact)
        (actualFinal : weights.s2_twofold_low_array.closure × Usize),
        StatefulFromFnTrace
          (fnMutStep
            (weights.s2_twofold_low_array.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
              actualFieldOps))
          count start (c,cursor) actualValues actualFinal ∧
        actualValues.map toActualS = modelValues ∧
        closureToLowInputs actualFinal.1 = final.1 ∧
        actualFinal.2 = final.2 ∧
        actualFinal.2.val = start + count := by
  induction htrace with
  | done start state =>
      intro c cursor hstate hcursor hcursorVal hbound
      cases state with
      | mk inputState modelCursor =>
        have hstate' : inputState = closureToLowInputs c := hstate
        have hcursor' : modelCursor = cursor := hcursor
        subst inputState
        subst modelCursor
        exact ⟨[],(c,cursor),.done start (c,cursor),by rfl,rfl,rfl,hcursorVal⟩
  | @call count start state nextState final modelValue modelValues hstep htail ih =>
      intro c cursor hstate hcursor hcursorVal hbound
      cases state with
      | mk inputState modelCursor =>
        cases nextState with
        | mk inputNext modelCursorNext =>
          have hindex : start < 16 := by omega
          have hmodelStep : fnMutStep (generatedLowCallback s)
              (inputState,modelCursor) start =
                .ok (modelValue,(inputNext,modelCursorNext)) := hstep
          have hmodelCursor : modelCursor = cursor := hcursor
          subst modelCursor
          have hsrc := actual_step_of_model_step s hscale c inputState cursor start
              modelValue inputNext modelCursorNext hstate hcursorVal hindex hmodelStep
          obtain ⟨actualValue,nextClosure,hactualStep,hvalue,hnextState,hnextVal⟩ := hsrc
          have htailState : inputNext = closureToLowInputs nextClosure := hnextState.symm
          obtain ⟨tailValues,tailFinal,htailActual,hmapTail,hfinalState,hfinalCursor,hfinalVal⟩ :=
            ih nextClosure modelCursorNext htailState (by rfl)
              hnextVal (by omega)
          refine ⟨actualValue::tailValues,tailFinal,.call hactualStep htailActual,?_,hfinalState,hfinalCursor,?_⟩
          simp only [List.map_cons, hvalue, hmapTail]
          omega

theorem actual_pair_low_array_total
    (c : weights.s2_twofold_low_array.closure)
    (hinputs : lowInputsCanonical (closureToLowInputs c)) :
    ∃ (s : field.M31)
      (actual : Aeneas.Std.Array field.WideExact (16#usize))
      (actualFinal : weights.s2_twofold_low_array.closure × Usize)
      (model : Aeneas.Std.Array ActualS (16#usize))
      (modelFinal : AspisR1S3PowersLowEntryCanonicalV1.LowInputs × Usize),
      actualFieldOps.m31Mul weights.QUARTER weights.QUARTER = .ok s ∧
      weights.s2_twofold_low_array_model actualFieldOps c.1 c.2 =
        .ok (actual,actualFinal) ∧
      core.array.from_fn_model (16#usize) (generatedLowCallback s) (closureToLowInputs c) =
        .ok (model,modelFinal) ∧
      actual.val.map toActualS = model.val ∧
      actualFinal.1 = c ∧
      actualFinal.2.val = (16#usize).val := by
  obtain ⟨s,hscale,_hval,_hbound⟩ := actual_quarter_squared_result
  obtain ⟨model,modelFinal,hmodel⟩ := generated_low_array_total s
    (closureToLowInputs c) hinputs
  have hlowTrace := core_array_from_fn_model_success_trace
    (16#usize) (generatedLowCallback s) (closureToLowInputs c) hmodel
  have hN : (16#usize).val = 16 := by decide
  have hbound : 0 + (16#usize).val ≤ 16 := by simp [hN]
  obtain ⟨actualValues,actualFinal,hactualTrace,hmap,_hfinalState,_hfinalCursor,hcursorFinal⟩ :=
    lift_low_fnMut_trace s hscale hlowTrace c (0#usize) rfl rfl (by decide) hbound
  have hrun := (statefulFromFnRun_success_iff_trace
    (fnMutStep
      (weights.s2_twofold_low_array.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        actualFieldOps))
    (16#usize).val 0 (c,0#usize) actualValues actualFinal).mpr hactualTrace
  have hlen := statefulFromFnTrace_length hactualTrace
  have hlenU : actualValues.length = (16#usize).val := by simpa [hN] using hlen
  have htraceRun : core.array.from_fn_trace_model (16#usize)
      (weights.s2_twofold_low_array.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        actualFieldOps) c = .ok (actualValues,actualFinal) := by
    simpa only [core.array.from_fn_trace_model] using hrun
  let actualArray : Aeneas.Std.Array field.WideExact (16#usize) :=
    ⟨actualValues,hlenU⟩
  have hactual : weights.s2_twofold_low_array_model actualFieldOps c.1 c.2 =
      .ok (actualArray,actualFinal) := by
    cases c with
    | mk ap0 ap1 =>
      unfold weights.s2_twofold_low_array_model
      change packArrayState (16#usize)
        (core.array.from_fn_trace_model (16#usize)
          (weights.s2_twofold_low_array.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
            actualFieldOps) (ap0,ap1)) = .ok (actualArray,actualFinal)
      rw [htraceRun]
      simp only [packArrayState, dif_pos hlenU]
      rfl
  have hmodelEq : core.array.from_fn_model (16#usize) (generatedLowCallback s)
      (closureToLowInputs c) = .ok (model,modelFinal) := hmodel
  have hclosure := actual_low_array_success_preserves_closure actualFieldOps c hactual
  exact ⟨s,actualArray,actualFinal,model,modelFinal,hscale,hactual,hmodelEq,hmap,hclosure,hcursorFinal⟩

#print axioms actual_pair_low_array_total

end AspisR1PairLowCallCut
