import S9HighTermsOneCallV2
import S9HighTermsStepLemmaV1
import S4FromFnP6GeneratedInterface
import S4FromFnP6GeneratedTrace

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1S9HighTermsTraceV1

open AspisR1S9HelperP6
open AspisR1S9HighTermsConcreteV1
open AspisR1FromFnP6Generated

local instance traceOps : AspisR1S9HelperP6.FieldOps :=
  AspisR1S9ConcreteFieldOpsV1.concreteFieldOps

abbrev W := AspisR1S9HelperP6.field.WideExact
abbrev Q := AspisR1S9HelperP6.field.QM31
abbrev Callback := weights.factored_s2_libra_weights.closure
abbrev CallbackFn :=
  weights.factored_s2_libra_weights.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
abbrev canonicalW (x : W) : Prop :=
  AspisR1CurrentWide.Proof.CanonicalWide
    (AspisR1S9GeneratedWideMulQM31V2.toWide x)
abbrev canonicalQ (x : Q) : Prop :=
  AspisR1CurrentWide.Proof.CanonicalQM
    (AspisR1S9GeneratedWideMulQM31V2.toQM x)
abbrev decW (x : W) : AspisWideTower.WideExact :=
  AspisR1CurrentWide.Proof.decodeWide
    (AspisR1S9GeneratedWideMulQM31V2.toWide x)
abbrev decQ (x : Q) : AspisR1S9HelperP6PowerSemanticsV1.ExactQM :=
  AspisR1CurrentWide.Proof.decodeQM
    (AspisR1S9GeneratedWideMulQM31V2.toQM x)


private theorem add_zero_one :
    ∃ c : Usize, (0#usize + 1#usize : Result Usize) = .ok c ∧ c = 1#usize := by
  obtain ⟨c, hc, hv⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := 0#usize) (y := 1#usize) (by scalar_tac))
  refine ⟨c, hc, ?_⟩
  apply UScalar.eq_of_val_eq
  simpa using hv

private theorem add_one_two :
    ∃ c : Usize, (1#usize + 1#usize : Result Usize) = .ok c ∧ c = 2#usize := by
  obtain ⟨c, hc, hv⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := 1#usize) (y := 1#usize) (by scalar_tac))
  refine ⟨c, hc, ?_⟩
  apply UScalar.eq_of_val_eq
  simpa using hv

private theorem add_two_three :
    ∃ c : Usize, (2#usize + 1#usize : Result Usize) = .ok c ∧ c = 3#usize := by
  obtain ⟨c, hc, hv⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := 2#usize) (y := 1#usize) (by scalar_tac))
  refine ⟨c, hc, ?_⟩
  apply UScalar.eq_of_val_eq
  simpa using hv

private theorem add_three_four :
    ∃ c : Usize, (3#usize + 1#usize : Result Usize) = .ok c ∧ c = 4#usize := by
  obtain ⟨c, hc, hv⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := 3#usize) (y := 1#usize) (by scalar_tac))
  refine ⟨c, hc, ?_⟩
  apply UScalar.eq_of_val_eq
  simpa using hv

abbrev HighTermCall := AspisR1S9HighTermsConcreteV1.HighTermCall

/-- Four ordered callback calls and the exact stateful P6/from_fn result. -/
structure HighTermsFour (ap1 : Array W (4#usize)) (high : Array Q (4#usize)) where
  call0 : HighTermCall ap1 high 0#usize
  call1 : HighTermCall ap1 high 1#usize
  call2 : HighTermCall ap1 high 2#usize
  call3 : HighTermCall ap1 high 3#usize
  terms : Array W (4#usize)
  terms_values : terms.val = [call0.term, call1.term, call2.term, call3.term]
  trace_model : core.array.from_fn_trace_model (4#usize) CallbackFn (ap1,high) =
    .ok ([call0.term, call1.term, call2.term, call3.term],((ap1,high),4#usize))
  generated_from_fn : @AspisR1S9HelperP6.core.array.from_fn W Callback
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (4#usize) CallbackFn (ap1,high) =
      .ok (terms,((ap1,high),4#usize))

/-- The generated N=4 high-term FnMut callback has four ordered successful
calls on one unchanged captured closure. Their outputs construct the exact
selected P6 `from_fn` model array; per-term meaning is retained for the
factored helper side body. This does not assert Rust std-library refinement. -/
theorem high_terms4_from_fn_p6
    (ap1 : Array W (4#usize)) (high : Array Q (4#usize))
    (hap1 : ∀ (j : Usize) (x : W), Array.index_usize ap1 j = .ok x → canonicalW x)
    (hhigh : ∀ (j : Usize) (q : Q), Array.index_usize high j = .ok q → canonicalQ q) :
    Nonempty (HighTermsFour ap1 high) := by
  obtain ⟨call0⟩ := AspisR1S9HighTermsConcreteV1.one_call_record ap1 high 0#usize (by decide) hap1 hhigh
  obtain ⟨call1⟩ := AspisR1S9HighTermsConcreteV1.one_call_record ap1 high 1#usize (by decide) hap1 hhigh
  obtain ⟨call2⟩ := AspisR1S9HighTermsConcreteV1.one_call_record ap1 high 2#usize (by decide) hap1 hhigh
  obtain ⟨call3⟩ := AspisR1S9HighTermsConcreteV1.one_call_record ap1 high 3#usize (by decide) hap1 hhigh
  let t0 := call0.term
  let t1 := call1.term
  let t2 := call2.term
  let t3 := call3.term
  obtain ⟨c1,hadd0,hc1eq⟩ := add_zero_one
  obtain ⟨c2,hadd1,hc2eq⟩ := add_one_two
  obtain ⟨c3,hadd2,hc3eq⟩ := add_two_three
  obtain ⟨c4,hadd3,hc4eq⟩ := add_three_four
  have hc0 := call0.callback_success
  have hc1 := call1.callback_success
  have hc2 := call2.callback_success
  have hc3 := call3.callback_success
  have hc1at : CallbackFn.call_mut (ap1,high) c1 = .ok (t1,(ap1,high)) := by
    simpa only [hc1eq] using hc1
  have hc2at : CallbackFn.call_mut (ap1,high) c2 = .ok (t2,(ap1,high)) := by
    simpa only [hc2eq] using hc2
  have hc3at : CallbackFn.call_mut (ap1,high) c3 = .ok (t3,(ap1,high)) := by
    simpa only [hc3eq] using hc3
  have hadd1at : (c1 + 1#usize : Result Usize) = .ok c2 := by
    simpa only [hc1eq] using hadd1
  have hadd2at : (c2 + 1#usize : Result Usize) = .ok c3 := by
    simpa only [hc2eq] using hadd2
  have hadd3at : (c3 + 1#usize : Result Usize) = .ok c4 := by
    simpa only [hc3eq] using hadd3
  have hstep0 : fnMutStep CallbackFn ((ap1,high),0#usize) 0 =
      .ok (t0,((ap1,high),c1)) :=
    AspisR1S9HighTermsStepLemmaV1.fnMutStep_of_successful_call CallbackFn (ap1,high) 0#usize 0 t0
      (ap1,high) c1 hc0 hadd0
  have hstep1 : fnMutStep CallbackFn ((ap1,high),c1) 1 =
      .ok (t1,((ap1,high),c2)) :=
    AspisR1S9HighTermsStepLemmaV1.fnMutStep_of_successful_call CallbackFn (ap1,high) c1 1 t1
      (ap1,high) c2 hc1at hadd1at
  have hstep2 : fnMutStep CallbackFn ((ap1,high),c2) 2 =
      .ok (t2,((ap1,high),c3)) :=
    AspisR1S9HighTermsStepLemmaV1.fnMutStep_of_successful_call CallbackFn (ap1,high) c2 2 t2
      (ap1,high) c3 hc2at hadd2at
  have hstep3 : fnMutStep CallbackFn ((ap1,high),c3) 3 =
      .ok (t3,((ap1,high),c4)) :=
    AspisR1S9HighTermsStepLemmaV1.fnMutStep_of_successful_call CallbackFn (ap1,high) c3 3 t3
      (ap1,high) c4 hc3at hadd3at
  have htrace : AspisR1FromFnP6.StatefulFromFnTrace (fnMutStep CallbackFn)
      4 0 ((ap1,high),0#usize) [t0,t1,t2,t3] ((ap1,high),c4) := by
    exact .call hstep0 (.call hstep1 (.call hstep2 (.call hstep3
      (.done 4 ((ap1,high),c4)))))
  have hrun := (AspisR1FromFnP6.statefulFromFnRun_success_iff_trace
      (fnMutStep CallbackFn) (4#usize).val 0 ((ap1,high),0#usize) [t0,t1,t2,t3]
      ((ap1,high),c4)).mpr htrace
  have htraceModel : core.array.from_fn_trace_model (4#usize) CallbackFn (ap1,high) =
      .ok ([t0,t1,t2,t3],((ap1,high),c4)) := by
    simpa only [core.array.from_fn_trace_model] using hrun
  have hlen : [t0,t1,t2,t3].length = (4#usize).val := by simp
  let terms : Array W (4#usize) := ⟨[t0,t1,t2,t3],hlen⟩
  have hmodel : core.array.from_fn_model (4#usize) CallbackFn (ap1,high) =
      .ok (terms,((ap1,high),c4)) := by
    unfold core.array.from_fn_model
    simp only [htraceModel, packArrayState, dif_pos hlen]
    rfl
  have hslot : @AspisR1S9HelperP6.core.array.from_fn W Callback
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (4#usize) CallbackFn (ap1,high) =
      .ok (terms,((ap1,high),4#usize)) := by
    unfold AspisR1S9HelperP6.core.array.from_fn
    simpa [hc4eq] using hmodel
  refine ⟨{
    call0 := call0
    call1 := call1
    call2 := call2
    call3 := call3
    terms := terms
    terms_values := rfl
    trace_model := ?_
    generated_from_fn := hslot
  }⟩
  simpa [hc4eq] using htraceModel

#print axioms AspisR1S9HighTermsConcreteV1.one_call
#print axioms high_terms4_from_fn_p6

end AspisR1S9HighTermsTraceV1
