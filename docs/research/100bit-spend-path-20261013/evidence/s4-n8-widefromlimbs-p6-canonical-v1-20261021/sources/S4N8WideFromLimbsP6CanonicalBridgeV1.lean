import S4N8WideFromLimbsCallBridgeV1
import S4FromFnP6InnerN8ActualCanonicalV1
import S4N8WideFromLimbsABI

open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent AspisR1FromFnP6Generated
set_option autoImplicit false

namespace AspisR1FastDotsN8WideFromLimbsP6CanonicalBridgeV1

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev U8 := Std.U8
abbrev U64 := Std.U64
abbrev U32 := Std.U32
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev Closure := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.closure
abbrev Callback := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
abbrev InnerFn (ops : Ops) :=
  fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 ops

/-- P6 agreement is required only at the actual N8 operation call. It maps
    the raw generated operation and callback result to the P6 execution using
    the current source reducer. This is the explicit Std/P6 boundary; it is
    not an output-canonicality assumption. -/
theorem actual_callback_success_n8_wideFromLimbs_of_p6
    (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (value : Wide) (c' : fast_dots.four_dots.closure)
    (h : Callback ops (a,g) slot = .ok (value,c'))
    (hp6 : ∀ (limbs : Array U64 8#usize),
      ops.arrayFromFn 8#usize (InnerFn ops) limbs =
        arrayFromFnP6 8#usize
          (InnerFn (fourDotsOpsWithActualReducer ops)) limbs)
    (hbinding : ∀ limbs, ops.wideFromLimbs limbs =
      AspisR1FastDotsN8WideFromLimbsABI.finishFromLimbsCurrent limbs) :
    ∃ (iter : AspisR1FastDotsActualCallbackTailTraceRootV1.StepBy)
      (limbs : Array U64 8#usize) (vals : Array U32 8#usize) (body : Wide),
      core.iter.traits.iterator.Iterator.step_by.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        {start:=0#usize, «end»:=26#usize} 4#usize = .ok iter ∧
      AspisR1FastDotsActualCallbackTailTraceRootV1.BaseLoop ops iter a g slot
        (Array.repeat 8#usize 0#u64) = .ok limbs ∧
      ops.arrayFromFn 8#usize (InnerFn ops) limbs = .ok vals ∧
      ops.wideFromLimbs vals = .ok (some body) ∧
      body = AspisR1FastDotsN8WideFromLimbsABI.finishToCurrent
        (AspisR1EbyKFinish.Proof.wideFromParts
          (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word0 vals)
          (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word1 vals)
          (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word2 vals)
          (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word3 vals)
          (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word4 vals)
          (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word5 vals)
          (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word6 vals)
          (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word7 vals)) := by
  obtain ⟨_hclosure,iter,limbs,vals,_optBody,body,_tail0,_wide28,_slotOffset,
      _start,_finish,_bytes,_optQ,_q,_pushed,_u,_tail2,_tailValue,
      hstep,hbase,harray,hbody,hunwrap,_hnew,_hread,_hmul,_hadd104,_hadd120,
      _hslice,_hparse,_hunq,_hpush,_hunpush,_htail,_hfinish,_hadd⟩ :=
    AspisR1FastDotsActualCallbackTailTraceRootV1.actual_callback_success_base_and_tail
      ops a g slot value c' h
  have hmodel : arrayFromFnP6 8#usize
      (InnerFn (fourDotsOpsWithActualReducer ops)) limbs = .ok vals := by
    exact (hp6 limbs).symm.trans harray
  have hactualAdapter :
      (fourDotsOpsWithP6ArrayFromFnN8 (fourDotsOpsWithActualReducer ops)).arrayFromFn
        8#usize (InnerFn (fourDotsOpsWithActualReducer ops)) limbs = .ok vals := by
    change arrayFromFnP6 8#usize
      (InnerFn (fourDotsOpsWithActualReducer ops)) limbs = .ok vals
    exact hmodel
  have hcanonical := generatedInnerN8_actualReducer_success_canonical
    ops limbs vals hactualAdapter
  have hsome : _optBody = some body := by
    have hu : Result.ofOption _optBody Error.panic = .ok body := by
      change Result.ofOption _optBody Error.panic = .ok body
      exact hunwrap
    cases _optBody with
    | none => simp [Result.ofOption] at hu
    | some w => simp only [Result.ofOption, Result.ok.injEq] at hu; subst w; rfl
  have hbody' : ops.wideFromLimbs vals = .ok (some body) := by
    rw [hsome] at hbody
    exact hbody
  have hvalue := AspisR1FastDotsN8WideFromLimbsABI.actual_wideFromLimbs_of_canonical_words
    ops vals body hcanonical hbinding hbody'
  exact ⟨iter,limbs,vals,body,hstep,hbase,harray,hbody',hvalue⟩

/-- Public composed model adapter: current reducer plus the reviewed P6 N8
    array execution. Its field agreement is definitional; this is a Lean model
    adapter and does not assert that the frozen Rust Std call is installed. -/
def withP6CurrentReducer (ops : Ops) : Ops :=
  fourDotsOpsWithP6ArrayFromFnN8 (fourDotsOpsWithActualReducer ops)

theorem p6_array_field_agreement (ops : Ops) (limbs : Array U64 8#usize) :
    (withP6CurrentReducer ops).arrayFromFn 8#usize
      (InnerFn (withP6CurrentReducer ops)) limbs =
    arrayFromFnP6 8#usize
      (InnerFn (fourDotsOpsWithActualReducer (withP6CurrentReducer ops))) limbs := by
  rfl

/-- Adapter specialization removes the P6 agreement premise by reflexivity;
    the only remaining source-operation condition is the explicit
    wideFromLimbs-to-EbyK binding. -/
theorem model_adapter_callback_success_n8_wideFromLimbs
    (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (value : Wide) (c' : fast_dots.four_dots.closure)
    (h : Callback (withP6CurrentReducer ops) (a,g) slot = .ok (value,c'))
    (hbinding : ∀ limbs, (withP6CurrentReducer ops).wideFromLimbs limbs =
      AspisR1FastDotsN8WideFromLimbsABI.finishFromLimbsCurrent limbs) :
    ∃ (iter : AspisR1FastDotsActualCallbackTailTraceRootV1.StepBy)
      (limbs : Array U64 8#usize) (vals : Array U32 8#usize) (body : Wide),
      core.iter.traits.iterator.Iterator.step_by.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        {start:=0#usize, «end»:=26#usize} 4#usize = .ok iter ∧
      AspisR1FastDotsActualCallbackTailTraceRootV1.BaseLoop (withP6CurrentReducer ops)
        iter a g slot (Array.repeat 8#usize 0#u64) = .ok limbs ∧
      (withP6CurrentReducer ops).arrayFromFn 8#usize
        (InnerFn (withP6CurrentReducer ops)) limbs = .ok vals ∧
      (withP6CurrentReducer ops).wideFromLimbs vals = .ok (some body) ∧
      body = AspisR1FastDotsN8WideFromLimbsABI.finishToCurrent
        (AspisR1EbyKFinish.Proof.wideFromParts
          (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word0 vals)
          (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word1 vals)
          (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word2 vals)
          (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word3 vals)
          (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word4 vals)
          (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word5 vals)
          (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word6 vals)
          (AspisR1FastDotsN8WideFromLimbsCallBridgeV1.word7 vals)) := by
  exact actual_callback_success_n8_wideFromLimbs_of_p6
    (withP6CurrentReducer ops) a g slot value c' h
    (p6_array_field_agreement ops) hbinding

#print axioms actual_callback_success_n8_wideFromLimbs_of_p6
#print axioms p6_array_field_agreement
#print axioms model_adapter_callback_success_n8_wideFromLimbs

end AspisR1FastDotsN8WideFromLimbsP6CanonicalBridgeV1
