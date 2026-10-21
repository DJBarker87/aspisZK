import S4N8WideFromLimbsABI
import FourDotsActualCallbackTailTraceRootV1

open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent
set_option autoImplicit false

namespace AspisR1FastDotsN8WideFromLimbsCallBridgeV1

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev U32 := Std.U32
abbrev Callback := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut

private theorem xs_length (xs : Array U32 8#usize) : xs.val.length = 8 := by
  have hsize : (8#usize).val = 8 := by scalar_tac
  simpa [hsize] using xs.property

def word0 (xs : Array U32 8#usize) : U32 :=
  xs.val[0]'(by have hx := xs_length xs; omega)
def word1 (xs : Array U32 8#usize) : U32 :=
  xs.val[1]'(by have hx := xs_length xs; omega)
def word2 (xs : Array U32 8#usize) : U32 :=
  xs.val[2]'(by have hx := xs_length xs; omega)
def word3 (xs : Array U32 8#usize) : U32 :=
  xs.val[3]'(by have hx := xs_length xs; omega)
def word4 (xs : Array U32 8#usize) : U32 :=
  xs.val[4]'(by have hx := xs_length xs; omega)
def word5 (xs : Array U32 8#usize) : U32 :=
  xs.val[5]'(by have hx := xs_length xs; omega)
def word6 (xs : Array U32 8#usize) : U32 :=
  xs.val[6]'(by have hx := xs_length xs; omega)
def word7 (xs : Array U32 8#usize) : U32 :=
  xs.val[7]'(by have hx := xs_length xs; omega)

private theorem ofOption_success {α : Type} (o : Option α) (e : Error) (x : α)
    (h : Result.ofOption o e = .ok x) : o = some x := by
  cases o with
  | none => simp [Result.ofOption] at h
  | some y =>
      simp only [Result.ofOption, Result.ok.injEq] at h
      subst y
      rfl

/-- The actual generated callback success contains one successful N8 array
    operation, followed by the same array's `wideFromLimbs` operation. Under
    explicit canonical-output and Ops-binding premises, the successful body
    value is the checked EbyKFinish limb packing mapped into the current
    nominal Wide carrier. -/
theorem actual_callback_success_n8_wideFromLimbs
    (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (value : Wide) (c' : fast_dots.four_dots.closure)
    (h : Callback ops (a,g) slot = .ok (value,c'))
    (hcanonical : ∀ (limbs : Array U64 8#usize) (vals : Array U32 8#usize),
      ops.arrayFromFn 8#usize
        (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 ops)
        limbs = .ok vals → ∀ x, x ∈ vals.val → x.val < AspisV8R17.RawReducer.P)
    (hbinding : ∀ limbs, ops.wideFromLimbs limbs =
      AspisR1FastDotsN8WideFromLimbsABI.finishFromLimbsCurrent limbs) :
    ∃ (iter : AspisR1FastDotsActualCallbackTailTraceRootV1.StepBy)
      (limbs : Array U64 8#usize) (vals : Array U32 8#usize) (body : Wide),
      core.iter.traits.iterator.Iterator.step_by.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        {start:=0#usize, «end»:=26#usize} 4#usize = .ok iter ∧
      AspisR1FastDotsActualCallbackTailTraceRootV1.BaseLoop ops iter a g slot
        (Array.repeat 8#usize 0#u64) = .ok limbs ∧
      ops.arrayFromFn 8#usize
        (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 ops)
        limbs = .ok vals ∧
      ops.wideFromLimbs vals = .ok (some body) ∧
      body = AspisR1FastDotsN8WideFromLimbsABI.finishToCurrent
        (AspisR1EbyKFinish.Proof.wideFromParts
          (word0 vals) (word1 vals) (word2 vals) (word3 vals)
          (word4 vals) (word5 vals) (word6 vals) (word7 vals)) := by
  obtain ⟨_, iter, limbs, vals, optBody, body, tail0, wide28, slotOffset,
      start, finish, bytes, optQ, q, pushed, u, tail2, tailValue,
      hstep, hbase, hvals, hbody, hunwrap, hnew, hread, hmul, hadd104,
      hadd120, hslice, hparse, hunq, hpush, hunpush, htail, hfinish, hadd⟩ :=
    AspisR1FastDotsActualCallbackTailTraceRootV1.actual_callback_success_base_and_tail
      ops a g slot value c' h
  have hsome : optBody = some body := by
    apply ofOption_success optBody Error.panic body
    change Result.ofOption optBody Error.panic = .ok body
    exact hunwrap
  have hbody' : ops.wideFromLimbs vals = .ok (some body) := by
    rw [hsome] at hbody
    exact hbody
  have hcan := hcanonical limbs vals hvals
  have hbodyEq := AspisR1FastDotsN8WideFromLimbsABI.actual_wideFromLimbs_of_canonical_words
    ops vals body hcan hbinding hbody'
  exact ⟨iter, limbs, vals, body, hstep, hbase, hvals, hbody', hbodyEq⟩

#print axioms actual_callback_success_n8_wideFromLimbs

end AspisR1FastDotsN8WideFromLimbsCallBridgeV1
