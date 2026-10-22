import S4FixedHeadLoopTransferRootV1
import S4LiteralN8PackingRootV1
import S4FixedTailProgramEqualityRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsWholeHelperTransferRootV1
open AspisR1FastDotsCurrent
open AspisR1FastDotsFixedTailProgramEqualityRootV1 (fixedTail oldTail fixed_tail_eq_old_tail)
open AspisR1FastDotsLiteralN8PackingRootV1 (literalEight readReduce literal_eight_success_p6_same_output)
abbrev Ops := FourDotsOps
abbrev Wide := aspis_core.field.wide_exact.WideExact
abbrev StepBy := core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)

def groupedFixed (ops : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) : Result Wide := do
  let limbs := Array.repeat 8#usize 0#u64
  let iter ← core.iter.traits.iterator.Iterator.step_by.trait_default
    (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
    { start := 0#usize, «end» := 26#usize } 4#usize
  let limbs1 ← fast_dots.four_dots_one_loop0 ops iter q g slot limbs
  let values ← literalEight ops limbs1
  let o ← ops.wideFromLimbs values
  let value ← core.option.Option.unwrap o
  fixedTail ops q g slot value

private theorem result_bind_assoc {A B C : Type} (r : Result A)
    (f : A → Result B) (g : B → Result C) :
    ((r >>= f) >>= g)=(r >>= fun x => f x >>= g) := by cases r <;> rfl
private theorem result_bind_ok_id {A : Type} (r : Result A) :
    (r >>= fun x => .ok x)=r := by cases r <;> rfl
private theorem bind_ok_inv {A B : Type} {r : Result A} {f : A → Result B} {x : B}
    (h : (r >>= f)=.ok x) : ∃ a, r=.ok a ∧ f a=.ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem fixed_helper_eq_grouped (ops : Ops) (q : Array U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize) :
    fast_dots.four_dots_one ops q g slot=groupedFixed ops q g slot := by
  simp only [fast_dots.four_dots_one,groupedFixed,literalEight,readReduce,fixedTail,
    result_bind_assoc,bind_tc_ok,result_bind_ok_id]

/-- Complete selected fixed helper accepted-run transfer to the original
callback, preserving the same output and unchanged captured arrays. The two
explicit operation boundaries are the limb count and P6 N8 array constructor. -/
theorem fixed_helper_success_old_callback
    (ops : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (out : Wide)
    (hcount : ops.wideLimbCount=.ok 8#usize)
    (harray : ∀ limbs : Array U64 8#usize,
      ops.arrayFromFn 8#usize
        (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 ops)
        limbs = AspisR1FromFnP6Generated.arrayFromFnP6 8#usize
          (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 ops) limbs)
    (hrun : fast_dots.four_dots_one ops q g slot=.ok out) :
    fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      ops (q,g) slot=.ok (out,(q,g)) := by
  rw [fixed_helper_eq_grouped] at hrun
  unfold groupedFixed at hrun
  obtain ⟨iter,hiter,hrun⟩ := bind_ok_inv hrun
  obtain ⟨limbs,hlimbs,hrun⟩ := bind_ok_inv hrun
  obtain ⟨values,hvalues,hrun⟩ := bind_ok_inv hrun
  obtain ⟨o,ho,hrun⟩ := bind_ok_inv hrun
  obtain ⟨value,hvalue,htail⟩ := bind_ok_inv hrun
  have hstep : iter.step_by=4#usize := by
    simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
      core.iter.traits.iterator.Iterator.step_by.default] at hiter
    cases Result.ok.inj hiter
    rfl
  have hhead := AspisR1FastDotsFixedHeadLoopTransferRootV1.fixed_head_loop_success_old_head_loop
    ops q g slot iter (Array.repeat 8#usize 0#u64) limbs hcount hstep hlimbs
  have hpack := literal_eight_success_p6_same_output ops limbs values hvalues
  have hpackOld : ops.arrayFromFn 8#usize
      (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 ops)
      limbs=.ok values := (harray limbs).trans hpack
  have htailOld : oldTail ops q g slot value=.ok out :=
    (fixed_tail_eq_old_tail ops q g slot value).symm.trans htail
  have htuple := congrArg (fun r : Result Wide => r >>= fun x => .ok (x,(q,g))) htailOld
  simp only [bind_tc_ok] at htuple
  unfold fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
  simp only [hiter,bind_tc_ok,hhead,hpackOld,ho,hvalue]
  simpa only [oldTail,result_bind_assoc,bind_tc_ok,result_bind_ok_id] using htuple

#print axioms fixed_helper_eq_grouped
#print axioms fixed_helper_success_old_callback
end AspisR1FastDotsWholeHelperTransferRootV1
