import S4FourCallbacksForwardRootV1
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

def oldCapturedTail (ops : Ops) (a : Array Std.U8 608#usize) (a1 : Array Wide 29#usize)
    (slot : Usize) (value : Wide) : Result (Wide × (Array U8 608#usize × Array Wide 29#usize)) := do
  let tail ← ops.ebyKNew
  let we ← Array.index_usize a1 28#usize
  let i ← slot * 120#usize
  let i1 ← i + 104#usize
  let i2 ← i + 120#usize
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) a
      { start := i1, «end» := i2 }
  let o1 ← ops.qm31FromBytes s
  let q ← core.option.Option.unwrap o1
  let (r, tail1) ← ops.ebyKPush tail we q
  core.result.Result.unwrap core.fmt.DebugUnit r
  let tail2 ←
    fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1 ops
      { start := 0#usize, «end» := 2#usize } a a1 slot tail1
  let we1 ← ops.ebyKFinish tail2
  let we2 ← ops.wideAdd value we1
  ok (we2,(a,a1))

def groupedOld (ops : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) : Result (Wide × (Array U8 608#usize × Array Wide 29#usize)) := do
  let limbs := Array.repeat 8#usize 0#u64
  let iter ← core.iter.traits.iterator.Iterator.step_by.trait_default
    (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
    { start := 0#usize, «end» := 26#usize } 4#usize
  let limbs1 ← fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
    ops iter q g slot limbs
  let values ← ops.arrayFromFn 8#usize
    (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 ops) limbs1
  let o ← ops.wideFromLimbs values
  let value ← core.option.Option.unwrap o
  oldCapturedTail ops q g slot value

private theorem bind_congr_right {A B : Type} (r : Result A)
    (f g : A → Result B) (h : ∀ x, f x=g x) : (r >>= f)=(r >>= g) := by
  cases r with
  | ok x => exact h x
  | fail e => rfl
  | div => rfl

theorem old_captured_tail_eq_map (ops : Ops) (q : Array U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize) (value : Wide) :
    oldCapturedTail ops q g slot value =
      (oldTail ops q g slot value >>= fun out => .ok (out,(q,g))) := by
  unfold oldCapturedTail oldTail
  simp only [result_bind_assoc,bind_tc_ok,result_bind_ok_id]
  repeat' (apply bind_congr_right; intro x)
  rcases x with ⟨r,t⟩
  change (core.result.Result.unwrap core.fmt.DebugUnit r >>= _) =
    ((core.result.Result.unwrap core.fmt.DebugUnit r >>= _) >>= _)
  rw [result_bind_assoc]
  apply bind_congr_right
  intro u
  simp only [result_bind_assoc,bind_tc_ok,result_bind_ok_id]

theorem old_callback_eq_grouped (ops : Ops) (q : Array U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize) :
    fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      ops (q,g) slot=groupedOld ops q g slot := by rfl

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
  rw [old_callback_eq_grouped]
  unfold groupedOld
  simp only [hiter,bind_tc_ok,hhead,hpackOld,ho,hvalue]
  rw [old_captured_tail_eq_map]
  exact htuple

/-- The retained concrete operation chain discharges both generic operation
premises. This remains the selected P6 installation, not Rust Std adoption. -/
theorem installed_fixed_helper_success_old_callback
    (base : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (out : Wide)
    (hrun : fast_dots.four_dots_one
      (AspisR1FastDotsFourCallbacksForwardRootV1.install base) q g slot=.ok out) :
    fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      (AspisR1FastDotsFourCallbacksForwardRootV1.install base) (q,g) slot=.ok (out,(q,g)) := by
  exact fixed_helper_success_old_callback
    (AspisR1FastDotsFourCallbacksForwardRootV1.install base) q g slot out rfl (fun _ => rfl) hrun

#print axioms installed_fixed_helper_success_old_callback

#print axioms old_captured_tail_eq_map
#print axioms old_callback_eq_grouped
#print axioms fixed_helper_eq_grouped
#print axioms fixed_helper_success_old_callback
end AspisR1FastDotsWholeHelperTransferRootV1
