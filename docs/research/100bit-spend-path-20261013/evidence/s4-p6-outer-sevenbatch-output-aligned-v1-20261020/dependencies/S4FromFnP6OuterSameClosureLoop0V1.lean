import S4FromFnP6OuterSameClosureSlotsV1
import Aeneas.Std.RangeIter

open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent
set_option autoImplicit false

namespace AspisR1FromFnP6Generated

private abbrev StepBy := core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)
private def localStartBy : StepBy :=
  { iter := { start := 0#usize, «end» := 26#usize }, step_by := 4#usize }
private theorem local_initialized_step_by :
    core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 0#usize, «end» := 26#usize } 4#usize = .ok localStartBy := by
  simp [localStartBy, core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default]

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem callback_success_loop0_and_array
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (q : Aeneas.Std.Array Std.U8 608#usize)
    (g : Aeneas.Std.Array aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize)
    {value : aspis_core.field.wide_exact.WideExact}
    {closure' : fast_dots.four_dots.closure}
    (h : fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      (fourDotsOpsWithP6ArrayFromFnN4N8 ops) (q,g) slot = .ok (value,closure')) :
    ∃ iter limbs vals,
      core.iter.traits.iterator.Iterator.step_by.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        { start := 0#usize, «end» := 26#usize } 4#usize = .ok iter ∧
      fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops) iter q g slot
        (Array.repeat 8#usize 0#u64) = .ok limbs ∧
      (fourDotsOpsWithP6ArrayFromFnN4N8 ops).arrayFromFn 8#usize
        (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
          (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) limbs = .ok vals := by
  unfold fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut at h
  obtain ⟨iter, hstep, hrest⟩ := bind_success _ _ _ h
  obtain ⟨limbs, hloop, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨vals, harray, _hrest⟩ := bind_success _ _ _ hrest
  exact ⟨iter, limbs, vals, hstep, hloop, harray⟩

/-- Successful composed N=4 construction exposes the source StepBy
initialization, loop0 result, and same-loop N=8 array call for each of the
four same-closure callback slots. The P6/Rust std correspondence remains
explicit. -/
theorem generatedFourDotsN4_success_same_closure_loop0_four_calls
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (q : Aeneas.Std.Array Std.U8 608#usize)
    (g : Aeneas.Std.Array aspis_core.field.wide_exact.WideExact 29#usize)
    {values : Aeneas.Std.Array aspis_core.field.wide_exact.WideExact 4#usize}
    (h : (fourDotsOpsWithP6ArrayFromFnN4N8 ops).arrayFromFn 4#usize
      (fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) (q,g) = .ok values) :
    ∃ (v0 v1 v2 v3 : aspis_core.field.wide_exact.WideExact)
      (limbs0 limbs1 limbs2 limbs3 : Aeneas.Std.Array Std.U64 8#usize)
      (vals0 vals1 vals2 vals3 : Aeneas.Std.Array Std.U32 8#usize),
      values.val = [v0,v1,v2,v3] ∧
      fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops) (q,g) 0#usize = .ok (v0,(q,g)) ∧
      fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops) (q,g) 1#usize = .ok (v1,(q,g)) ∧
      fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops) (q,g) 2#usize = .ok (v2,(q,g)) ∧
      fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops) (q,g) 3#usize = .ok (v3,(q,g)) ∧
      core.iter.traits.iterator.Iterator.step_by.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        { start := 0#usize, «end» := 26#usize } 4#usize =
          .ok localStartBy ∧
      fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops) localStartBy q g 0#usize
        (Array.repeat 8#usize 0#u64) = .ok limbs0 ∧
      (fourDotsOpsWithP6ArrayFromFnN4N8 ops).arrayFromFn 8#usize
        (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
          (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) limbs0 = .ok vals0 ∧
      fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops) localStartBy q g 1#usize
        (Array.repeat 8#usize 0#u64) = .ok limbs1 ∧
      (fourDotsOpsWithP6ArrayFromFnN4N8 ops).arrayFromFn 8#usize
        (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
          (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) limbs1 = .ok vals1 ∧
      fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops) localStartBy q g 2#usize
        (Array.repeat 8#usize 0#u64) = .ok limbs2 ∧
      (fourDotsOpsWithP6ArrayFromFnN4N8 ops).arrayFromFn 8#usize
        (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
          (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) limbs2 = .ok vals2 ∧
      fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops) localStartBy q g 3#usize
        (Array.repeat 8#usize 0#u64) = .ok limbs3 ∧
      (fourDotsOpsWithP6ArrayFromFnN4N8 ops).arrayFromFn 8#usize
        (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
          (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) limbs3 = .ok vals3 := by
  obtain ⟨v0,v1,v2,v3,limbsRead0,limbsRead1,limbsRead2,limbsRead3,hvalues,
      hcall0,hcall1,hcall2,hcall3,_hread0,_hread1,_hread2,_hread3⟩ :=
    generatedFourDotsN4_success_same_closure_slots_and_innerN8 ops q g h
  obtain ⟨it0,limbs0,vals0,hs0,hloop0,harray0⟩ :=
    callback_success_loop0_and_array ops q g 0#usize hcall0
  obtain ⟨it1,limbs1,vals1,hs1,hloop1,harray1⟩ :=
    callback_success_loop0_and_array ops q g 1#usize hcall1
  obtain ⟨it2,limbs2,vals2,hs2,hloop2,harray2⟩ :=
    callback_success_loop0_and_array ops q g 2#usize hcall2
  obtain ⟨it3,limbs3,vals3,hs3,hloop3,harray3⟩ :=
    callback_success_loop0_and_array ops q g 3#usize hcall3
  have hstart0 : it0 = localStartBy :=
    Result.ok.inj (hs0.symm.trans local_initialized_step_by)
  have hstart1 : it1 = localStartBy :=
    Result.ok.inj (hs1.symm.trans local_initialized_step_by)
  have hstart2 : it2 = localStartBy :=
    Result.ok.inj (hs2.symm.trans local_initialized_step_by)
  have hstart3 : it3 = localStartBy :=
    Result.ok.inj (hs3.symm.trans local_initialized_step_by)
  exact ⟨v0,v1,v2,v3,limbs0,limbs1,limbs2,limbs3,vals0,vals1,vals2,vals3,hvalues,
    hcall0,hcall1,hcall2,hcall3,local_initialized_step_by,
    by simpa only [hstart0] using hloop0, harray0,
    by simpa only [hstart1] using hloop1, harray1,
    by simpa only [hstart2] using hloop2, harray2,
    by simpa only [hstart3] using hloop3, harray3⟩

#print axioms generatedFourDotsN4_success_same_closure_loop0_four_calls

end AspisR1FromFnP6Generated
