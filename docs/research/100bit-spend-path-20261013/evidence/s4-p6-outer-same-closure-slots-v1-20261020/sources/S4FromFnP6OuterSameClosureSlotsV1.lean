import S4FromFnP6GeneratedOuterN8FourTraceV2
import S4GeneratedCallbackClosurePreservationV28

open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent
set_option autoImplicit false

namespace AspisR1FromFnP6Generated

private theorem add_success_value {x y z : Usize}
    (h : (x + y : Result Usize) = .ok z) : z.val = x.val + y.val := by
  have hequiv := UScalar.add_equiv x y
  rw [h] at hequiv
  rcases hequiv with ⟨_, hval, _⟩
  exact hval

private theorem next_cursor_eq_one (z : Usize)
    (h : (0#usize + 1#usize : Result Usize) = .ok z) : z = 1#usize := by
  apply UScalar.eq_of_val_eq
  have hv := add_success_value h
  have hz : (0#usize).val = 0 := by scalar_tac
  have ho : (1#usize).val = 1 := by scalar_tac
  simpa [hz, ho] using hv

private theorem next_cursor_eq_two (z : Usize)
    (h : (1#usize + 1#usize : Result Usize) = .ok z) : z = 2#usize := by
  apply UScalar.eq_of_val_eq
  have hv := add_success_value h
  have ho : (1#usize).val = 1 := by scalar_tac
  have ht : (2#usize).val = 2 := by scalar_tac
  simpa [ho, ht] using hv

private theorem next_cursor_eq_three (z : Usize)
    (h : (2#usize + 1#usize : Result Usize) = .ok z) : z = 3#usize := by
  apply UScalar.eq_of_val_eq
  have hv := add_success_value h
  have ht : (2#usize).val = 2 := by scalar_tac
  have hth : (3#usize).val = 3 := by scalar_tac
  simpa [ht, hth] using hv

private theorem composedN8Field_success_readback
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (limbs : Aeneas.Std.Array Std.U64 8#usize)
    (values : Aeneas.Std.Array Std.U32 8#usize)
    (h : (fourDotsOpsWithP6ArrayFromFnN4N8 ops).arrayFromFn 8#usize
      (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) limbs = .ok values) :
    InnerN8Readback (fourDotsOpsWithP6ArrayFromFnN4N8 ops) limbs values := by
  have hN : (8#usize).val = 8 := by scalar_tac
  have hneq : (8#usize).val ≠ 4 := by omega
  have hmodel : arrayFromFnP6 8#usize
      (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) limbs = .ok values := by
    simpa only [fourDotsOpsWithP6ArrayFromFnN4N8,
      fourDotsOpsWithP6ArrayFromFn, fourDotsOpsWithP6ArrayFromFnN8,
      if_neg hneq, if_pos hN] using h
  exact innerArrayP6_success_values_match_fixedV6
    (fourDotsOpsWithP6ArrayFromFnN4N8 ops) limbs values hmodel

/-- The P6 N=4 outer trace calls the generated four_dots callback four times
with the same captured `(q,g)` closure at slots 0 through 3. Each such call
also reaches its actual N=8 array-field operation; the latter retains its
ordered limb-read/reducer facts. The P6 Rust-stdlib correspondence remains an
explicit boundary. -/
theorem generatedFourDotsN4_success_same_closure_slots_and_innerN8
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (q : Aeneas.Std.Array Std.U8 608#usize)
    (g : Aeneas.Std.Array aspis_core.field.wide_exact.WideExact 29#usize)
    {values : Aeneas.Std.Array aspis_core.field.wide_exact.WideExact 4#usize}
    (h : (fourDotsOpsWithP6ArrayFromFnN4N8 ops).arrayFromFn 4#usize
      (fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) (q,g) = .ok values) :
    ∃ (v0 v1 v2 v3 : aspis_core.field.wide_exact.WideExact)
      (limbs0 limbs1 limbs2 limbs3 : Aeneas.Std.Array Std.U64 8#usize),
      values.val = [v0,v1,v2,v3] ∧
      fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops) (q,g) 0#usize = .ok (v0,(q,g)) ∧
      fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops) (q,g) 1#usize = .ok (v1,(q,g)) ∧
      fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops) (q,g) 2#usize = .ok (v2,(q,g)) ∧
      fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops) (q,g) 3#usize = .ok (v3,(q,g)) ∧
      (∃ vals0 : Aeneas.Std.Array Std.U32 8#usize,
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops).arrayFromFn 8#usize
          (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
            (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) limbs0 = .ok vals0 ∧
        InnerN8Readback (fourDotsOpsWithP6ArrayFromFnN4N8 ops) limbs0 vals0) ∧
      (∃ vals1 : Aeneas.Std.Array Std.U32 8#usize,
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops).arrayFromFn 8#usize
          (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
            (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) limbs1 = .ok vals1 ∧
        InnerN8Readback (fourDotsOpsWithP6ArrayFromFnN4N8 ops) limbs1 vals1) ∧
      (∃ vals2 : Aeneas.Std.Array Std.U32 8#usize,
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops).arrayFromFn 8#usize
          (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
            (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) limbs2 = .ok vals2 ∧
        InnerN8Readback (fourDotsOpsWithP6ArrayFromFnN4N8 ops) limbs2 vals2) ∧
      (∃ vals3 : Aeneas.Std.Array Std.U32 8#usize,
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops).arrayFromFn 8#usize
          (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
            (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) limbs3 = .ok vals3 ∧
        InnerN8Readback (fourDotsOpsWithP6ArrayFromFnN4N8 ops) limbs3 vals3) := by
  have houter : (fourDotsOpsWithP6ArrayFromFn
      (fourDotsOpsWithP6ArrayFromFnN8 ops)).arrayFromFn 4#usize
      (fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (fourDotsOpsWithP6ArrayFromFn
          (fourDotsOpsWithP6ArrayFromFnN8 ops))) (q,g) = .ok values := by
    simpa [fourDotsOpsWithP6ArrayFromFnN4N8] using h
  obtain ⟨v0,v1,v2,v3,s1,s2,s3,s4,hvalues,h0,h1,h2,h3⟩ :=
    fourDotsOuterGeneratedCallback_success_four_steps
      (fourDotsOpsWithP6ArrayFromFnN8 ops) q g houter
  let cb := fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
      (fourDotsOpsWithP6ArrayFromFnN4N8 ops)
  obtain ⟨c1,i1,hcall0,hadd0,hs1⟩ := fnMutStep_success cb ((q,g),0#usize) 0 h0
  have hpres0 := actualGeneratedCallback_success_preserves_closure
    (fourDotsOpsWithP6ArrayFromFnN4N8 ops) (q,g) 0#usize hcall0
  have hi1 := next_cursor_eq_one i1 hadd0
  have hs1' : s1 = ((q,g),1#usize) := by rw [hs1,hpres0,hi1]; rfl
  rw [hs1'] at h1
  obtain ⟨c2,i2,hcall1,hadd1,hs2⟩ := fnMutStep_success cb ((q,g),1#usize) 1 h1
  have hpres1 := actualGeneratedCallback_success_preserves_closure
    (fourDotsOpsWithP6ArrayFromFnN4N8 ops) (q,g) 1#usize hcall1
  have hi2 := next_cursor_eq_two i2 (by simpa using hadd1)
  have hs2' : s2 = ((q,g),2#usize) := by rw [hs2,hpres1,hi2]; rfl
  rw [hs2'] at h2
  obtain ⟨c3,i3,hcall2,hadd2,hs3⟩ := fnMutStep_success cb ((q,g),2#usize) 2 h2
  have hpres2 := actualGeneratedCallback_success_preserves_closure
    (fourDotsOpsWithP6ArrayFromFnN4N8 ops) (q,g) 2#usize hcall2
  have hi3 := next_cursor_eq_three i3 (by simpa using hadd2)
  have hs3' : s3 = ((q,g),3#usize) := by rw [hs3,hpres2,hi3]; rfl
  rw [hs3'] at h3
  obtain ⟨_,_,hcall3,_,_⟩ := fnMutStep_success cb ((q,g),3#usize) 3 h3
  have hpres3 := actualGeneratedCallback_success_preserves_closure
    (fourDotsOpsWithP6ArrayFromFnN4N8 ops) (q,g) 3#usize hcall3
  obtain ⟨limbs0,vals0,hfield0⟩ := generatedFourDotsCall_success_has_innerN8_array_call
    (fourDotsOpsWithP6ArrayFromFnN4N8 ops) q g 0#usize hcall0
  obtain ⟨limbs1,vals1,hfield1⟩ := generatedFourDotsCall_success_has_innerN8_array_call
    (fourDotsOpsWithP6ArrayFromFnN4N8 ops) q g 1#usize hcall1
  obtain ⟨limbs2,vals2,hfield2⟩ := generatedFourDotsCall_success_has_innerN8_array_call
    (fourDotsOpsWithP6ArrayFromFnN4N8 ops) q g 2#usize hcall2
  obtain ⟨limbs3,vals3,hfield3⟩ := generatedFourDotsCall_success_has_innerN8_array_call
    (fourDotsOpsWithP6ArrayFromFnN4N8 ops) q g 3#usize hcall3
  have hfacts0 := composedN8Field_success_readback ops limbs0 vals0 hfield0
  have hfacts1 := composedN8Field_success_readback ops limbs1 vals1 hfield1
  have hfacts2 := composedN8Field_success_readback ops limbs2 vals2 hfield2
  have hfacts3 := composedN8Field_success_readback ops limbs3 vals3 hfield3
  exact ⟨v0,v1,v2,v3,limbs0,limbs1,limbs2,limbs3,hvalues,
    (by simpa [cb,hpres0] using hcall0),
    (by simpa [cb,hpres1] using hcall1),
    (by simpa [cb,hpres2] using hcall2),
    (by simpa [cb,hpres3] using hcall3),
    ⟨vals0,hfield0,hfacts0⟩,⟨vals1,hfield1,hfacts1⟩,
    ⟨vals2,hfield2,hfacts2⟩,⟨vals3,hfield3,hfacts3⟩⟩

#print axioms generatedFourDotsN4_success_same_closure_slots_and_innerN8

end AspisR1FromFnP6Generated
