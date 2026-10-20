import S4FromFnP6InnerN8ArrayFieldV1
import S4FromFnP6FourTraceV1
import AspisR1FastDotsCurrent.FunsOpsV4

open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent
set_option autoImplicit false

namespace AspisR1FromFnP6Generated

/-- Compose the reviewed P6 operation at the generated N=4 outer constructor
and the generated N=8 inner array callback. -/
def fourDotsOpsWithP6ArrayFromFnN4N8
    (ops : AspisR1FastDotsCurrent.FourDotsOps) :
    AspisR1FastDotsCurrent.FourDotsOps :=
  fourDotsOpsWithP6ArrayFromFn
    (fourDotsOpsWithP6ArrayFromFnN8 ops)

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Exact success decomposition of the generated callback body: reaching a
successful callback result entails success of its actual length-eight
`arrayFromFn` field call. No arithmetic backend is unfolded. -/
theorem generatedFourDotsCall_success_has_innerN8_array_call
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (q : Aeneas.Std.Array Std.U8 608#usize)
    (g : Aeneas.Std.Array aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize)
    {value : aspis_core.field.wide_exact.WideExact}
    {closure' : fast_dots.four_dots.closure}
    (h : fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      ops (q,g) slot = .ok (value,closure')) :
    ∃ limbs : Aeneas.Std.Array Std.U64 8#usize,
      ∃ values : Aeneas.Std.Array Std.U32 8#usize,
        ops.arrayFromFn 8#usize
          (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 ops)
          limbs = .ok values := by
  unfold fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut at h
  obtain ⟨iter, _hstepBy, hrest⟩ := bind_success _ _ _ h
  obtain ⟨limbs, _hloop0, hrest⟩ := bind_success _ _ _ hrest
  obtain ⟨values, harray, _hrest⟩ := bind_success _ _ _ hrest
  exact ⟨limbs, values, harray⟩

/-- Eight-cell evidence produced by `innerArrayP6_success_values_match_fixedV6`. -/
def InnerN8Readback (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (limbs : Aeneas.Std.Array Std.U64 8#usize)
    (values : Aeneas.Std.Array Std.U32 8#usize) : Prop :=
  ∃ m0 m1 m2 m3 m4 m5 m6 m7 w0 w1 w2 w3 w4 w5 w6 w7,
    values.val = [m0,m1,m2,m3,m4,m5,m6,m7] ∧
    Array.index_usize limbs 0#usize = .ok w0 ∧ ops.m31ReduceU64 w0 = .ok m0 ∧
    Array.index_usize limbs 1#usize = .ok w1 ∧ ops.m31ReduceU64 w1 = .ok m1 ∧
    Array.index_usize limbs 2#usize = .ok w2 ∧ ops.m31ReduceU64 w2 = .ok m2 ∧
    Array.index_usize limbs 3#usize = .ok w3 ∧ ops.m31ReduceU64 w3 = .ok m3 ∧
    Array.index_usize limbs 4#usize = .ok w4 ∧ ops.m31ReduceU64 w4 = .ok m4 ∧
    Array.index_usize limbs 5#usize = .ok w5 ∧ ops.m31ReduceU64 w5 = .ok m5 ∧
    Array.index_usize limbs 6#usize = .ok w6 ∧ ops.m31ReduceU64 w6 = .ok m6 ∧
    Array.index_usize limbs 7#usize = .ok w7 ∧ ops.m31ReduceU64 w7 = .ok m7

private theorem composedN8Field_success_readback
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (limbs : Aeneas.Std.Array Std.U64 8#usize)
    (values : Aeneas.Std.Array Std.U32 8#usize)
    (h : (fourDotsOpsWithP6ArrayFromFnN4N8 ops).arrayFromFn 8#usize
      (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) limbs = .ok values) :
    InnerN8Readback (fourDotsOpsWithP6ArrayFromFnN4N8 ops) limbs values := by
  have hN : (8#usize).val = 8 := by decide
  have hneq : (8#usize).val ≠ 4 := by omega
  have hmodel : arrayFromFnP6 8#usize
      (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) limbs = .ok values := by
    simpa only [fourDotsOpsWithP6ArrayFromFnN4N8,
      fourDotsOpsWithP6ArrayFromFn, fourDotsOpsWithP6ArrayFromFnN8,
      if_neg hneq, if_pos hN] using h
  exact innerArrayP6_success_values_match_fixedV6
    (fourDotsOpsWithP6ArrayFromFnN4N8 ops) limbs values hmodel

/-- A successful composed N=4 generated array call yields four ordered outer
callbacks, and each callback success reaches the same generated N=8 array
field call with the eight exact limb-read/reducer facts. -/
theorem generatedFourDotsN4_success_four_innerN8_readbacks
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
      (∃ vals : Aeneas.Std.Array Std.U32 8#usize,
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops).arrayFromFn 8#usize
          (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
            (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) limbs0 = .ok vals ∧
        InnerN8Readback (fourDotsOpsWithP6ArrayFromFnN4N8 ops) limbs0 vals) ∧
      (∃ vals : Aeneas.Std.Array Std.U32 8#usize,
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops).arrayFromFn 8#usize
          (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
            (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) limbs1 = .ok vals ∧
        InnerN8Readback (fourDotsOpsWithP6ArrayFromFnN4N8 ops) limbs1 vals) ∧
      (∃ vals : Aeneas.Std.Array Std.U32 8#usize,
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops).arrayFromFn 8#usize
          (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
            (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) limbs2 = .ok vals ∧
        InnerN8Readback (fourDotsOpsWithP6ArrayFromFnN4N8 ops) limbs2 vals) ∧
      (∃ vals : Aeneas.Std.Array Std.U32 8#usize,
        (fourDotsOpsWithP6ArrayFromFnN4N8 ops).arrayFromFn 8#usize
          (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
            (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) limbs3 = .ok vals ∧
        InnerN8Readback (fourDotsOpsWithP6ArrayFromFnN4N8 ops) limbs3 vals) := by
  have houter : (fourDotsOpsWithP6ArrayFromFn
      (fourDotsOpsWithP6ArrayFromFnN8 ops)).arrayFromFn 4#usize
      (fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (fourDotsOpsWithP6ArrayFromFn
          (fourDotsOpsWithP6ArrayFromFnN8 ops))) (q,g) = .ok values := by
    simpa [fourDotsOpsWithP6ArrayFromFnN4N8] using h
  obtain ⟨v0,v1,v2,v3,s1,s2,s3,s4,hvalues,h0,h1,h2,h3⟩ :=
    fourDotsOuterGeneratedCallback_success_four_steps
      (fourDotsOpsWithP6ArrayFromFnN8 ops) q g houter
  obtain ⟨_, _, hcall0, _, _⟩ := fnMutStep_success
    (fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
      (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) ((q,g),0#usize) 0 h0
  obtain ⟨_, _, hcall1, _, _⟩ := fnMutStep_success
    (fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
      (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) s1 1 h1
  obtain ⟨_, _, hcall2, _, _⟩ := fnMutStep_success
    (fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
      (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) s2 2 h2
  obtain ⟨_, _, hcall3, _, _⟩ := fnMutStep_success
    (fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
      (fourDotsOpsWithP6ArrayFromFnN4N8 ops)) s3 3 h3
  obtain ⟨limbs0, vals0, hfield0⟩ := generatedFourDotsCall_success_has_innerN8_array_call
    (fourDotsOpsWithP6ArrayFromFnN4N8 ops) q g 0#usize hcall0
  obtain ⟨limbs1, vals1, hfield1⟩ := generatedFourDotsCall_success_has_innerN8_array_call
    (fourDotsOpsWithP6ArrayFromFnN4N8 ops) s1.1.1 s1.1.2 s1.2 hcall1
  obtain ⟨limbs2, vals2, hfield2⟩ := generatedFourDotsCall_success_has_innerN8_array_call
    (fourDotsOpsWithP6ArrayFromFnN4N8 ops) s2.1.1 s2.1.2 s2.2 hcall2
  obtain ⟨limbs3, vals3, hfield3⟩ := generatedFourDotsCall_success_has_innerN8_array_call
    (fourDotsOpsWithP6ArrayFromFnN4N8 ops) s3.1.1 s3.1.2 s3.2 hcall3
  have hfacts0 := composedN8Field_success_readback ops limbs0 vals0 hfield0
  have hfacts1 := composedN8Field_success_readback ops limbs1 vals1 hfield1
  have hfacts2 := composedN8Field_success_readback ops limbs2 vals2 hfield2
  have hfacts3 := composedN8Field_success_readback ops limbs3 vals3 hfield3
  exact ⟨v0,v1,v2,v3,limbs0,limbs1,limbs2,limbs3,
    hvalues,⟨vals0,hfield0,hfacts0⟩,⟨vals1,hfield1,hfacts1⟩,
    ⟨vals2,hfield2,hfacts2⟩,⟨vals3,hfield3,hfacts3⟩⟩

#print axioms generatedFourDotsCall_success_has_innerN8_array_call
#print axioms generatedFourDotsN4_success_four_innerN8_readbacks

end AspisR1FromFnP6Generated
