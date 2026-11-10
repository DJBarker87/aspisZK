
/-- PCVE step reductions: the matcher inside `row_loop.body` is not reduced by `cases o` (the goal keeps
`let (o, iter1) := (some d, iter1); match_1 ...` with the bound `d` inside a lambda, which is why `e_shr` about the free `d`
never matched in PCQH_L022..L025). These two lemmas reduce each side to its explicit `some d` continuation by `rfl`. -/
theorem PCVE.fresh_body_some (j : Std.Usize) (iter iter1 : core.ops.range.Range Std.Usize) (out d : Std.Usize)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = ok (some d, iter1)) :
    FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row_loop.body j iter out =
      (do
        let i ← lift (Std.Usize.wrapping_mul 2#usize d)
        let i1 ← lift (FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.Std.Usize.wrapping_shr j i)
        let i2 ← lift (i1 &&& 3#usize)
        let i3 ← Array.index_usize FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.TAU d
        let i4 ← lift (Std.Usize.wrapping_mul 2#usize i3)
        let i5 ← lift (FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.Std.Usize.wrapping_shl i2 i4)
        let out1 ← lift (out ||| i5)
        ok (ControlFlow.cont (iter1, out1))) := by
  unfold FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row_loop.body
  rw [hn]
  rfl

theorem PCVE.gate_body_some (j : Std.Usize) (iter iter1 : core.ops.range.Range Std.Usize) (out d : Std.Usize)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = ok (some d, iter1)) :
    FIo_Native.transport.Variant.row_loop.body j iter out =
      (do
        let i ← lift (Std.Usize.wrapping_mul 2#usize d)
        let i1 ← (j >>> i)
        let i2 ← lift (i1 &&& 3#usize)
        let i3 ← Array.index_usize FIo_Native.transport.TAU d
        let i4 ← lift (Std.Usize.wrapping_mul 2#usize i3)
        let i5 ← (i2 <<< i4)
        let out1 ← lift (out ||| i5)
        ok (ControlFlow.cont (iter1, out1))) := by
  unfold FIo_Native.transport.Variant.row_loop.body
  rw [hn]
  rfl
#print axioms PCVE.fresh_body_some
#print axioms PCVE.gate_body_some
