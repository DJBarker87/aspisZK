
theorem PCVE.transport.Variant.row_loop_dom (iter : core.ops.range.Range Std.Usize) (j out : Std.Usize)
    (hend : iter.«end».val ≤ 16) :
    FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row_loop iter j out = FIo_Native.transport.Variant.row_loop iter j out := by
  unfold FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row_loop FIo_Native.transport.Variant.row_loop
  refine PRVH.loop_eq_dom _ _ (fun x => x.1.«end».val ≤ 16) ?_ ?_ (iter, out) hend
  · rintro ⟨iter1, out1⟩ h
    exact PCVE.transport.Variant.row_loop.body_dom j iter1 out1 h
  · rintro ⟨iter1, out1⟩ ⟨iter2, out2⟩ h hF
    have := PRVEq.RPz7_FIo_NativeFuns_h2.body_end j iter1 out1 iter2 out2 hF
    simp only at h ⊢
    rw [this]
    exact h
#print axioms PCVE.transport.Variant.row_loop_dom

/-- No domain hypothesis: `row` fixes the range to `0..5` (end 5 <= 16). -/
theorem PCVE.transport.Variant.row : @FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row = @FIo_Native.transport.Variant.row := by
  have hr : ∀ j : Std.Usize, FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row_loop { start := 0#usize, «end» := 5#usize } j 0#usize
      = FIo_Native.transport.Variant.row_loop { start := 0#usize, «end» := 5#usize } j 0#usize :=
    fun j => PCVE.transport.Variant.row_loop_dom _ j 0#usize (by scalar_tac)
  delta FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row FIo_Native.transport.Variant.row
  simp only [PRVEq.RPz7_FIo_NativeFuns_h2.transport.Variant.Insts.CoreCmpPartialEqVariant.eq, hr]
#print axioms PCVE.transport.Variant.row
