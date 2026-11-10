
theorem PCVE.transport.Variant.row_loop.body_dom (j : Std.Usize) (iter : core.ops.range.Range Std.Usize) (out : Std.Usize)
    (hend : iter.«end».val ≤ 16) :
    FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row_loop.body j iter out = FIo_Native.transport.Variant.row_loop.body j iter out := by
  cases hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter with
  | fail e =>
    unfold FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row_loop.body FIo_Native.transport.Variant.row_loop.body
    rw [hn]; rfl
  | div =>
    unfold FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row_loop.body FIo_Native.transport.Variant.row_loop.body
    rw [hn]; rfl
  | ok p =>
    obtain ⟨o, iter1⟩ := p
    cases o with
    | none =>
      unfold FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row_loop.body FIo_Native.transport.Variant.row_loop.body
      rw [hn]; rfl
    | some d =>
      rw [PCVE.fresh_body_some j iter iter1 out d hn, PCVE.gate_body_some j iter iter1 out d hn]
      have hd : d.val < 16 := by have := PRVEq.RPz7_FIo_NativeFuns_h2.range_next_usize_lt iter iter1 d hn; omega
      have hi := PRVEq.RPz7_FIo_NativeFuns_h2.wmul2_lt d hd
      have e_shr : (j >>> Std.Usize.wrapping_mul 2#usize d : Result Std.Usize)
          = ok (Aeneas.Std.Usize.wrapping_shr j (UScalar.cast .U32 (Std.Usize.wrapping_mul 2#usize d))) :=
        PRVH.usize_shr_usize j _ hi
      simp only [lift, bind_tc_ok, e_shr, PRVEq.RPz7_FIo_NativeFuns_h2.transport.TAU,
        PRVEq.RPz7_FIo_NativeFuns_h2.fresh_shr_eq, PRVEq.RPz7_FIo_NativeFuns_h2.fresh_shl_eq]
      cases h3 : Array.index_usize FIo_Native.transport.TAU d with
      | fail e => simp [h3]
      | div => simp [h3]
      | ok i3 =>
        have h4 := PRVEq.RPz7_FIo_NativeFuns_h2.wmul2_lt i3 (by have := PRVEq.RPz7_FIo_NativeFuns_h2.TAU_le d i3 h3; omega)
        have e_shl := PRVH.usize_shl_usize ((Aeneas.Std.Usize.wrapping_shr j (UScalar.cast .U32 (Std.Usize.wrapping_mul 2#usize d))) &&& 3#usize)
          (Std.Usize.wrapping_mul 2#usize i3) h4
        simp only [h3, bind_tc_ok, e_shl]
#print axioms PCVE.transport.Variant.row_loop.body_dom
