
theorem PCVE.probe1 (j : Std.Usize) (iter : core.ops.range.Range Std.Usize) (out : Std.Usize)
    (hend : iter.«end».val ≤ 16) :
    FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row_loop.body j iter out = FIo_Native.transport.Variant.row_loop.body j iter out := by
  unfold FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row_loop.body FIo_Native.transport.Variant.row_loop.body
  refine PRVEq.RPz7_FIo_NativeFuns_h2.bind_congr_ok _ _ _ ?_
  rintro ⟨o, iter1⟩ hn
  cases o with
  | none => rfl
  | some d =>
    have hd : d.val < 16 := by have := PRVEq.RPz7_FIo_NativeFuns_h2.range_next_usize_lt iter iter1 d hn; omega
    have hi := PRVEq.RPz7_FIo_NativeFuns_h2.wmul2_lt d hd
    have e_shr : (j >>> Std.Usize.wrapping_mul 2#usize d : Result Std.Usize)
        = ok (Aeneas.Std.Usize.wrapping_shr j (UScalar.cast .U32 (Std.Usize.wrapping_mul 2#usize d))) :=
      PRVH.usize_shr_usize j _ hi
    try dsimp only
    trace_state
    set_option pp.explicit true in
    trace_state
    simp only [lift, bind_tc_ok]
    set_option pp.explicit false in
    trace_state
    done
