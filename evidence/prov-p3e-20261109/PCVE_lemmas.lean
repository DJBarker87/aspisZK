set_option maxHeartbeats 200000 in
theorem PRVEq.RPz7_FIo_NativeFuns_h2.transport.Variant.Insts.CoreCmpPartialEqVariant.eq : @FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.Insts.CoreCmpPartialEqVariant.eq = @FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq := by
  first | (trace "PRV-S1 PRVEq.RPz7_FIo_NativeFuns_h2.transport.Variant.Insts.CoreCmpPartialEqVariant.eq"; rfl) | (trace "PRV-S2 PRVEq.RPz7_FIo_NativeFuns_h2.transport.Variant.Insts.CoreCmpPartialEqVariant.eq"; delta FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.Insts.CoreCmpPartialEqVariant.eq FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq; try rfl; done)
#print axioms PRVEq.RPz7_FIo_NativeFuns_h2.transport.Variant.Insts.CoreCmpPartialEqVariant.eq

set_option maxHeartbeats 200000 in
theorem PRVEq.RPz7_FIo_NativeFuns_h2.transport.TAU : @FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.TAU = @FIo_Native.transport.TAU := by
  first | (trace "PRV-S1 PRVEq.RPz7_FIo_NativeFuns_h2.transport.TAU"; rfl) | (trace "PRV-S2 PRVEq.RPz7_FIo_NativeFuns_h2.transport.TAU"; delta FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.TAU FIo_Native.transport.TAU; try rfl; done)
#print axioms PRVEq.RPz7_FIo_NativeFuns_h2.transport.TAU

/-- PCQH helper: successful `Range<usize>::next` returning `some d` has `d < end`. -/
theorem PRVEq.RPz7_FIo_NativeFuns_h2.range_next_usize_lt (r r1 : core.ops.range.Range Std.Usize) (d : Std.Usize)
    (h : core.iter.range.IteratorRange.next core.iter.range.StepUsize r = ok (some d, r1)) :
    d.val < r.«end».val := by
  unfold core.iter.range.IteratorRange.next at h
  simp [core.iter.range.StepUsize, core.iter.range.UScalarStep, core.cmp.PartialOrdUsize, core.clone.CloneUsize,
    liftFun2, liftFun1, core.cmp.impls.PartialOrdUsize.lt, core.clone.impls.CloneUsize.clone] at h
  by_cases hlt : r.start.val < r.«end».val
  · rw [if_pos hlt] at h
    cases hf : core.iter.range.UScalarStep.forward_checked r.start 1#usize with
    | fail e => simp [hf] at h
    | div => simp [hf] at h
    | ok n =>
      cases n with
      | none => simp [hf] at h
      | some n =>
        simp [hf] at h
        rw [← h.1]
        exact hlt
  · rw [if_neg hlt] at h
    simp at h

/-- PCQH helper: every element of the gate `TAU` is at most 4. -/
theorem PRVEq.RPz7_FIo_NativeFuns_h2.TAU_le (d i3 : Std.Usize) (h : FIo_Native.transport.TAU.index_usize d = ok i3) : i3.val ≤ 4 := by
  unfold Std.Array.index_usize at h
  cases hq : (FIo_Native.transport.TAU)[d]? with
  | none => simp [hq] at h
  | some x =>
    simp [hq] at h
    rw [← h]
    rw [Std.Array.getElem?_Usize_eq] at hq
    have hmem : x ∈ ([3#usize, 4#usize, 2#usize, 0#usize, 1#usize] : List Std.Usize) := by
      have h2 : x ∈ (FIo_Native.transport.TAU : Std.Array Std.Usize 5#usize).val := List.mem_of_getElem? hq
      unfold FIo_Native.transport.TAU at h2
      exact h2
    simp at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl <;> scalar_tac

theorem PRVEq.RPz7_FIo_NativeFuns_h2.wmul2_lt (x : Std.Usize) (hx : x.val < 16) : (Std.Usize.wrapping_mul 2#usize x).val < 32 := by
  rw [Std.Usize.wrapping_mul_val_eq]
  have h2 : (2#usize).val = 2 := by scalar_tac
  have hs : 32 < UScalar.size UScalarTy.Usize := by
    rw [UScalar.size_UScalarTyUsize, Std.Usize.size_def]
    rcases System.Platform.numBits_eq with h | h <;> simp [Std.Usize.numBits, h]
  rw [h2, Nat.mod_eq_of_lt (by omega)]
  omega

theorem PRVEq.RPz7_FIo_NativeFuns_h2.fresh_shr_eq (j i : Std.Usize) : FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.Std.Usize.wrapping_shr j i = Aeneas.Std.Usize.wrapping_shr j (UScalar.cast .U32 i) := rfl
theorem PRVEq.RPz7_FIo_NativeFuns_h2.fresh_shl_eq (j i : Std.Usize) : FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.Std.Usize.wrapping_shl j i = Aeneas.Std.Usize.wrapping_shl j (UScalar.cast .U32 i) := rfl

theorem PRVEq.RPz7_FIo_NativeFuns_h2.bind_congr_ok {α β : Type} (m : Result α) (f g : α → Result β) (h : ∀ a, m = ok a → f a = g a) :
    Bind.bind m f = Bind.bind m g := by
  cases hm : m with
  | ok a => simp only [bind_tc_ok]; exact h a hm
  | fail e => rfl
  | div => rfl

/-- PCQH: the fresh body preserves the end of the range. -/
theorem PRVEq.RPz7_FIo_NativeFuns_h2.body_end (j : Std.Usize) (iter : core.ops.range.Range Std.Usize) (out : Std.Usize) (iter2 : core.ops.range.Range Std.Usize) (out2 : Std.Usize)
    (h : FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row_loop.body j iter out = ok (ControlFlow.cont (iter2, out2))) : iter2.«end» = iter.«end» := by
  unfold FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.Variant.row_loop.body at h
  cases hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter with
  | fail e => simp [hn] at h
  | div => simp [hn] at h
  | ok p =>
    obtain ⟨o, iter1⟩ := p
    have he := PRVH.range_next_end core.iter.range.StepUsize iter iter1 o hn
    simp only [hn, bind_tc_ok] at h
    cases o with
    | none => simp at h
    | some d =>
      simp only [lift, bind_tc_ok] at h
      cases h3 : FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2.transport.TAU.index_usize d with
      | fail e => simp [h3] at h
      | div => simp [h3] at h
      | ok i3 =>
        simp [h3] at h
        rw [← h.1]
        exact he

