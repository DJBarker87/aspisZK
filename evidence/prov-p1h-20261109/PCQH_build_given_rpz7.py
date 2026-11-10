#!/usr/bin/env python3
"""PCQH_build_given_rpz7.py: writes inputs/RPz7_h2_given.json (hand proofs for the transport row family, domain-restricted)."""
import json
F='FIo_Native.PRVFresh_RPz7_FIo_NativeFuns_h2'
P='PRVEq.RPz7_FIo_NativeFuns_h2'
helpers=f'''/-- PCQH helper: successful `Range<usize>::next` returning `some d` has `d < end`. -/
theorem {P}.range_next_usize_lt (r r1 : core.ops.range.Range Std.Usize) (d : Std.Usize)
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
theorem {P}.TAU_le (d i3 : Std.Usize) (h : FIo_Native.transport.TAU.index_usize d = ok i3) : i3.val ≤ 4 := by
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

theorem {P}.wmul2_lt (x : Std.Usize) (hx : x.val < 16) : (Std.Usize.wrapping_mul 2#usize x).val < 32 := by
  rw [Std.Usize.wrapping_mul_val_eq]
  have h2 : (2#usize).val = 2 := by scalar_tac
  have hs : 32 < UScalar.size UScalarTy.Usize := by
    rw [UScalar.size_UScalarTyUsize, Std.Usize.size_def]
    rcases System.Platform.numBits_eq with h | h <;> simp [Std.Usize.numBits, h]
  rw [h2, Nat.mod_eq_of_lt (by omega)]
  omega

theorem {P}.fresh_shr_eq (j i : Std.Usize) : {F}.Std.Usize.wrapping_shr j i = Aeneas.Std.Usize.wrapping_shr j (UScalar.cast .U32 i) := rfl
theorem {P}.fresh_shl_eq (j i : Std.Usize) : {F}.Std.Usize.wrapping_shl j i = Aeneas.Std.Usize.wrapping_shl j (UScalar.cast .U32 i) := rfl

theorem {P}.bind_congr_ok {{α β : Type}} (m : Result α) (f g : α → Result β) (h : ∀ a, m = ok a → f a = g a) :
    Bind.bind m f = Bind.bind m g := by
  cases hm : m with
  | ok a => simp only [bind_tc_ok]; exact h a hm
  | fail e => rfl
  | div => rfl

/-- PCQH: the fresh body preserves the end of the range. -/
theorem {P}.body_end (j : Std.Usize) (iter : core.ops.range.Range Std.Usize) (out : Std.Usize) (iter2 : core.ops.range.Range Std.Usize) (out2 : Std.Usize)
    (h : {F}.transport.Variant.row_loop.body j iter out = ok (ControlFlow.cont (iter2, out2))) : iter2.«end» = iter.«end» := by
  unfold {F}.transport.Variant.row_loop.body at h
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
      cases h3 : {F}.transport.TAU.index_usize d with
      | fail e => simp [h3] at h
      | div => simp [h3] at h
      | ok i3 =>
        simp [h3] at h
        rw [← h.1]
        exact he

/-- PCQH SEMANTIC NOTE (not an encoding difference): the gate row_loop.body uses CHECKED shifts `j >>> i`, `i2 <<< i4`
(fail when the amount is not below the word width), the OFF fresh body uses `wrapping_shr`/`wrapping_shl` (mask the amount). The two bodies are NOT
equal on all inputs (an iterator with start >= numBits/2 gives `fail integerOverflow` on the gate side and a later `fail arrayOutOfBounds` or a value on the fresh side).
They agree whenever the range end is at most 16 (then d < 16 and 2*d < 32; TAU entries are at most 4). -/
theorem {P}.transport.Variant.row_loop.body_dom (j : Std.Usize) (iter : core.ops.range.Range Std.Usize) (out : Std.Usize)
    (hend : iter.«end».val ≤ 16) :
    {F}.transport.Variant.row_loop.body j iter out = FIo_Native.transport.Variant.row_loop.body j iter out := by
  unfold {F}.transport.Variant.row_loop.body FIo_Native.transport.Variant.row_loop.body
  refine {P}.bind_congr_ok _ _ _ ?_
  rintro ⟨o, iter1⟩ hn
  cases o with
  | none => rfl
  | some d =>
    have hd : d.val < 16 := by have := {P}.range_next_usize_lt iter iter1 d hn; omega
    have hi := {P}.wmul2_lt d hd
    have e_shr : (j >>> Std.Usize.wrapping_mul 2#usize d : Result Std.Usize)
        = ok (Aeneas.Std.Usize.wrapping_shr j (UScalar.cast .U32 (Std.Usize.wrapping_mul 2#usize d))) :=
      PRVH.usize_shr_usize j _ hi
    try dsimp only
    simp only [lift, bind_tc_ok, e_shr, {P}.fresh_shr_eq, {P}.fresh_shl_eq, {P}.transport.TAU]
    cases h3 : FIo_Native.transport.TAU.index_usize d with
    | fail e => simp [h3]
    | div => simp [h3]
    | ok i3 =>
      have h4 := {P}.wmul2_lt i3 (by have := {P}.TAU_le d i3 h3; omega)
      have e_shl := PRVH.usize_shl_usize ((Aeneas.Std.Usize.wrapping_shr j (UScalar.cast .U32 (Std.Usize.wrapping_mul 2#usize d))) &&& 3#usize)
        (Std.Usize.wrapping_mul 2#usize i3) h4
      simp only [h3, bind_tc_ok, lift, e_shl]
#print axioms {P}.transport.Variant.row_loop.body_dom'''
loop=f'''theorem {P}.transport.Variant.row_loop_dom (iter : core.ops.range.Range Std.Usize) (j out : Std.Usize)
    (hend : iter.«end».val ≤ 16) :
    {F}.transport.Variant.row_loop iter j out = FIo_Native.transport.Variant.row_loop iter j out := by
  unfold {F}.transport.Variant.row_loop FIo_Native.transport.Variant.row_loop
  refine PRVH.loop_eq_dom _ _ (fun x => x.1.«end».val ≤ 16) ?_ ?_ (iter, out) hend
  · rintro ⟨iter1, out1⟩ h
    exact {P}.transport.Variant.row_loop.body_dom j iter1 out1 h
  · rintro ⟨iter1, out1⟩ ⟨iter2, out2⟩ h hF
    have := {P}.body_end j iter1 out1 iter2 out2 hF
    simp only at h ⊢
    rw [this]
    exact h
#print axioms {P}.transport.Variant.row_loop_dom'''
row=f'''set_option maxHeartbeats 400000 in
/-- PCQH: the fresh `row` equals the gate `row` for ALL arguments: `row` calls `row_loop` with the fixed range `0..5` (end 5 <= 16), so the domain condition of
`row_loop_dom` always holds. -/
theorem {P}.transport.Variant.row : @{F}.transport.Variant.row = @FIo_Native.transport.Variant.row := by
  have hr : ∀ j : Std.Usize, {F}.transport.Variant.row_loop {{ start := 0#usize, «end» := 5#usize }} j 0#usize
      = FIo_Native.transport.Variant.row_loop {{ start := 0#usize, «end» := 5#usize }} j 0#usize :=
    fun j => {P}.transport.Variant.row_loop_dom _ j 0#usize (by scalar_tac)
  delta {F}.transport.Variant.row FIo_Native.transport.Variant.row
  simp only [{P}.transport.Variant.Insts.CoreCmpPartialEqVariant.eq, hr]
#print axioms {P}.transport.Variant.row'''
g={'transport.Variant.row_loop.body':helpers,'transport.Variant.row_loop':loop,'transport.Variant.row':row}
json.dump(g,open('inputs/RPz7_h2_given.json','w'),indent=1)
