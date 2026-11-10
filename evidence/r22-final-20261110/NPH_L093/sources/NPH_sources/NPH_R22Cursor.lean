import NPH_R22Loops5
import NCV_Reference.Funs
import S1NativeCompactModelV1
import S1ValuesOwnedModelV1
import AspisR1DecodeKFullV10.Funs
import RPt_FIo_RangeNext

/-! NPH_ (R22, item 2 of the 2026-11-10 continuation: cursor and index arithmetic owed by callers).
Lemmas about the existing gate definitions; nothing merged changes.

- PRECONDITION_B, NCV_Reference bytes32_loop.body and digest_loop.body: reached-cursor loop
  invariants that need no caller length. `BInv`: i = 0 or s + i ≤ len b (every earlier point
  read succeeded); `DInv`: i = 0 or s + 4i ≤ len b (every earlier word32 succeeded,
  `word32_bound`). On them the checked s + i (resp. 4*i, s + 4i) and i + 1 are ok; a cont step keeps
  the invariant; the only callers bytes32 / digest enter at i = 0.
- DIRECT, NCV_Reference decode_frontier_loop.body: every checked operation (32*level, 48 + ·,
  next >>> level, level + 1) is ok under the body's guard level < 20 (`frontier_ops`).
- DIRECT, AspisS1NativeCompact expand_semantic_loop.body: each checked cursor add is followed by a
  bounds-checked range read or range index_mut at [p, p + n); if the wrapping program's access at
  the wrapped end succeeds, the checked add is ok with the same value (NPH_R22Loops4.cursor_direct
  for reads, `mut_cursor_direct` for index_mut, `range_mut_success`); size / 2 is ok for every size.
- PRECONDITION_B, AspisR1DecodeKFullV10 decode_k_value: on `DK` (value < N, byte_offset + 32·N
  and offset_values + N within usize) every checked operation is ok (`dk_ops`). DK holds at every
  call: the only caller is decode_k_loop.body, run only by decode_k with byte_offset = val, where
  decode_k's own checked_mul/checked_add guards returned Some (`dk_guards`) and the loop iterator
  keeps end = N (`dk_value`, `dk_step`).
- PRECONDITION_B, AspisS1ValuesOwned copy_chunk_loop.body: on chunk·32 + 31 ≤ usize max every
  checked operation is ok (`cc_ops`); this holds at every call: copy_chunk runs only from
  values_owned_reference_loop.body under chunk < count, and values_owned_reference fixes
  count = len input / 16 after its checked 2·len succeeded (`vo_guards`, `cc_domain`).
Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22Cursor
open Aeneas Aeneas.Std Result ControlFlow AspisR1.NPH_R22FieldRef

theorem add_val {ty : UScalarTy} (x y z : UScalar ty) (h : (x + y : Result (UScalar ty)) = ok z) :
    z.val = x.val + y.val := by
  have e := UScalar.add_equiv x y
  rw [h] at e
  exact e.2.1

theorem mul_val {ty : UScalarTy} (x y z : UScalar ty) (h : (x * y : Result (UScalar ty)) = ok z) :
    x.val * y.val ≤ UScalar.max ty ∧ z.val = x.val * y.val := by
  have e := UScalar.mul_equiv x y
  change UScalar.mul x y = ok z at h
  rw [h] at e
  exact ⟨e.1, e.2.1⟩

theorem usize_le_max (x : Usize) : x.val ≤ UScalar.max .Usize := by scalar_tac

/-! ### NCV_Reference bytes32_loop.body -/

def BInv (b : Slice U8) (s i : Usize) : Prop := i.val = 0 ∨ s.val + i.val ≤ b.val.length

theorem bytes32_ops (b : Slice U8) (s i : Usize) (inv : BInv b s i) (hi : i < 32#usize) :
    (∃ z, (s + i : Result Usize) = ok z ∧ z.val = s.val + i.val) ∧
      ∃ z, (i + 1#usize : Result Usize) = ok z ∧ z.val = i.val + 1 := by
  have hl := NPH_R22Loops5.slice_len_le b
  have hs := usize_le_max s
  have hb : s.val + i.val ≤ UScalar.max .Usize := by
    rcases inv with h | h
    · omega
    · omega
  exact ⟨add_ok s i hb, NPH_R22Loops.usize_succ_ok i 32#usize (by scalar_tac)⟩

theorem bytes32_step (b : Slice U8) (s : Usize) (a : Array U8 32#usize) (i : Usize)
    (inv : BInv b s i) (a' : Array U8 32#usize) (i' : Usize)
    (h : NCV_Reference.bytes32_loop.body b s a i = ok (cont (a', i'))) : BInv b s i' := by
  unfold NCV_Reference.bytes32_loop.body at h
  split at h
  · rename_i hi
    obtain ⟨⟨z, hz, hzv⟩, ⟨w, hw, hwv⟩⟩ := bytes32_ops b s i inv hi
    obtain ⟨i1, h1, h⟩ := Port3_PushFrame.bind_success _ _ _ h
    obtain ⟨v, hr, h⟩ := Port3_PushFrame.bind_success _ _ _ h
    obtain ⟨a1, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
    obtain ⟨i3, h3, h⟩ := Port3_PushFrame.bind_success _ _ _ h
    have e := Result.ok.inj h
    simp only [ControlFlow.cont.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl⟩ := e
    have zi : z = i1 := Result.ok.inj (hz.symm.trans h1)
    subst zi
    have wi : w = i3 := Result.ok.inj (hw.symm.trans h3)
    subst wi
    have rd := AspisR1.F3P_SliceIndex.read b z v hr
    have hlt : z.val < b.val.length := (List.getElem?_eq_some_iff.mp rd).1
    unfold BInv
    right
    omega
  · cases h

theorem bytes32_entry (b : Slice U8) (s : Usize) :
    NCV_Reference.bytes32 b s = NCV_Reference.bytes32_loop b s (Array.repeat 32#usize 0#u8) 0#usize ∧
      BInv b s 0#usize :=
  ⟨rfl, Or.inl rfl⟩

/-! ### NCV_Reference digest_loop.body -/

theorem word32_bound (b : Slice U8) (s : Usize) (x : U32)
    (h : NCV_Reference.word32 b s = ok x) : s.val + 4 ≤ b.val.length := by
  unfold NCV_Reference.word32 at h
  obtain ⟨v0, r0, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨j1, a1, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨v1, r1, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨j2, a2, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨v2, r2, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨j3, a3, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  obtain ⟨v3, r3, _⟩ := Port3_PushFrame.bind_success _ _ _ h
  have e1 := add_val s 1#usize j1 a1
  have e2 := add_val s 2#usize j2 a2
  have e3 := add_val s 3#usize j3 a3
  have rd := AspisR1.F3P_SliceIndex.read b j3 v3 r3
  have hlt : j3.val < b.val.length := (List.getElem?_eq_some_iff.mp rd).1
  have h3 : (3#usize : Usize).val = 3 := by first | rfl | simp
  rw [e3, h3] at hlt
  omega

def DInv (b : Slice U8) (s i : Usize) : Prop := i.val = 0 ∨ s.val + 4 * i.val ≤ b.val.length

theorem digest_ops (b : Slice U8) (s i : Usize) (inv : DInv b s i) (hi : i < 8#usize) :
    ∃ i1, (4#usize * i : Result Usize) = ok i1 ∧ i1.val = 4 * i.val ∧
      (∃ i2, (s + i1 : Result Usize) = ok i2 ∧ i2.val = s.val + 4 * i.val) ∧
      ∃ z, (i + 1#usize : Result Usize) = ok z ∧ z.val = i.val + 1 := by
  have hl := NPH_R22Loops5.slice_len_le b
  have hs := usize_le_max s
  have h4 : (4#usize : Usize).val = 4 := by first | rfl | simp
  have hm : (4#usize : Usize).val * i.val ≤ UScalar.max .Usize := by
    have := usize_le_max i
    rw [h4]
    have hi' : i.val < 8 := by scalar_tac
    have : 32 ≤ UScalar.max .Usize := by scalar_tac
    omega
  obtain ⟨i1, hi1, vi1⟩ := mul_ok _ _ hm
  have hb : s.val + i1.val ≤ UScalar.max .Usize := by
    rw [vi1, h4]
    rcases inv with h | h
    · rw [h]; omega
    · omega
  obtain ⟨i2, hi2, vi2⟩ := add_ok s i1 hb
  refine ⟨i1, hi1, by rw [vi1, h4], ⟨i2, hi2, by rw [vi2, vi1, h4]⟩,
    NPH_R22Loops.usize_succ_ok i 8#usize (by scalar_tac)⟩

theorem digest_step (b : Slice U8) (s : Usize) (out : Array U32 8#usize) (i : Usize)
    (inv : DInv b s i) (out' : Array U32 8#usize) (i' : Usize)
    (h : NCV_Reference.digest_loop.body b s out i = ok (cont (out', i'))) : DInv b s i' := by
  unfold NCV_Reference.digest_loop.body at h
  split at h
  · rename_i hi
    obtain ⟨z1, hz1, vz1, ⟨z2, hz2, vz2⟩, ⟨w, hw, hwv⟩⟩ := digest_ops b s i inv hi
    obtain ⟨i1, h1, h⟩ := Port3_PushFrame.bind_success _ _ _ h
    have e1 : z1 = i1 := Result.ok.inj (hz1.symm.trans h1)
    subst e1
    obtain ⟨i2, h2, h⟩ := Port3_PushFrame.bind_success _ _ _ h
    have e2 : z2 = i2 := Result.ok.inj (hz2.symm.trans h2)
    subst e2
    obtain ⟨x, hx, h⟩ := Port3_PushFrame.bind_success _ _ _ h
    have wb := word32_bound b z2 x hx
    split at h
    · cases h
    · obtain ⟨o1, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
      obtain ⟨i3, h3, h⟩ := Port3_PushFrame.bind_success _ _ _ h
      have e := Result.ok.inj h
      simp only [ControlFlow.cont.injEq, Prod.mk.injEq] at e
      obtain ⟨_, rfl⟩ := e
      have e3 : w = i3 := Result.ok.inj (hw.symm.trans h3)
      subst e3
      unfold DInv
      right
      rw [hwv]
      omega
  · cases h

theorem digest_entry (b : Slice U8) (s : Usize) : DInv b s 0#usize := Or.inl rfl

/-! ### NCV_Reference decode_frontier_loop.body (DIRECT, guard level < 20) -/

theorem frontier_ops (level : Usize) (hl : level < 20#usize) (next : U64) :
    (∃ i, (32#usize * level : Result Usize) = ok i ∧ ∃ i1, (48#usize + i : Result Usize) = ok i1) ∧
      (∃ z, (next >>> level : Result U64) = ok z) ∧
      ∃ z, (level + 1#usize : Result Usize) = ok z ∧ z.val = level.val + 1 := by
  have hlv : level.val < 20 := by scalar_tac
  have big : 1000 ≤ UScalar.max .Usize := by scalar_tac
  have h32 : (32#usize : Usize).val = 32 := by first | rfl | simp
  have h48 : (48#usize : Usize).val = 48 := by first | rfl | simp
  obtain ⟨i, hi, vi⟩ := mul_ok (32#usize) level (by rw [h32]; omega)
  obtain ⟨i1, hi1, _⟩ := add_ok (48#usize) i (by rw [h48, vi, h32]; omega)
  have hs : level.val < UScalarTy.U64.numBits := by
    first
    | (rw [UScalarTy.U64_numBits_eq]; omega)
    | (simp only [UScalarTy.numBits]; omega)
    | omega
  obtain ⟨z, hz, _⟩ := WP.spec_imp_exists (UScalar.ShiftRight_spec next level hs)
  exact ⟨⟨i, hi, i1, hi1⟩, ⟨z, hz⟩, NPH_R22Loops.usize_succ_ok level 20#usize (by scalar_tac)⟩

/-! ### AspisS1NativeCompact expand_semantic_loop.body (DIRECT) -/

theorem range_mut_success {T : Type} (s : Slice T) (start finish : Usize)
    (out : Slice T × (Slice T → Slice T))
    (h : core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice T)
      s {start := start, «end» := finish} = ok out) :
    start.val ≤ finish.val ∧ finish.val ≤ s.val.length := by
  simp only [core.slice.index.Slice.index_mut, core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut] at h
  split at h
  · rename_i c
    exact ⟨c.1, c.2⟩
  · cases h

/-- If the wrapping program's range index_mut [p, p.wrapping_add n) succeeds, the checked p + n is
ok with the same value. If that access fails, both profiles abort. -/
theorem mut_cursor_direct (b : Slice U8) (p n : Usize) (out : Slice U8 × (Slice U8 → Slice U8))
    (h : core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice U8) b
      { start := p, «end» := Usize.wrapping_add p n } = ok out) :
    ∃ z, (p + n : Result Usize) = ok z ∧ z.val = (Usize.wrapping_add p n).val := by
  have hr := range_mut_success b p _ out h
  have hw := AspisR1.T2Nat_RawBounds.no_wrap p n hr.1
  have hl := NPH_R22Loops5.slice_len_le b
  have hsum : p.val + n.val ≤ UScalar.max .Usize := by
    have := hr.2; rw [hw] at this; omega
  obtain ⟨z, hz, hv⟩ := add_ok p n hsum
  exact ⟨z, hz, by rw [hv, hw]⟩

theorem half_ok (size : Usize) : ∃ z, (size / 2#usize : Result Usize) = ok z := by
  obtain ⟨j, hj, _⟩ := UScalar.div_spec (x:=size) (y:=2#usize) (by decide)
  exact ⟨j, hj⟩

/-! ### AspisR1DecodeKFullV10 decode_k_value: domain, operations and the decode_k guards -/

def DK (byteOffset value offsetValues N : Usize) : Prop :=
  value.val < N.val ∧ byteOffset.val + 32 * N.val ≤ UScalar.max .Usize ∧
    offsetValues.val + N.val ≤ UScalar.max .Usize

theorem dk_ops (byteOffset value offsetValues N : Usize) (d : DK byteOffset value offsetValues N) :
    ∃ i, (value * 32#usize : Result Usize) = ok i ∧
      ∃ start, (byteOffset + i : Result Usize) = ok start ∧ start.val = byteOffset.val + 32 * value.val ∧
        (∀ k : Usize, k.val ≤ 15 → ∃ z, (start + k : Result Usize) = ok z) ∧
        ∃ z, (offsetValues + value : Result Usize) = ok z := by
  obtain ⟨hv, hb, ho⟩ := d
  have h32 : (32#usize : Usize).val = 32 := by first | rfl | simp
  obtain ⟨i, hi, vi⟩ := mul_ok value (32#usize) (by rw [h32]; omega)
  obtain ⟨st, hst, vst⟩ := add_ok byteOffset i (by rw [vi, h32]; omega)
  refine ⟨i, hi, st, hst, by rw [vst, vi, h32]; omega, fun k hk => ?_, ?_⟩
  · obtain ⟨z, hz, _⟩ := add_ok st k (by rw [vst, vi, h32]; omega)
    exact ⟨z, hz⟩
  · obtain ⟨z, hz, _⟩ := add_ok offsetValues value (by omega)
    exact ⟨z, hz⟩

theorem checked_mul_some (x y v : Usize) (h : Usize.checked_mul x y = some v) :
    x.val * y.val ≤ UScalar.max .Usize ∧ v.val = x.val * y.val := by
  unfold Usize.checked_mul core.num.checked_mul_UScalar at h
  cases hm : UScalar.mul x y with
  | ok z =>
    rw [hm] at h
    have zv : z = v := Option.some.inj h
    subst zv
    exact mul_val x y z hm
  | fail e => rw [hm] at h; cases h
  | div => rw [hm] at h; cases h

theorem checked_add_some (x y v : Usize) (h : Usize.checked_add x y = some v) :
    x.val + y.val ≤ UScalar.max .Usize ∧ v.val = x.val + y.val := by
  unfold Usize.checked_add core.num.checked_add_UScalar at h
  cases hm : (x + y : Result Usize) with
  | ok z =>
    first
    | (rw [hm] at h)
    | (change Option.ofResult (x + y) = some v at h; rw [hm] at h)
    have zv : z = v := Option.some.inj h
    subst zv
    have hv := add_val x y z hm
    exact ⟨by rw [← hv]; exact usize_le_max z, hv⟩
  | fail e =>
    first
    | (rw [hm] at h; cases h)
    | (change Option.ofResult (x + y) = some v at h; rw [hm] at h; cases h)
  | div =>
    first
    | (rw [hm] at h; cases h)
    | (change Option.ofResult (x + y) = some v at h; rw [hm] at h; cases h)

/-- decode_k's three checked guards give DK for every value below N, with byte_offset = val. -/
theorem dk_guards (offsetValues N val val1 val2 : Usize)
    (h1 : Usize.checked_mul offsetValues 32#usize = some val)
    (h2 : Usize.checked_mul N 32#usize = some val1)
    (h3 : Usize.checked_add val val1 = some val2) (value : Usize) (hv : value.val < N.val) :
    DK val value offsetValues N := by
  obtain ⟨b1, v1⟩ := checked_mul_some _ _ _ h1
  obtain ⟨b2, v2⟩ := checked_mul_some _ _ _ h2
  obtain ⟨b3, v3⟩ := checked_add_some _ _ _ h3
  have h32 : (32#usize : Usize).val = 32 := by first | rfl | simp
  rw [h32] at b1 b2 v1 v2
  refine ⟨hv, by omega, by omega⟩

/-- The decode_k loop: the value handed to decode_k_value is below the iterator end, and a cont
step keeps the end. -/
theorem dk_value (iter iter1 : core.ops.range.Range Usize) (value : Usize)
    (h : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = ok (some value, iter1)) :
    value.val < iter.end.val ∧ iter1.end = iter.end := by
  have pr := FIo_RangeNext.some_next iter iter1 value h
  rw [pr.1]
  exact ⟨pr.2.2.2, pr.2.1⟩

theorem dk_step {N : Usize} (self : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord) (row : U8)
    (offsetValues byteOffset : Usize) (iter : core.ops.range.Range Usize)
    (out : Array AspisR1DecodeKFullV10.aspis_core.field.QM31 N)
    (iter' : core.ops.range.Range Usize) (out' : Array AspisR1DecodeKFullV10.aspis_core.field.QM31 N)
    (h : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body self row offsetValues
      byteOffset iter out = ok (cont (iter', out'))) : iter'.end = iter.end := by
  unfold AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_loop.body at h
  obtain ⟨⟨o, iter1⟩, hn, h⟩ := Port3_PushFrame.bind_success _ _ _ h
  cases o with
  | none => cases h
  | some value =>
    obtain ⟨r, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
    obtain ⟨cf, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
    cases cf with
    | Continue val =>
      obtain ⟨out1, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
      have e := Result.ok.inj h
      simp only [ControlFlow.cont.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, _⟩ := e
      exact (dk_value iter iter1 value hn).2
    | Break residual =>
      obtain ⟨r1, _, h⟩ := Port3_PushFrame.bind_success _ _ _ h
      cases h

/-! ### AspisS1ValuesOwned copy_chunk_loop.body -/

theorem cc_ops (chunk byte : Usize) (hc : chunk.val * 32 + 31 ≤ UScalar.max .Usize)
    (hb : byte < 16#usize) :
    ∃ i, (chunk * 16#usize : Result Usize) = ok i ∧ (∃ i1, (i + byte : Result Usize) = ok i1) ∧
      ∃ i2, (chunk * 32#usize : Result Usize) = ok i2 ∧ (∃ i3, (i2 + byte : Result Usize) = ok i3) ∧
        ∃ i4, (i2 + 16#usize : Result Usize) = ok i4 ∧ (∃ i5, (i4 + byte : Result Usize) = ok i5) ∧
          ∃ z, (byte + 1#usize : Result Usize) = ok z ∧ z.val = byte.val + 1 := by
  have hbv : byte.val < 16 := by scalar_tac
  have h16 : (16#usize : Usize).val = 16 := by first | rfl | simp
  have h32 : (32#usize : Usize).val = 32 := by first | rfl | simp
  obtain ⟨i, hi, vi⟩ := mul_ok chunk (16#usize) (by rw [h16]; omega)
  obtain ⟨i1, hi1, _⟩ := add_ok i byte (by rw [vi, h16]; omega)
  obtain ⟨i2, hi2, vi2⟩ := mul_ok chunk (32#usize) (by rw [h32]; omega)
  obtain ⟨i3, hi3, _⟩ := add_ok i2 byte (by rw [vi2, h32]; omega)
  obtain ⟨i4, hi4, vi4⟩ := add_ok i2 (16#usize) (by rw [vi2, h32, h16]; omega)
  obtain ⟨i5, hi5, _⟩ := add_ok i4 byte (by rw [vi4, vi2, h32, h16]; omega)
  exact ⟨i, hi, ⟨i1, hi1⟩, i2, hi2, ⟨i3, hi3⟩, i4, hi4, ⟨i5, hi5⟩,
    NPH_R22Loops.usize_succ_ok byte 16#usize (by scalar_tac)⟩

/-- values_owned_reference's checked 2·len and len / 16, on the path that enters the loop. -/
theorem vo_guards (len i4 count : Usize) (h4 : (2#usize * len : Result Usize) = ok i4)
    (hcount : (len / 16#usize : Result Usize) = ok count) :
    2 * len.val ≤ UScalar.max .Usize ∧ count.val = len.val / 16 := by
  obtain ⟨b, _⟩ := mul_val _ _ _ h4
  have h2 : (2#usize : Usize).val = 2 := by first | rfl | simp
  rw [h2] at b
  obtain ⟨j, hj, vj⟩ := UScalar.div_spec (x:=len) (y:=16#usize) (by decide)
  have same : j = count := Result.ok.inj (hj.symm.trans hcount)
  subst same
  have h16 : (16#usize : Usize).val = 16 := by first | rfl | simp
  refine ⟨b, ?_⟩
  first | (rw [vj, h16]) | (simpa [h16] using vj) | omega

/-- Every chunk run by values_owned_reference_loop.body (guard chunk < count) satisfies the
copy_chunk domain. -/
theorem cc_domain (len count chunk : Usize) (h2 : 2 * len.val ≤ UScalar.max .Usize)
    (hc : count.val = len.val / 16) (hlt : chunk < count) :
    chunk.val * 32 + 31 ≤ UScalar.max .Usize := by
  have : chunk.val < count.val := by scalar_tac
  omega

#print axioms add_val
#print axioms mul_val
#print axioms bytes32_ops
#print axioms bytes32_step
#print axioms bytes32_entry
#print axioms word32_bound
#print axioms digest_ops
#print axioms digest_step
#print axioms digest_entry
#print axioms frontier_ops
#print axioms range_mut_success
#print axioms mut_cursor_direct
#print axioms half_ok
#print axioms dk_ops
#print axioms checked_mul_some
#print axioms checked_add_some
#print axioms dk_guards
#print axioms dk_value
#print axioms dk_step
#print axioms cc_ops
#print axioms vo_guards
#print axioms cc_domain
end AspisR1.NPH_R22Cursor
