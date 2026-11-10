import NPH_R22Cursor
import AspisR1PrefixAggregateParser.Funs
import OraclePortCkptAbi2Extracted.Funs
import MultiproofConeRef.Funs
import AspisR1Post25Sampler.Funs
import AspisR1Post25SamplerIndexedAddSmallCandidate.Funs

/-! NPH_ (R22, items 2-3 of the 2026-11-10 continuation): bodies whose every checked operation is
ok by its own guard, a constant divisor, a constant table bound, or a following bounds-checked access.
Lemmas about the existing gate definitions; nothing merged changes.

- DIRECT, AspisR1PrefixAggregateParser parse_record: its only checked operation 5 + size takes size
  from row_shape, and every row_shape size is ≤ 3712 (`table_size`, ExtractedRowShape.table), so it is
  ok for every input (`record_size_ok`).
- DIRECT, parse_record_at: 5 + i likewise; offset + length is followed by Slice.get [offset, ·):
  if the wrapping program's get at the wrapped end returns Some, the checked add is ok with the same
  value (`get_cursor_direct`, `get_success`). When that get returns None the wrapping program
  returns Err(Length) while the checked model aborts at the add; both are rejections because every
  executing caller (Prefix.parse) propagates the error with `?` (textual reading, flagged).
- DIRECT, OraclePortCkptAbi2Extracted body_byte: every subtraction i - c runs on the else branch of
  i < c (`guarded_sub`); / and % are by nonzero constants (`divrem_ok`); the queries branch is the
  e_byte pattern (NPH_R22Loops5.ebyte_ops).
- DIRECT, AspisR1Post25Sampler qm31_div_pass_loop.body (j - 1 under j > 0, u64 shift by 32, / and %
  by P), low_base_p_digits_loop0.body (4i, start + 1..3, i + 1 under i < 8) and
  AspisR1Post25SamplerIndexedAddSmallCandidate add_small_base_p_loop.body (u64 sum of two u32, % and
  / by P, i + 1 under i < 8): every checked operation is ok for every input under the guard.
- DIRECT, MultiproofConeRef write_parent: index / 2 is ok for every u32, and w + 1 follows a
  successful Array.update at w on a 16-element array, so w < 16 (`update_lt`).
Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22Direct
open Aeneas Aeneas.Std Result AspisR1.NPH_R22FieldRef

/-! ### Row-shape sizes and the two record parsers -/

theorem table_size (row : U8) (k : U8) (size : Usize)
    (h : AspisR1.ExtractedRowShape.table row = some (k, size)) : size.val ≤ 3712 := by
  unfold AspisR1.ExtractedRowShape.table at h
  split_ifs at h <;> (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; decide)

theorem prefix_shape_size (row : U8) (k : U8) (size : Usize)
    (h : AspisR1PrefixAggregateParser.r1_wire.row_shape row = ok (some (k, size))) : size.val ≤ 3712 := by
  rw [NCO_ParserShape.source_shape, AspisR1.ExtractedRowShape.row_shape_eq_table row] at h
  exact table_size row k size (Result.ok.inj h)

theorem record_size_ok (row : U8) (k : U8) (size : Usize)
    (h : AspisR1PrefixAggregateParser.r1_wire.row_shape row = ok (some (k, size))) :
    ∃ z, (5#usize + size : Result Usize) = ok z ∧ z.val = 5 + size.val := by
  have hs := prefix_shape_size row k size h
  have h5 : (5#usize : Usize).val = 5 := by first | rfl | simp
  have big : 4000 ≤ UScalar.max .Usize := by scalar_tac
  obtain ⟨z, hz, hv⟩ := add_ok (5#usize) size (by rw [h5]; omega)
  exact ⟨z, hz, by rw [hv, h5]⟩

theorem get_success {T : Type} (s : Slice T) (start finish : Usize) (x : Slice T)
    (h : core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice T) s
      {start := start, «end» := finish} = ok (some x)) :
    start.val ≤ finish.val ∧ finish.val ≤ s.val.length := by
  simp only [core.slice.Slice.get, core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.get] at h
  split at h
  · rename_i c
    exact ⟨c.1, c.2⟩
  · cases h

/-- If the wrapping program's get [offset, offset.wrapping_add length) returns Some, the checked
offset + length is ok with the same value. -/
theorem get_cursor_direct (b : Slice U8) (p n : Usize) (x : Slice U8)
    (h : core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8) b
      {start := p, «end» := Usize.wrapping_add p n} = ok (some x)) :
    ∃ z, (p + n : Result Usize) = ok z ∧ z.val = (Usize.wrapping_add p n).val := by
  have hr := get_success b p _ x h
  have hw := AspisR1.T2Nat_RawBounds.no_wrap p n hr.1
  have hl := NPH_R22Loops5.slice_len_le b
  have hsum : p.val + n.val ≤ UScalar.max .Usize := by
    have := hr.2; rw [hw] at this; omega
  obtain ⟨z, hz, hv⟩ := add_ok p n hsum
  exact ⟨z, hz, by rw [hv, hw]⟩

/-! ### Guarded subtraction and constant division -/

theorem guarded_sub (i c : Usize) (h : ¬ i < c) : ∃ z, (i - c : Result Usize) = ok z := by
  have hle : c.val ≤ i.val := by scalar_tac
  obtain ⟨z, hz, _⟩ := sub_ok i c hle
  exact ⟨z, hz⟩

theorem divrem_ok {ty : UScalarTy} (x d : UScalar ty) (hd : d.val ≠ 0) :
    (∃ z, (x / d : Result (UScalar ty)) = ok z) ∧ ∃ z, (x % d : Result (UScalar ty)) = ok z := by
  obtain ⟨q, hq, _⟩ := UScalar.div_spec (x:=x) (y:=d) hd
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists (UScalar.rem_spec (x:=x) (y:=d) hd)
  exact ⟨⟨q, hq⟩, ⟨r, hr⟩⟩

/-! ### Sampler loops -/

theorem post25P : AspisR1Post25Sampler.field.P.val = 2147483647 := by
  first
  | (rw [AspisR1Post25Sampler.field.P]; rfl)
  | (norm_num [AspisR1Post25Sampler.field.P, UScalar.ofNatCore_val_eq])
  | (unfold AspisR1Post25Sampler.field.P; rfl)

theorem addSmallP : AspisR1Post25SamplerIndexedAddSmallCandidate.field.P.val = 2147483647 := by
  first
  | (rw [AspisR1Post25SamplerIndexedAddSmallCandidate.field.P]; rfl)
  | (norm_num [AspisR1Post25SamplerIndexedAddSmallCandidate.field.P, UScalar.ofNatCore_val_eq])
  | (unfold AspisR1Post25SamplerIndexedAddSmallCandidate.field.P; rfl)

theorem widen_val (x : U32) : (core.convert.num.FromU64U32.from x).val = x.val := by
  change (UScalar.cast .U64 x).val = _
  rw [UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (by have := x.bv.isLt; simp only [UScalarTy.numBits] at this ⊢; omega)

theorem shl64_ok (x : U64) : ∃ z, (x <<< 32#i32 : Result U64) = ok z := by
  have h0 : 0 ≤ (32#i32).val := by decide
  have h1 : (32#i32).val < 64 := by decide
  first
  | (obtain ⟨z, hz, _⟩ := WP.spec_imp_exists (U64.ShiftLeft_IScalar_spec x (32#i32) h0 (by
        first | (rw [UScalarTy.U64_numBits_eq]; exact h1) | (simp only [UScalarTy.numBits]; exact h1) | omega))
     exact ⟨z, hz⟩)
  | (obtain ⟨z, hz, _⟩ := WP.spec_imp_exists (UScalar.ShiftLeft_IScalar_spec x (32#i32) (UScalar.size UScalarTy.U64) h0 (by
        first | (rw [UScalarTy.U64_numBits_eq]; exact h1) | (simp only [UScalarTy.numBits]; exact h1) | omega) rfl)
     exact ⟨z, hz⟩)

theorem div_pass_ops (j : Usize) (hj : j > 0#usize) (remainder dividend : U64) :
    (∃ z, (j - 1#usize : Result Usize) = ok z) ∧ (∃ z, (remainder <<< 32#i32 : Result U64) = ok z) ∧
      (∃ z, (dividend / core.convert.num.FromU64U32.from AspisR1Post25Sampler.field.P : Result U64) = ok z) ∧
      ∃ z, (dividend % core.convert.num.FromU64U32.from AspisR1Post25Sampler.field.P : Result U64) = ok z := by
  have hP : (core.convert.num.FromU64U32.from AspisR1Post25Sampler.field.P).val ≠ 0 := by
    rw [widen_val, post25P]; decide
  obtain ⟨hd, hr⟩ := divrem_ok dividend _ hP
  exact ⟨NPH_R22Loops4.usize_pos_pred_ok j hj, shl64_ok remainder, hd, hr⟩

theorem low_digits_ops (i : Usize) (hi : i < 8#usize) :
    ∃ start, (4#usize * i : Result Usize) = ok start ∧
      (∀ k : Usize, k.val ≤ 3 → ∃ z, (start + k : Result Usize) = ok z) ∧
      ∃ z, (i + 1#usize : Result Usize) = ok z ∧ z.val = i.val + 1 := by
  have hiv : i.val < 8 := by scalar_tac
  have h4 : (4#usize : Usize).val = 4 := by first | rfl | simp
  have big : 1000 ≤ UScalar.max .Usize := by scalar_tac
  obtain ⟨st, hst, vst⟩ := mul_ok (4#usize) i (by rw [h4]; omega)
  refine ⟨st, hst, fun k hk => ?_, NPH_R22Loops.usize_succ_ok i 8#usize (by scalar_tac)⟩
  obtain ⟨z, hz, _⟩ := add_ok st k (by rw [vst, h4]; omega)
  exact ⟨z, hz⟩

theorem add_small_ops (i : Usize) (hi : i < 8#usize) (digit addend : U32) :
    ∃ sum, (core.convert.num.FromU64U32.from digit + core.convert.num.FromU64U32.from addend :
        Result U64) = ok sum ∧
      (∃ z, (sum % core.convert.num.FromU64U32.from AspisR1Post25SamplerIndexedAddSmallCandidate.field.P :
        Result U64) = ok z) ∧
      (∃ z, (sum / core.convert.num.FromU64U32.from AspisR1Post25SamplerIndexedAddSmallCandidate.field.P :
        Result U64) = ok z) ∧
      ∃ z, (i + 1#usize : Result Usize) = ok z ∧ z.val = i.val + 1 := by
  have hd := digit.bv.isLt
  have ha := addend.bv.isLt
  have hb : (core.convert.num.FromU64U32.from digit).val + (core.convert.num.FromU64U32.from addend).val ≤
      UScalar.max .U64 := by
    rw [widen_val, widen_val, max64]
    simp only [UScalarTy.numBits] at hd ha
    have e1 : digit.val = digit.bv.toNat := rfl
    have e2 : addend.val = addend.bv.toNat := rfl
    omega
  obtain ⟨sum, hs, _⟩ := add_ok _ _ hb
  have hP : (core.convert.num.FromU64U32.from AspisR1Post25SamplerIndexedAddSmallCandidate.field.P).val ≠ 0 := by
    rw [widen_val, addSmallP]; decide
  obtain ⟨hdv, hrm⟩ := divrem_ok sum _ hP
  exact ⟨sum, hs, hrm, hdv, NPH_R22Loops.usize_succ_ok i 8#usize (by scalar_tac)⟩

/-! ### MultiproofConeRef write_parent -/

theorem update_lt {α : Type} {n : Usize} (v : Array α n) (i : Usize) (x : α) (v' : Array α n)
    (h : Array.update v i x = ok v') : i.val < v.val.length := by
  unfold Array.update at h
  split at h
  · cases h
  · rename_i value hv
    have hv' : v.val[i.val]? = some value := hv
    exact (List.getElem?_eq_some_iff.mp hv').1

theorem write_parent_ops (index : U32) (w : Usize) {α : Type} (a : Array α 16#usize) (x : α)
    (a' : Array α 16#usize) (hu : Array.update a w x = ok a') :
    (∃ z, (index / 2#u32 : Result U32) = ok z) ∧ ∃ z, (w + 1#usize : Result Usize) = ok z ∧ z.val = w.val + 1 := by
  have hl := update_lt a w x a' hu
  have hlen : a.val.length = 16 := by first | exact a.property | simpa using a.property
  obtain ⟨q, hq, _⟩ := UScalar.div_spec (x:=index) (y:=2#u32) (by decide)
  exact ⟨⟨q, hq⟩, NPH_R22Loops.usize_succ_ok w 16#usize (by rw [hlen] at hl; scalar_tac)⟩

#print axioms table_size
#print axioms prefix_shape_size
#print axioms record_size_ok
#print axioms get_success
#print axioms get_cursor_direct
#print axioms guarded_sub
#print axioms divrem_ok
#print axioms post25P
#print axioms addSmallP
#print axioms widen_val
#print axioms shl64_ok
#print axioms div_pass_ops
#print axioms low_digits_ops
#print axioms add_small_ops
#print axioms update_lt
#print axioms write_parent_ops
end AspisR1.NPH_R22Direct
