import NPH_R22Loops4
import NCO_ParserShape
import ExtractedRowShape
import NJC_ValidateArithmetic
import F3P_SliceIndex

/-! NPH_ (R22 item 2, batch 2). Lemmas about the existing gate definitions; nothing merged changes.
- TOTAL: the two executing r1_wire.row_shape copies (AspisR1PrefixAggregateParser, AspisS1NativeCompact)
  are ok for every row: the closure equates them with AspisR1RowShape.r1_wire.row_shape
  (NCO_ParserShape.source_shape, NCO_ScalarBridge.row_shape, NCO_ParserShape.prefix_shape), which is
  ok (table row) for every row (ExtractedRowShape.row_shape_eq_table).
- DIRECT, NJC_ValidateEmission validate_checkpoint_queries_loop.body: `1 <<< 18` is the constant 262144
  (NJC_ValidateArithmetic.shift) and `i + 1` runs under the body's guard i < Slice.len (usize_succ_ok).
- DIRECT, point-read chains (NCV_Reference word32/word64, OraclePortCkptAbi2Extracted word_spec):
  every `s + k` follows a successful bounds-checked read at index s + k - 1 (`point_step`), so it is
  below the slice length and cannot overflow; word_spec's shifts are u32 shifts by 8, 16, 24 (`shl_u32_ok`).
- DIRECT, OraclePortCkptAbi2Extracted e_byte (`ebyte_ops`): i / 4 and i % 4 are ok for every i,
  8 * (i % 4) ≤ 24, and the u32 shift by that amount is ok; the limb read is bounds-checked in both
  profiles. Standard axioms. -/
set_option autoImplicit false
namespace AspisR1.NPH_R22Loops5
open Aeneas Aeneas.Std Result AspisR1.NPH_R22FieldRef

theorem prefix_row_shape_total (row : U8) :
    ∃ r, AspisR1PrefixAggregateParser.r1_wire.row_shape row = ok r := by
  rw [NCO_ParserShape.source_shape]
  exact ⟨_, AspisR1.ExtractedRowShape.row_shape_eq_table row⟩

theorem compact_row_shape_total (row : U8) :
    ∃ r, AspisS1NativeCompact.r1_wire.row_shape row = ok r := by
  rw [← NCO_ScalarBridge.row_shape, NCO_ParserShape.prefix_shape, NCO_ParserShape.source_shape]
  exact ⟨_, AspisR1.ExtractedRowShape.row_shape_eq_table row⟩

theorem validate_step (i n : Usize) (h : i < n) :
    (1#u32 <<< 18#i32 : Result U32) = ok 262144#u32 ∧
      ∃ z, (i + 1#usize : Result Usize) = ok z ∧ z.val = i.val + 1 :=
  ⟨NJC_ValidateArithmetic.shift, AspisR1.NPH_R22Loops.usize_succ_ok i n (by scalar_tac)⟩

theorem slice_len_le {T : Type} (b : Slice T) : b.val.length ≤ UScalar.max .Usize := by
  first | exact b.property | (have := b.property; scalar_tac) | simpa using b.property

/-- `s + k` after a successful read at j = s + k - 1. -/
theorem point_step {T : Type} (b : Slice T) (s k j : Usize) (v : T) (hj : j.val + 1 = s.val + k.val)
    (h : Slice.index_usize b j = ok v) :
    ∃ z, (s + k : Result Usize) = ok z ∧ z.val = s.val + k.val := by
  have hr := AspisR1.F3P_SliceIndex.read b j v h
  have hlt : j.val < b.val.length := (List.getElem?_eq_some_iff.mp hr).1
  have hl := slice_len_le b
  exact add_ok s k (by omega)

theorem shl_u32_ok (x : U32) (s : I32) (h0 : 0 ≤ s.val) (h1 : s.val < 32) :
    ∃ z, (x <<< s : Result U32) = ok z := by
  first
  | (obtain ⟨z, hz, _⟩ := WP.spec_imp_exists (U32.ShiftLeft_IScalar_spec x s h0 (by
        first | (rw [UScalarTy.U32_numBits_eq]; exact h1) | (simp only [UScalarTy.numBits]; exact h1) | omega))
     exact ⟨z, hz⟩)
  | (obtain ⟨z, hz, _⟩ := WP.spec_imp_exists (UScalar.ShiftLeft_IScalar_spec x s (UScalar.size UScalarTy.U32) h0 (by
        first | (rw [UScalarTy.U32_numBits_eq]; exact h1) | (simp only [UScalarTy.numBits]; exact h1) | omega) rfl)
     exact ⟨z, hz⟩)

theorem word_spec_shifts (x : U32) :
    (∃ z, (x <<< 8#i32 : Result U32) = ok z) ∧ (∃ z, (x <<< 16#i32 : Result U32) = ok z) ∧
      (∃ z, (x <<< 24#i32 : Result U32) = ok z) :=
  ⟨shl_u32_ok x _ (by decide) (by decide), shl_u32_ok x _ (by decide) (by decide),
    shl_u32_ok x _ (by decide) (by decide)⟩

theorem ebyte_ops (i : Usize) :
    (∃ i1, (i / 4#usize : Result Usize) = ok i1) ∧
      ∃ i3, (i % 4#usize : Result Usize) = ok i3 ∧ ∃ i4, (8#usize * i3 : Result Usize) = ok i4 ∧
        ∀ x : U32, ∃ y, (x >>> i4 : Result U32) = ok y := by
  obtain ⟨j, hj, _⟩ := UScalar.div_spec (x:=i) (y:=4#usize) (by decide)
  obtain ⟨r, hr, hrv⟩ := WP.spec_imp_exists (UScalar.rem_spec (x:=i) (y:=4#usize) (by decide))
  have h4 : (4#usize : Usize).val = 4 := by first | rfl | simp
  have h8 : (8#usize : Usize).val = 8 := by first | rfl | simp
  have rlt : r.val < 4 := by rw [hrv, h4]; exact Nat.mod_lt _ (by decide)
  have hb := AspisR1.NPH_R22QRawShift.numBits_ge
  have hpow : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) hb
  have hmax : (8#usize : Usize).val * r.val ≤ UScalar.max .Usize := by
    rw [h8]
    first
    | (simp only [UScalar.max, UScalarTy.numBits]; omega)
    | (unfold UScalar.max; simp only [UScalarTy.numBits]; omega)
    | scalar_tac
  obtain ⟨m, hm, hmv⟩ := mul_ok _ _ hmax
  refine ⟨⟨j, hj⟩, r, hr, m, hm, fun x => ?_⟩
  have hs : m.val < UScalarTy.U32.numBits := by
    first | (rw [UScalarTy.U32_numBits_eq, hmv, h8]; omega) | (simp only [UScalarTy.numBits]; rw [hmv, h8]; omega)
  obtain ⟨y, hy, _⟩ := WP.spec_imp_exists (UScalar.ShiftRight_spec x m hs)
  exact ⟨y, hy⟩

#print axioms prefix_row_shape_total
#print axioms compact_row_shape_total
#print axioms validate_step
#print axioms slice_len_le
#print axioms point_step
#print axioms shl_u32_ok
#print axioms word_spec_shifts
#print axioms ebyte_ops
end AspisR1.NPH_R22Loops5
