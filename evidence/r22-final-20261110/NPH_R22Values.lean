import NPH_R22Binary
import NPH_R22JoinCW6
import NOC_PrepareDiv
import NGV_ByteWindow
import S1ValuesOwnedInstallationV1
import S1NativeCompactModelV1

/-! NPH_ (R22, 2026-11-10 continuation, items 3 and 4). Lemmas about the existing gate definitions;
nothing merged changes.

Item 3, PRECONDITION_B, AspisS1ValuesOwned.values_owned_reference. Its checked operations are
len % 16 and len / 16 (ok for every input, NPH_R22Direct.divrem_ok) and 2 * len, which is ok with the
exact value whenever len <= 1856 (`vo_mul_ok`). The only definition referrer is
AspisS1ValuesOwnedInstallation.expandValues (NPH_REFS6.json), which passes toVec of its first
argument (`toVec_len`). Its executing call sites:
- compact expand_semantic_loop.body (the nativeValues record): the argument is
  s3 = input[i1, i1 + size / 2) with size from the compact row_shape, size <= 3712
  (`compact_shape_size`), so len s3 <= 1856 (`compact_site`).
- candidate.prepare's op11 call (the withValues record): the argument is
  proof[OFF_Y1, OFF_INACTIVE), whose length is OFF_INACTIVE - OFF_Y1 (`window_len`); every
  successful range read has length end - start, and the value used by `prepare_site` is any
  window whose length is at most 1856.
Item 4, PRECONDITION_B, AspisR1CurrentCaller.verifier.candidate.prepare. Its only checked operation
is LOGICAL_SEMANTIC + LOGICAL_Y1. At every installed configuration op15 is the constant 13831
(`installed_ls`), unchanged by the op8 replacement of NPH_R22JoinCW6 (`guarded_ls`), LOGICAL_Y1 is
928 (NOC_PrepareDiv.logical_y1), and the sum is ok with value 14759 (`prepare_add`).
Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22Values
open Aeneas Aeneas.Std Result AspisR1.NPH_R22FieldRef

/-! ### values_owned_reference -/

theorem vec_len (v : alloc.vec.Vec U8) : (alloc.vec.Vec.len v).val = v.val.length := by
  first | rfl | simp | scalar_tac

theorem vo_mul_ok (input : alloc.vec.Vec U8) (h : input.val.length ≤ 1856) :
    ∃ z, (2#usize * alloc.vec.Vec.len input : Result Usize) = ok z ∧ z.val = 2 * input.val.length := by
  have hl := vec_len input
  have h2 : (2#usize : Usize).val = 2 := by first | rfl | simp | decide
  have hmax : 4000 ≤ UScalar.max .Usize := by scalar_tac
  have hm : (2#usize : Usize).val * (alloc.vec.Vec.len input).val ≤ UScalar.max .Usize := by
    rw [h2, hl]; omega
  obtain ⟨z, hz, hv⟩ := mul_ok _ _ hm
  exact ⟨z, hz, by rw [hv, h2, hl]⟩

theorem vo_divrem_ok (input : alloc.vec.Vec U8) :
    (∃ z, (alloc.vec.Vec.len input / 16#usize : Result Usize) = ok z) ∧
      ∃ z, (alloc.vec.Vec.len input % 16#usize : Result Usize) = ok z :=
  NPH_R22Direct.divrem_ok _ _ (by first | decide | simp)

theorem toVec_len (s : Slice U8) :
    (AspisS1ValuesOwnedInstallation.toVec s).val.length = s.val.length := rfl

/-- Every successful range read [a, b) has length b - a. -/
theorem window_len (bytes out : Slice U8) (a b : Usize)
    (h : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
      { start := a, «end» := b } = ok out) :
    out.val.length = b.val - a.val := by
  have rs := AspisR1.T2Nat_RawBounds.range_success bytes out a b h
  rw [NGV_ByteWindow.read bytes a b rs] at h
  have e := Result.ok.inj h
  rw [← e, NGV_ByteWindow.select_length _ _ _ (by omega)]

theorem compact_shape_size (row : U8) (k : U8) (size : Usize)
    (h : AspisS1NativeCompact.r1_wire.row_shape row = ok (some (k, size))) : size.val ≤ 3712 := by
  rw [← NCO_ScalarBridge.row_shape, NCO_ParserShape.prefix_shape, NCO_ParserShape.source_shape,
    AspisR1.ExtractedRowShape.row_shape_eq_table row] at h
  exact NPH_R22Direct.table_size row k size (Result.ok.inj h)

/-- The compact expand site: the expandValues argument input[i1, i1 + size/2) has length <= 1856,
so the checked 2 * len inside values_owned_reference is ok. -/
theorem compact_site (input s3 : Slice U8) (row k : U8) (size i1 i2 i3 : Usize)
    (shape : AspisS1NativeCompact.r1_wire.row_shape row = ok (some (k, size)))
    (half : (size / 2#usize : Result Usize) = ok i2)
    (sum : (i1 + i2 : Result Usize) = ok i3)
    (read : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) input
      { start := i1, «end» := i3 } = ok s3) :
    s3.val.length ≤ 1856 ∧
      ∃ z, (2#usize * alloc.vec.Vec.len (AspisS1ValuesOwnedInstallation.toVec s3) : Result Usize) = ok z ∧
        z.val = 2 * s3.val.length := by
  have hs := compact_shape_size row k size shape
  obtain ⟨q, hq, vq⟩ := UScalar.div_spec (x:=size) (y:=2#usize) (by decide)
  have qi : q = i2 := Result.ok.inj (hq.symm.trans half)
  subst qi
  have h2 : (2#usize : Usize).val = 2 := by first | rfl | simp | decide
  rw [h2] at vq
  have v3 := NPH_R22Cursor.add_val i1 q i3 sum
  have hl := window_len input s3 i1 i3 read
  have small : s3.val.length ≤ 1856 := by rw [hl, v3, vq]; omega
  refine ⟨small, ?_⟩
  obtain ⟨z, hz, hv⟩ := vo_mul_ok (AspisS1ValuesOwnedInstallation.toVec s3) (by rw [toVec_len]; exact small)
  exact ⟨z, hz, by rw [hv, toVec_len]⟩

/-- The prepare op11 site: any window proof[a, b) with b - a <= 1856 makes the checked 2 * len ok. -/
theorem prepare_site (proof s2 : Slice U8) (a b : Usize) (width : b.val - a.val ≤ 1856)
    (read : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) proof
      { start := a, «end» := b } = ok s2) :
    s2.val.length ≤ 1856 ∧
      ∃ z, (2#usize * alloc.vec.Vec.len (AspisS1ValuesOwnedInstallation.toVec s2) : Result Usize) = ok z ∧
        z.val = 2 * s2.val.length := by
  have hl := window_len proof s2 a b read
  have small : s2.val.length ≤ 1856 := by rw [hl]; exact width
  obtain ⟨z, hz, hv⟩ := vo_mul_ok (AspisS1ValuesOwnedInstallation.toVec s2) (by rw [toVec_len]; exact small)
  exact ⟨small, z, hz, by rw [hv, toVec_len]⟩

/-! ### candidate.prepare: the installed op15 constant -/

theorem installed_ls {F C : Type} (cfg : AspisR1.DrvC_Installation.Configuration F C) :
    AspisR1CurrentCaller.compact.LOGICAL_SEMANTIC (AspisR1.DrvC_Installation.currentInstalled cfg) =
      ok 13831#usize := by
  unfold AspisR1CurrentCaller.compact.LOGICAL_SEMANTIC; rfl

theorem guarded_ls {F C : Type} (cfg : AspisR1.DrvC_Installation.Configuration F C) :
    AspisR1CurrentCaller.compact.LOGICAL_SEMANTIC
      { AspisR1.DrvC_Installation.currentInstalled cfg with op8 := AspisR1.NPH_R22JoinCW6.guardedOp8 } =
      ok 13831#usize := by
  rw [AspisR1.NPH_R22JoinCW6.ls_eq]; exact installed_ls cfg

/-- The only checked operation of candidate.prepare is ok at every installed configuration. -/
theorem prepare_add {F C : Type} (cfg : AspisR1.DrvC_Installation.Configuration F C) :
    AspisR1CurrentCaller.compact.LOGICAL_SEMANTIC (AspisR1.DrvC_Installation.currentInstalled cfg) =
      ok 13831#usize ∧
    AspisR1CurrentCaller.compact.LOGICAL_Y1 = ok 928#usize ∧
    ((13831#usize : Usize) + (928#usize : Usize) : Result Usize) = ok 14759#usize :=
  ⟨installed_ls cfg, AspisR1.NOC_PrepareDiv.logical_y1, AspisR1.NOC_PrepareDiv.logical_sum⟩

#print axioms vec_len
#print axioms vo_mul_ok
#print axioms vo_divrem_ok
#print axioms toVec_len
#print axioms window_len
#print axioms compact_shape_size
#print axioms compact_site
#print axioms prepare_site
#print axioms installed_ls
#print axioms guarded_ls
#print axioms prepare_add
end AspisR1.NPH_R22Values
