import Qm31PackBase4Slice
import ExtractedMaskQmPackBase4InitCopy
import ExtractedMaskQmPackBase4Fragments

/-! Composition of the exact generated length-four packer with the checked
array/copy prelude and its checked arithmetic tail. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskQmPackBase4Whole

open Aeneas.Std Result

abbrev CurrentQM := AspisR1.ExtractedMaskQM31Exact.CurrentQM
abbrev CurrentCanonicalQM := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM

def inputAt (values : Slice AspisR1SelectedMaskProbe.field.QM31)
    (hlen : values.length = 4) (j : Fin 4) : CurrentQM :=
  values.val[j.val]'(by
    have hvalues : values.val.length = 4 := by simpa using hlen
    exact Nat.lt_of_lt_of_eq j.isLt hvalues.symm)

def afterArray (a : Array AspisR1SelectedMaskProbe.field.QM31 4#usize) :
    Result CurrentQM := do
  let v0 ← Array.index_usize a 0#usize
  let v1 ← Array.index_usize a 1#usize
  let v2 ← Array.index_usize a 2#usize
  let v3 ← Array.index_usize a 3#usize
  let p ← lift (core.convert.num.FromU64U32.from AspisR1SelectedMaskProbe.field.P)
  let i2 ← AspisR1SelectedMaskProbe.field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call () v0.c0.a
  let i3 ← AspisR1SelectedMaskProbe.field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call () v1.c0.b
  let i4 ← p - i3
  let i5 ← i2 + i4
  let i6 ← AspisR1SelectedMaskProbe.field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call () v2.c1.a
  let i7 ← 2#u64 * i6
  let i8 ← i5 + i7
  let i9 ← AspisR1SelectedMaskProbe.field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call () v2.c1.b
  let i10 ← p - i9
  let i11 ← i8 + i10
  let i12 ← AspisR1SelectedMaskProbe.field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call () v3.c1.a
  let i13 ← p - i12
  let i14 ← i11 + i13
  let i15 ← 2#u64 * p
  let i16 ← AspisR1SelectedMaskProbe.field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call () v3.c1.b
  let i17 ← 2#u64 * i16
  let i18 ← i15 - i17
  let c0_a ← i14 + i18
  let i19 ← AspisR1SelectedMaskProbe.field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call () v0.c0.b
  let i20 ← AspisR1SelectedMaskProbe.field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call () v1.c0.a
  let i21 ← i19 + i20
  let i22 ← i21 + i6
  let i23 ← 2#u64 * i9
  let i24 ← i22 + i23
  let i25 ← 2#u64 * i12
  let i26 ← i24 + i25
  let i27 ← p - i16
  let c0_b ← i26 + i27
  let i28 ← AspisR1SelectedMaskProbe.field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call () v0.c1.a
  let i29 ← AspisR1SelectedMaskProbe.field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call () v1.c1.b
  let i30 ← p - i29
  let i31 ← i28 + i30
  let i32 ← AspisR1SelectedMaskProbe.field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call () v2.c0.a
  let i33 ← i31 + i32
  let i34 ← AspisR1SelectedMaskProbe.field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call () v3.c0.b
  let i35 ← p - i34
  let c1_a ← i33 + i35
  let i36 ← AspisR1SelectedMaskProbe.field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call () v0.c1.b
  let i37 ← AspisR1SelectedMaskProbe.field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call () v1.c1.a
  let i38 ← i36 + i37
  let i39 ← AspisR1SelectedMaskProbe.field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call () v2.c0.b
  let i40 ← i38 + i39
  let i41 ← AspisR1SelectedMaskProbe.field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call () v3.c0.a
  let c1_b ← i40 + i41
  let m ← AspisR1SelectedMaskProbe.field.M31.reduce_u64 c0_a
  let m1 ← AspisR1SelectedMaskProbe.field.M31.reduce_u64 c0_b
  let c ← AspisR1SelectedMaskProbe.field.CM31.new m m1
  let m2 ← AspisR1SelectedMaskProbe.field.M31.reduce_u64 c1_a
  let m3 ← AspisR1SelectedMaskProbe.field.M31.reduce_u64 c1_b
  let c1 ← AspisR1SelectedMaskProbe.field.CM31.new m2 m3
  ok ⟨c, c1⟩

theorem generated_eq_prefix_after
    (values : Slice AspisR1SelectedMaskProbe.field.QM31) :
    AspisR1SelectedMaskProbe.field.qm31_pack_base4 values = (do
      let i := Slice.len values
      massert (i ≤ 4#usize)
      let copied ← AspisR1.ExtractedMaskQmPackBase4InitCopy.copyPrefixWith
        AspisR1SelectedMaskProbe.field.QM31.ZERO
        AspisR1SelectedMaskProbe.field.QM31.Insts.CoreMarkerCopy values
      afterArray copied) := by
  simp only [AspisR1SelectedMaskProbe.field.qm31_pack_base4,
    AspisR1.ExtractedMaskQmPackBase4InitCopy.copyPrefixWith, afterArray,
    Aeneas.Std.bind_assoc_eq, bind_tc_ok]

private theorem index_input
    (a : Array AspisR1SelectedMaskProbe.field.QM31 4#usize)
    (values : Slice AspisR1SelectedMaskProbe.field.QM31)
    (ha : a.val = values.val) (i : Usize) (hi : i.val < 4) :
    Array.index_usize a i = .ok (values.val.get ⟨i.val, by
      have hvalues : values.val.length = 4 := by
        rw [← ha]
        exact a.property
      rw [hvalues]
      exact hi⟩) := by
  have hbound : i.val < a.length := by
    have := a.property
    scalar_tac
  obtain ⟨x, hx, hxval⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec a i hbound)
  have hiValues : i.val < values.val.length := by
    have hvalues : values.val.length = 4 := by
      rw [← ha]
      exact a.property
    rw [hvalues]
    exact hi
  have hxval' : x = values.val.get ⟨i.val, hiValues⟩ := by
    simpa [ha] using hxval
  exact hx.trans (congrArg Result.ok hxval')

theorem after_eq_run
    (a : Array AspisR1SelectedMaskProbe.field.QM31 4#usize)
    (values : Slice AspisR1SelectedMaskProbe.field.QM31)
    (ha : a.val = values.val) (hlen : values.length = 4) :
    afterArray a = AspisR1.ExtractedMaskQmPackBase4Tail.run (inputAt values hlen) := by
  have h0 := index_input a values ha 0#usize (by decide)
  have h1 := index_input a values ha 1#usize (by decide)
  have h2 := index_input a values ha 2#usize (by decide)
  have h3 := index_input a values ha 3#usize (by decide)
  have h0' : Array.index_usize a 0#usize = .ok (inputAt values hlen 0) := by
    simpa [inputAt] using h0
  have h1' : Array.index_usize a 1#usize = .ok (inputAt values hlen 1) := by
    simpa [inputAt] using h1
  have h2' : Array.index_usize a 2#usize = .ok (inputAt values hlen 2) := by
    simpa [inputAt] using h2
  have h3' : Array.index_usize a 3#usize = .ok (inputAt values hlen 3) := by
    simpa [inputAt] using h3
  simp only [afterArray, AspisR1.ExtractedMaskQmPackBase4Tail.run,
    h0', h1', h2', h3',
    AspisR1.ExtractedMaskQmPackBase4SourceArithmetic.limb_call_exact,
    AspisR1.ExtractedMaskQmPackBase4CheckedU64.packLimbCall_eq_cast,
    AspisR1.ExtractedMaskQmPackBase4CheckedU64.limbToU64,
    AspisR1.ExtractedMaskQmPackBase4SourceArithmetic.sourceP64,
    Aeneas.Std.lift, Aeneas.Std.bind_assoc_eq, bind_tc_ok,
    HAdd.hAdd, HSub.hSub, HMul.hMul]

theorem qm31_pack_base4_success
    (values : Slice AspisR1SelectedMaskProbe.field.QM31)
    (hlen : values.length = 4)
    (hcanonical : ∀ j : Fin 4, CurrentCanonicalQM (inputAt values hlen j)) :
    ∃ out : CurrentQM,
      AspisR1SelectedMaskProbe.field.qm31_pack_base4 values = .ok out ∧
      CurrentCanonicalQM out ∧
      AspisR1.ExtractedMaskQM31Exact.decode out =
        AspisR1.ExtractedMaskQmPackBase4Arithmetic.mathematicalPack
          (inputAt values hlen) := by
  obtain ⟨copied, hcopy, hcopied⟩ :=
    AspisR1.ExtractedMaskQmPackBase4InitCopy.copyPrefixWith_eq_source
      AspisR1SelectedMaskProbe.field.QM31.ZERO
      AspisR1SelectedMaskProbe.field.QM31.Insts.CoreMarkerCopy values hlen
  have hassert : massert (Slice.len values ≤ 4#usize) = .ok () := by
    apply (Aeneas.Std.massert_ok _).2
    have hv : (Slice.len values).val = 4 := by simp [Slice.len_val, hlen]
    scalar_tac
  have hrun := after_eq_run copied values hcopied hlen
  have hprefix :
      (do
        let i := Slice.len values
        massert (i ≤ 4#usize)
        let copied ← AspisR1.ExtractedMaskQmPackBase4InitCopy.copyPrefixWith
          AspisR1SelectedMaskProbe.field.QM31.ZERO
          AspisR1SelectedMaskProbe.field.QM31.Insts.CoreMarkerCopy values
        afterArray copied) =
      AspisR1.ExtractedMaskQmPackBase4Tail.run (inputAt values hlen) := by
    simp only [hassert, hcopy, hrun, bind_tc_ok]
  rw [generated_eq_prefix_after, hprefix]
  obtain ⟨out, hout, hcanon, hdecode⟩ :=
    AspisR1.ExtractedMaskQmPackBase4Fragments.run_success
      (inputAt values hlen) hcanonical
  exact ⟨out, hout, hcanon, hdecode⟩

#print axioms qm31_pack_base4_success
end AspisR1.ExtractedMaskQmPackBase4Whole
