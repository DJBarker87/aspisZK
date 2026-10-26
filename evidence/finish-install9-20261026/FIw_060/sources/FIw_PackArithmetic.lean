import FIv_Arithmetic
import ExtractedMaskQmPackBase4Whole
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_PackArithmetic
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic
open FIv_Map (map map_bind map_ok)

def array {N : Usize} (a : Array NQ N) : Array PQ N :=
  ⟨a.val.map qm,by simpa only [List.length_map] using a.property⟩

theorem index {N : Usize} (a : Array NQ N) (i : Usize) :
    map qm (Array.index_usize a i)=Array.index_usize (array a) i := by
  simp only [Array.index_usize,Array.getElem?_Usize_eq,array,List.getElem?_map]
  cases a.val[i.val]? <;> rfl

def afterArray (a : Array NQ 4#usize) : Result NQ := do
  let v0 ← Array.index_usize a 0#usize
  let v1 ← Array.index_usize a 1#usize
  let v2 ← Array.index_usize a 2#usize
  let v3 ← Array.index_usize a 3#usize
  let p ← lift (core.convert.num.FromU64U32.from field.P)
  let i2 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v0.c0.a
  let i3 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v1.c0.b
  let i4 ← p - i3
  let i5 ← i2 + i4
  let i6 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v2.c1.a
  let i7 ← 2#u64 * i6
  let i8 ← i5 + i7
  let i9 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v2.c1.b
  let i10 ← p - i9
  let i11 ← i8 + i10
  let i12 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v3.c1.a
  let i13 ← p - i12
  let i14 ← i11 + i13
  let i15 ← 2#u64 * p
  let i16 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v3.c1.b
  let i17 ← 2#u64 * i16
  let i18 ← i15 - i17
  let c0_a ← i14 + i18
  let i19 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v0.c0.b
  let i20 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v1.c0.a
  let i21 ← i19 + i20
  let i22 ← i21 + i6
  let i23 ← 2#u64 * i9
  let i24 ← i22 + i23
  let i25 ← 2#u64 * i12
  let i26 ← i24 + i25
  let i27 ← p - i16
  let c0_b ← i26 + i27
  let i28 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v0.c1.a
  let i29 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v1.c1.b
  let i30 ← p - i29
  let i31 ← i28 + i30
  let i32 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v2.c0.a
  let i33 ← i31 + i32
  let i34 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v3.c0.b
  let i35 ← p - i34
  let c1_a ← i33 + i35
  let i36 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v0.c1.b
  let i37 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v1.c1.a
  let i38 ← i36 + i37
  let i39 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v2.c0.b
  let i40 ← i38 + i39
  let i41 ←
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call ()
      v3.c0.a
  let c1_b ← i40 + i41
  let m ← field.M31.reduce_u64 c0_a
  let m1 ← field.M31.reduce_u64 c0_b
  let c ← field.CM31.new m m1
  let m2 ← field.M31.reduce_u64 c1_a
  let m3 ← field.M31.reduce_u64 c1_b
  let c1 ← field.CM31.new m2 m3
  ok { c0 := c, c1 }

theorem cm_new (a b : U32) : map cm (field.CM31.new a b)=
    AspisR1SelectedMaskProbe.field.CM31.new a b := rfl

theorem mapped (a : Array NQ 4#usize) : map qm (afterArray a)=
    ExtractedMaskQmPackBase4Whole.afterArray (array a) := by
  simp only [afterArray,ExtractedMaskQmPackBase4Whole.afterArray,
    ← index,bind_map,map_bind,map_ok,
    field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call,
    AspisR1SelectedMaskProbe.field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call,
    field.P,AspisR1SelectedMaskProbe.field.P,
    ← m31_reduce,← cm_new,qm,cm,bind_tc_ok]

#print axioms index
#print axioms cm_new
#print axioms mapped
end AspisR1.FIw_PackArithmetic
end
