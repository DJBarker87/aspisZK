import PV_B3P_P227_00
import PV_B3P_LiftHeadEq9227
import PV_B3P_Index3_100227
import PV_B3P_Index3_101227
import PV_B3P_Index3_102227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

def accumulate_pure_storage10 (sums : Array (Array U64 3#usize) 3#usize)
    (right : aspis_core.field.QM31) (left : reference_field.PreparedQm31Multiplier) : Result (Array (Array U64 3#usize) 3#usize) := do
  let right_sum ← aspis_core.field.CM31.add right.c0 right.c1
  let m ← aspis_core.field.M31.add right.c0.a right.c0.b
  let m1 ← aspis_core.field.M31.add right.c1.a right.c1.b
  let m2 ← aspis_core.field.M31.add right_sum.a right_sum.b
  let a := get3_0 left.components
  let m3 := get3_0 a
  let i := (UScalar.cast .U64 m3)
  let a1 := get3_0 (Array.make 3#usize [
        (Array.make 3#usize [ right.c0.a, right.c0.b, m ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array
        aspis_core.field.M31 3#usize),
        (Array.make 3#usize [ right.c1.a, right.c1.b, m1 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array
        aspis_core.field.M31 3#usize),
        (Array.make 3#usize [ right_sum.a, right_sum.b, m2 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array
        aspis_core.field.M31 3#usize)
        ] (by simp only [List.length_cons,List.length_nil]; rfl))
  let m4 := get3_0 a1
  let i1 := (UScalar.cast .U64 m4)
  let i2 := (Std.U64.wrapping_mul i i1)
  let a2 := get3_0 sums
  let i3 := get3_0 a2
  let i4 := (Std.U64.wrapping_add i3 i2)
  let (a3, index_mut_back) := (get3_0 sums,Aeneas.Std.Array.set sums 0#usize)
  let a4 := Aeneas.Std.Array.set a3 0#usize i4
  let m5 := get3_1 a
  let i5 := (UScalar.cast .U64 m5)
  let m6 := get3_1 a1
  let i6 := (UScalar.cast .U64 m6)
  let i7 := (Std.U64.wrapping_mul i5 i6)
  let sums1 := index_mut_back a4
  let a5 := get3_0 sums1
  let i8 := get3_1 a5
  let i9 := (Std.U64.wrapping_add i8 i7)
  let (a6, index_mut_back1) := (get3_0 sums1,Aeneas.Std.Array.set sums1 0#usize)
  let a7 := Aeneas.Std.Array.set a6 1#usize i9
  let m7 := get3_2 a
  let i10 := (UScalar.cast .U64 m7)
  let m8 := get3_2 a1
  let i11 := (UScalar.cast .U64 m8)
  let i12 := (Std.U64.wrapping_mul i10 i11)
  let sums2 := index_mut_back1 a7
  let a8 := get3_0 sums2
  let i13 := get3_2 a8
  let i14 := (Std.U64.wrapping_add i13 i12)
  let (a9, index_mut_back2) := (get3_0 sums2,Aeneas.Std.Array.set sums2 0#usize)
  let a10 := Aeneas.Std.Array.set a9 2#usize i14
  let a11 := get3_1 left.components
  let m9 := get3_0 a11
  let i15 := (UScalar.cast .U64 m9)
  let a12 := get3_1 (Array.make 3#usize [
        (Array.make 3#usize [ right.c0.a, right.c0.b, m ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array
        aspis_core.field.M31 3#usize),
        (Array.make 3#usize [ right.c1.a, right.c1.b, m1 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array
        aspis_core.field.M31 3#usize),
        (Array.make 3#usize [ right_sum.a, right_sum.b, m2 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array
        aspis_core.field.M31 3#usize)
        ] (by simp only [List.length_cons,List.length_nil]; rfl))
  let m10 := get3_0 a12
  let i16 := (UScalar.cast .U64 m10)
  let i17 := (Std.U64.wrapping_mul i15 i16)
  let sums3 := index_mut_back2 a10
  let a13 := get3_1 sums3
  let i18 := get3_0 a13
  let i19 := (Std.U64.wrapping_add i18 i17)
  let (a14, index_mut_back3) := (get3_1 sums3,Aeneas.Std.Array.set sums3 1#usize)
  let a15 := Aeneas.Std.Array.set a14 0#usize i19
  let m11 := get3_1 a11
  let i20 := (UScalar.cast .U64 m11)
  let m12 := get3_1 a12
  let i21 := (UScalar.cast .U64 m12)
  let i22 := (Std.U64.wrapping_mul i20 i21)
  let sums4 := index_mut_back3 a15
  let a16 := get3_1 sums4
  let i23 := get3_1 a16
  let i24 := (Std.U64.wrapping_add i23 i22)
  let (a17, index_mut_back4) := (get3_1 sums4,Aeneas.Std.Array.set sums4 1#usize)
  let a18 := Aeneas.Std.Array.set a17 1#usize i24
  let m13 := get3_2 a11
  let i25 := (UScalar.cast .U64 m13)
  let m14 := get3_2 a12
  let i26 := (UScalar.cast .U64 m14)
  let i27 := (Std.U64.wrapping_mul i25 i26)
  let sums5 := index_mut_back4 a18
  let a19 := get3_1 sums5
  let i28 := get3_2 a19
  let i29 := (Std.U64.wrapping_add i28 i27)
  let (a20, index_mut_back5) := (get3_1 sums5,Aeneas.Std.Array.set sums5 1#usize)
  let a21 := Aeneas.Std.Array.set a20 2#usize i29
  let a22 := get3_2 left.components
  let m15 := get3_0 a22
  let i30 := (UScalar.cast .U64 m15)
  let a23 := get3_2 (Array.make 3#usize [
        (Array.make 3#usize [ right.c0.a, right.c0.b, m ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array
        aspis_core.field.M31 3#usize),
        (Array.make 3#usize [ right.c1.a, right.c1.b, m1 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array
        aspis_core.field.M31 3#usize),
        (Array.make 3#usize [ right_sum.a, right_sum.b, m2 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array
        aspis_core.field.M31 3#usize)
        ] (by simp only [List.length_cons,List.length_nil]; rfl))
  let m16 := get3_0 a23
  let i31 := (UScalar.cast .U64 m16)
  let i32 := (Std.U64.wrapping_mul i30 i31)
  let sums6 := index_mut_back5 a21
  let a24 := get3_2 sums6
  let i33 := get3_0 a24
  let i34 := (Std.U64.wrapping_add i33 i32)
  let (a25, index_mut_back6) := (get3_2 sums6,Aeneas.Std.Array.set sums6 2#usize)
  let a26 := Aeneas.Std.Array.set a25 0#usize i34
  let m17 := get3_1 a22
  let i35 := (UScalar.cast .U64 m17)
  let m18 := get3_1 a23
  let i36 := (UScalar.cast .U64 m18)
  let i37 := (Std.U64.wrapping_mul i35 i36)
  let sums7 := index_mut_back6 a26
  let a27 := get3_2 sums7
  let i38 := get3_1 a27
  let i39 := (Std.U64.wrapping_add i38 i37)
  let (a28, index_mut_back7) := (get3_2 sums7,Aeneas.Std.Array.set sums7 2#usize)
  let a29 := Aeneas.Std.Array.set a28 1#usize i39
  let m19 := get3_2 a22
  let i40 := (UScalar.cast .U64 m19)
  let m20 := get3_2 a23
  let i41 := (UScalar.cast .U64 m20)
  let i42 := (Std.U64.wrapping_mul i40 i41)
  let sums8 := index_mut_back7 a29
  let a30 := get3_2 sums8
  let i43 := get3_2 a30
  let i44 := (Std.U64.wrapping_add i43 i42)
  let (a31, index_mut_back8) := (get3_2 sums8,Aeneas.Std.Array.set sums8 2#usize)
  let a32 := Aeneas.Std.Array.set a31 2#usize i44
  ok (index_mut_back8 a32)

attribute [local irreducible] aspis_core.field.CM31.add aspis_core.field.M31.add UScalar.cast U64.wrapping_add U64.wrapping_mul Aeneas.Std.Array.set get3_0 get3_1 get3_2

theorem accumulate_storage_binding10 (sums : Array (Array U64 3#usize) 3#usize)
    (right : aspis_core.field.QM31) (left : reference_field.PreparedQm31Multiplier) :
    reference_field.accumulate_prepared227 sums right left = accumulate_pure_storage10 sums right left := by
  unfold reference_field.accumulate_prepared227 accumulate_pure_storage10
  apply bind_equal9
  intro right_sum
  apply bind_equal9
  intro m
  apply bind_equal9
  intro m1
  apply bind_equal9
  intro m2
  rw [index3_0]
  apply equal_ok_head9
  rw [index3_0]
  apply equal_ok_head9
  apply lift_head_equal9 (UScalar.cast .U64 m3)
  rw [index3_0]
  apply equal_ok_head9
  rw [index3_0]
  apply equal_ok_head9
  apply lift_head_equal9 (UScalar.cast .U64 m4)
  apply lift_head_equal9 (Std.U64.wrapping_mul i i1)
  rw [index3_0]
  apply equal_ok_head9
  rw [index3_0]
  apply equal_ok_head9
  apply lift_head_equal9 (Std.U64.wrapping_add i3 i2)
  rw [borrow3_0]
  apply equal_ok_head9
  rw [update3_0]
  apply equal_ok_head9
  rw [index3_1]
  apply equal_ok_head9
  apply lift_head_equal9 (UScalar.cast .U64 m5)
  rw [index3_1]
  apply equal_ok_head9
  apply lift_head_equal9 (UScalar.cast .U64 m6)
  apply lift_head_equal9 (Std.U64.wrapping_mul i5 i6)
  rw [index3_0]
  apply equal_ok_head9
  rw [index3_1]
  apply equal_ok_head9
  apply lift_head_equal9 (Std.U64.wrapping_add i8 i7)
  rw [borrow3_0]
  apply equal_ok_head9
  rw [update3_1]
  apply equal_ok_head9
  rw [index3_2]
  apply equal_ok_head9
  apply lift_head_equal9 (UScalar.cast .U64 m7)
  rw [index3_2]
  apply equal_ok_head9
  apply lift_head_equal9 (UScalar.cast .U64 m8)
  apply lift_head_equal9 (Std.U64.wrapping_mul i10 i11)
  rw [index3_0]
  apply equal_ok_head9
  rw [index3_2]
  apply equal_ok_head9
  apply lift_head_equal9 (Std.U64.wrapping_add i13 i12)
  rw [borrow3_0]
  apply equal_ok_head9
  rw [update3_2]
  apply equal_ok_head9
  rw [index3_1]
  apply equal_ok_head9
  rw [index3_0]
  apply equal_ok_head9
  apply lift_head_equal9 (UScalar.cast .U64 m9)
  rw [index3_1]
  apply equal_ok_head9
  rw [index3_0]
  apply equal_ok_head9
  apply lift_head_equal9 (UScalar.cast .U64 m10)
  apply lift_head_equal9 (Std.U64.wrapping_mul i15 i16)
  rw [index3_1]
  apply equal_ok_head9
  rw [index3_0]
  apply equal_ok_head9
  apply lift_head_equal9 (Std.U64.wrapping_add i18 i17)
  rw [borrow3_1]
  apply equal_ok_head9
  rw [update3_0]
  apply equal_ok_head9
  rw [index3_1]
  apply equal_ok_head9
  apply lift_head_equal9 (UScalar.cast .U64 m11)
  rw [index3_1]
  apply equal_ok_head9
  apply lift_head_equal9 (UScalar.cast .U64 m12)
  apply lift_head_equal9 (Std.U64.wrapping_mul i20 i21)
  rw [index3_1]
  apply equal_ok_head9
  rw [index3_1]
  apply equal_ok_head9
  apply lift_head_equal9 (Std.U64.wrapping_add i23 i22)
  rw [borrow3_1]
  apply equal_ok_head9
  rw [update3_1]
  apply equal_ok_head9
  rw [index3_2]
  apply equal_ok_head9
  apply lift_head_equal9 (UScalar.cast .U64 m13)
  rw [index3_2]
  apply equal_ok_head9
  apply lift_head_equal9 (UScalar.cast .U64 m14)
  apply lift_head_equal9 (Std.U64.wrapping_mul i25 i26)
  rw [index3_1]
  apply equal_ok_head9
  rw [index3_2]
  apply equal_ok_head9
  apply lift_head_equal9 (Std.U64.wrapping_add i28 i27)
  rw [borrow3_1]
  apply equal_ok_head9
  rw [update3_2]
  apply equal_ok_head9
  rw [index3_2]
  apply equal_ok_head9
  rw [index3_0]
  apply equal_ok_head9
  apply lift_head_equal9 (UScalar.cast .U64 m15)
  rw [index3_2]
  apply equal_ok_head9
  rw [index3_0]
  apply equal_ok_head9
  apply lift_head_equal9 (UScalar.cast .U64 m16)
  apply lift_head_equal9 (Std.U64.wrapping_mul i30 i31)
  rw [index3_2]
  apply equal_ok_head9
  rw [index3_0]
  apply equal_ok_head9
  apply lift_head_equal9 (Std.U64.wrapping_add i33 i32)
  rw [borrow3_2]
  apply equal_ok_head9
  rw [update3_0]
  apply equal_ok_head9
  rw [index3_1]
  apply equal_ok_head9
  apply lift_head_equal9 (UScalar.cast .U64 m17)
  rw [index3_1]
  apply equal_ok_head9
  apply lift_head_equal9 (UScalar.cast .U64 m18)
  apply lift_head_equal9 (Std.U64.wrapping_mul i35 i36)
  rw [index3_2]
  apply equal_ok_head9
  rw [index3_1]
  apply equal_ok_head9
  apply lift_head_equal9 (Std.U64.wrapping_add i38 i37)
  rw [borrow3_2]
  apply equal_ok_head9
  rw [update3_1]
  apply equal_ok_head9
  rw [index3_2]
  apply equal_ok_head9
  apply lift_head_equal9 (UScalar.cast .U64 m19)
  rw [index3_2]
  apply equal_ok_head9
  apply lift_head_equal9 (UScalar.cast .U64 m20)
  apply lift_head_equal9 (Std.U64.wrapping_mul i40 i41)
  rw [index3_2]
  apply equal_ok_head9
  rw [index3_2]
  apply equal_ok_head9
  apply lift_head_equal9 (Std.U64.wrapping_add i43 i42)
  rw [borrow3_2]
  apply equal_ok_head9
  rw [update3_2]
  apply equal_ok_head9
  rfl

#print axioms accumulate_storage_binding10
end PV_B3P_Binding10227
