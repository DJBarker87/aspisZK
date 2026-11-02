import PV_B3P_RawRefTail1550227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227 Result PV_B3P_Binding9227
set_option autoImplicit false
attribute [local irreducible] Array.index_usize reference_poseidon.extension_limbs
  reference_poseidon.raw_limb227 U64.wrapping_add U64.wrapping_sub U64.wrapping_mul
  core.convert.num.FromU64U32.from

theorem raw_reference_tail0_factor550 (a a1 a2 a3 : Limbs32_550) :
    (show Result Limbs64_550 from do
  let a4 : Limbs32_550 ← Array.index_usize (Array.make 4#usize [ a, a1, a2, a3 ] (PV_B3P_Length227.size4 (a) (a1) (a2) (a3))) 0#usize
  let i : U32 ← Array.index_usize a4 0#usize
  let a5 : U64 ← lift (core.convert.num.FromU64U32.from i)
  let a6 : Limbs32_550 ← Array.index_usize (Array.make 4#usize [ a, a1, a2, a3 ] (PV_B3P_Length227.size4 (a) (a1) (a2) (a3))) 1#usize
  let i1 : U32 ← Array.index_usize a6 0#usize
  let b : U64 ← lift (core.convert.num.FromU64U32.from i1)
  let a7 : Limbs32_550 ← Array.index_usize (Array.make 4#usize [ a, a1, a2, a3 ] (PV_B3P_Length227.size4 (a) (a1) (a2) (a3))) 2#usize
  let i2 : U32 ← Array.index_usize a7 0#usize
  let c : U64 ← lift (core.convert.num.FromU64U32.from i2)
  let a8 : Limbs32_550 ← Array.index_usize (Array.make 4#usize [ a, a1, a2, a3 ] (PV_B3P_Length227.size4 (a) (a1) (a2) (a3))) 3#usize
  let i3 : U32 ← Array.index_usize a8 0#usize
  let d : U64 ← lift (core.convert.num.FromU64U32.from i3)
  let i4 : U64 ← reference_poseidon.raw_limb227 0#usize a5 b c d
  let i5 : U32 ← Array.index_usize a4 1#usize
  let a9 : U64 ← lift (core.convert.num.FromU64U32.from i5)
  let i6 : U32 ← Array.index_usize a6 1#usize
  let b1 : U64 ← lift (core.convert.num.FromU64U32.from i6)
  let i7 : U32 ← Array.index_usize a7 1#usize
  let c1 : U64 ← lift (core.convert.num.FromU64U32.from i7)
  let i8 : U32 ← Array.index_usize a8 1#usize
  let d1 : U64 ← lift (core.convert.num.FromU64U32.from i8)
  let i9 : U64 ← reference_poseidon.raw_limb227 0#usize a9 b1 c1 d1
  let i10 : U32 ← Array.index_usize a4 2#usize
  let a10 : U64 ← lift (core.convert.num.FromU64U32.from i10)
  let i11 : U32 ← Array.index_usize a6 2#usize
  let b2 : U64 ← lift (core.convert.num.FromU64U32.from i11)
  let i12 : U32 ← Array.index_usize a7 2#usize
  let c2 : U64 ← lift (core.convert.num.FromU64U32.from i12)
  let i13 : U32 ← Array.index_usize a8 2#usize
  let d2 : U64 ← lift (core.convert.num.FromU64U32.from i13)
  let i14 : U64 ← reference_poseidon.raw_limb227 0#usize a10 b2 c2 d2
  let i15 : U32 ← Array.index_usize a4 3#usize
  let a11 : U64 ← lift (core.convert.num.FromU64U32.from i15)
  let i16 : U32 ← Array.index_usize a6 3#usize
  let b3 : U64 ← lift (core.convert.num.FromU64U32.from i16)
  let i17 : U32 ← Array.index_usize a7 3#usize
  let c3 : U64 ← lift (core.convert.num.FromU64U32.from i17)
  let i18 : U32 ← Array.index_usize a8 3#usize
  let d3 : U64 ← lift (core.convert.num.FromU64U32.from i18)
  let i19 : U64 ← reference_poseidon.raw_limb227 0#usize a11 b3 c3 d3
  let i20 : U32 ← Array.index_usize a4 0#usize
  let a12 : U64 ← lift (core.convert.num.FromU64U32.from i20)
  let i21 : U32 ← Array.index_usize a6 0#usize
  let b4 : U64 ← lift (core.convert.num.FromU64U32.from i21)
  let i22 : U32 ← Array.index_usize a7 0#usize
  let c4 : U64 ← lift (core.convert.num.FromU64U32.from i22)
  let i23 : U32 ← Array.index_usize a8 0#usize
  let d4 : U64 ← lift (core.convert.num.FromU64U32.from i23)
  let i24 : U64 ← reference_poseidon.raw_limb227 1#usize a12 b4 c4 d4
  let i25 : U32 ← Array.index_usize a4 1#usize
  let a13 : U64 ← lift (core.convert.num.FromU64U32.from i25)
  let i26 : U32 ← Array.index_usize a6 1#usize
  let b5 : U64 ← lift (core.convert.num.FromU64U32.from i26)
  let i27 : U32 ← Array.index_usize a7 1#usize
  let c5 : U64 ← lift (core.convert.num.FromU64U32.from i27)
  let i28 : U32 ← Array.index_usize a8 1#usize
  let d5 : U64 ← lift (core.convert.num.FromU64U32.from i28)
  let i29 : U64 ← reference_poseidon.raw_limb227 1#usize a13 b5 c5 d5
  let i30 : U32 ← Array.index_usize a4 2#usize
  let a14 : U64 ← lift (core.convert.num.FromU64U32.from i30)
  let i31 : U32 ← Array.index_usize a6 2#usize
  let b6 : U64 ← lift (core.convert.num.FromU64U32.from i31)
  let i32 : U32 ← Array.index_usize a7 2#usize
  let c6 : U64 ← lift (core.convert.num.FromU64U32.from i32)
  let i33 : U32 ← Array.index_usize a8 2#usize
  let d6 : U64 ← lift (core.convert.num.FromU64U32.from i33)
  let i34 : U64 ← reference_poseidon.raw_limb227 1#usize a14 b6 c6 d6
  let i35 : U32 ← Array.index_usize a4 3#usize
  let a15 : U64 ← lift (core.convert.num.FromU64U32.from i35)
  let i36 : U32 ← Array.index_usize a6 3#usize
  let b7 : U64 ← lift (core.convert.num.FromU64U32.from i36)
  let i37 : U32 ← Array.index_usize a7 3#usize
  let c7 : U64 ← lift (core.convert.num.FromU64U32.from i37)
  let i38 : U32 ← Array.index_usize a8 3#usize
  let d7 : U64 ← lift (core.convert.num.FromU64U32.from i38)
  let i39 : U64 ← reference_poseidon.raw_limb227 1#usize a15 b7 c7 d7
  let i40 : U32 ← Array.index_usize a4 0#usize
  let a16 : U64 ← lift (core.convert.num.FromU64U32.from i40)
  let i41 : U32 ← Array.index_usize a6 0#usize
  let b8 : U64 ← lift (core.convert.num.FromU64U32.from i41)
  let i42 : U32 ← Array.index_usize a7 0#usize
  let c8 : U64 ← lift (core.convert.num.FromU64U32.from i42)
  let i43 : U32 ← Array.index_usize a8 0#usize
  let d8 : U64 ← lift (core.convert.num.FromU64U32.from i43)
  let i44 : U64 ← reference_poseidon.raw_limb227 2#usize a16 b8 c8 d8
  let i45 : U32 ← Array.index_usize a4 1#usize
  let a17 : U64 ← lift (core.convert.num.FromU64U32.from i45)
  let i46 : U32 ← Array.index_usize a6 1#usize
  let b9 : U64 ← lift (core.convert.num.FromU64U32.from i46)
  let i47 : U32 ← Array.index_usize a7 1#usize
  let c9 : U64 ← lift (core.convert.num.FromU64U32.from i47)
  let i48 : U32 ← Array.index_usize a8 1#usize
  let d9 : U64 ← lift (core.convert.num.FromU64U32.from i48)
  let i49 : U64 ← reference_poseidon.raw_limb227 2#usize a17 b9 c9 d9
  let i50 : U32 ← Array.index_usize a4 2#usize
  let a18 : U64 ← lift (core.convert.num.FromU64U32.from i50)
  let i51 : U32 ← Array.index_usize a6 2#usize
  let b10 : U64 ← lift (core.convert.num.FromU64U32.from i51)
  let i52 : U32 ← Array.index_usize a7 2#usize
  let c10 : U64 ← lift (core.convert.num.FromU64U32.from i52)
  let i53 : U32 ← Array.index_usize a8 2#usize
  let d10 : U64 ← lift (core.convert.num.FromU64U32.from i53)
  let i54 : U64 ← reference_poseidon.raw_limb227 2#usize a18 b10 c10 d10
  let i55 : U32 ← Array.index_usize a4 3#usize
  let a19 : U64 ← lift (core.convert.num.FromU64U32.from i55)
  let i56 : U32 ← Array.index_usize a6 3#usize
  let b11 : U64 ← lift (core.convert.num.FromU64U32.from i56)
  let i57 : U32 ← Array.index_usize a7 3#usize
  let c11 : U64 ← lift (core.convert.num.FromU64U32.from i57)
  let i58 : U32 ← Array.index_usize a8 3#usize
  let d11 : U64 ← lift (core.convert.num.FromU64U32.from i58)
  let i59 : U64 ← reference_poseidon.raw_limb227 2#usize a19 b11 c11 d11
  let i60 : U32 ← Array.index_usize a4 0#usize
  let a20 : U64 ← lift (core.convert.num.FromU64U32.from i60)
  let i61 : U32 ← Array.index_usize a6 0#usize
  let b12 : U64 ← lift (core.convert.num.FromU64U32.from i61)
  let i62 : U32 ← Array.index_usize a7 0#usize
  let c12 : U64 ← lift (core.convert.num.FromU64U32.from i62)
  let i63 : U32 ← Array.index_usize a8 0#usize
  let d12 : U64 ← lift (core.convert.num.FromU64U32.from i63)
  let i64 : U64 ← reference_poseidon.raw_limb227 3#usize a20 b12 c12 d12
  let i65 : U32 ← Array.index_usize a4 1#usize
  let a21 : U64 ← lift (core.convert.num.FromU64U32.from i65)
  let i66 : U32 ← Array.index_usize a6 1#usize
  let b13 : U64 ← lift (core.convert.num.FromU64U32.from i66)
  let i67 : U32 ← Array.index_usize a7 1#usize
  let c13 : U64 ← lift (core.convert.num.FromU64U32.from i67)
  let i68 : U32 ← Array.index_usize a8 1#usize
  let d13 : U64 ← lift (core.convert.num.FromU64U32.from i68)
  let i69 : U64 ← reference_poseidon.raw_limb227 3#usize a21 b13 c13 d13
  let i70 : U32 ← Array.index_usize a4 2#usize
  let a22 : U64 ← lift (core.convert.num.FromU64U32.from i70)
  let i71 : U32 ← Array.index_usize a6 2#usize
  let b14 : U64 ← lift (core.convert.num.FromU64U32.from i71)
  let i72 : U32 ← Array.index_usize a7 2#usize
  let c14 : U64 ← lift (core.convert.num.FromU64U32.from i72)
  let i73 : U32 ← Array.index_usize a8 2#usize
  let d14 : U64 ← lift (core.convert.num.FromU64U32.from i73)
  let i74 : U64 ← reference_poseidon.raw_limb227 3#usize a22 b14 c14 d14
  let i75 : U32 ← Array.index_usize a4 3#usize
  let a23 : U64 ← lift (core.convert.num.FromU64U32.from i75)
  let i76 : U32 ← Array.index_usize a6 3#usize
  let b15 : U64 ← lift (core.convert.num.FromU64U32.from i76)
  let i77 : U32 ← Array.index_usize a7 3#usize
  let c15 : U64 ← lift (core.convert.num.FromU64U32.from i77)
  let i78 : U32 ← Array.index_usize a8 3#usize
  let d15 : U64 ← lift (core.convert.num.FromU64U32.from i78)
  let i79 : U64 ← reference_poseidon.raw_limb227 3#usize a23 b15 c15 d15
  let a24 ←
    Array.index_usize
      (Array.make 4#usize [
        (Array.make 4#usize [ i4, i9, i14, i19 ] (PV_B3P_Length227.size4 (i4) (i9) (i14) (i19)) : Array Std.U64 4#usize),
        (Array.make 4#usize [ i24, i29, i34, i39 ] (PV_B3P_Length227.size4 (i24) (i29) (i34) (i39)) : Array Std.U64 4#usize),
        (Array.make 4#usize [ i44, i49, i54, i59 ] (PV_B3P_Length227.size4 (i44) (i49) (i54) (i59)) : Array Std.U64 4#usize),
        (Array.make 4#usize [ i64, i69, i74, i79 ] (PV_B3P_Length227.size4 (i64) (i69) (i74) (i79)) : Array Std.U64 4#usize)
        ] (PV_B3P_Length227.size4 ((Array.make 4#usize [ i4, i9, i14, i19 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)) ((Array.make 4#usize [ i24, i29, i34, i39 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)) ((Array.make 4#usize [ i44, i49, i54, i59 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)) ((Array.make 4#usize [ i64, i69, i74, i79 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)))) 0#usize
  let _ : U64 ← Array.index_usize a24 0#usize
  let i80 : U64 ← reference_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND
  let _ : U64 ← Array.index_usize a24 1#usize
  let _ : U64 ← Array.index_usize a24 2#usize
  let _ : U64 ← Array.index_usize a24 3#usize
  let a25 ←
    Array.index_usize
      (Array.make 4#usize [
        (Array.make 4#usize [ i4, i9, i14, i19 ] (PV_B3P_Length227.size4 (i4) (i9) (i14) (i19)) : Array Std.U64 4#usize),
        (Array.make 4#usize [ i24, i29, i34, i39 ] (PV_B3P_Length227.size4 (i24) (i29) (i34) (i39)) : Array Std.U64 4#usize),
        (Array.make 4#usize [ i44, i49, i54, i59 ] (PV_B3P_Length227.size4 (i44) (i49) (i54) (i59)) : Array Std.U64 4#usize),
        (Array.make 4#usize [ i64, i69, i74, i79 ] (PV_B3P_Length227.size4 (i64) (i69) (i74) (i79)) : Array Std.U64 4#usize)
        ] (PV_B3P_Length227.size4 ((Array.make 4#usize [ i4, i9, i14, i19 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)) ((Array.make 4#usize [ i24, i29, i34, i39 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)) ((Array.make 4#usize [ i44, i49, i54, i59 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)) ((Array.make 4#usize [ i64, i69, i74, i79 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)))) 1#usize
  let _ : U64 ← Array.index_usize a25 0#usize
  let _ : U64 ← Array.index_usize a25 1#usize
  let _ : U64 ← Array.index_usize a25 2#usize
  let _ : U64 ← Array.index_usize a25 3#usize
  let a26 ←
    Array.index_usize
      (Array.make 4#usize [
        (Array.make 4#usize [ i4, i9, i14, i19 ] (PV_B3P_Length227.size4 (i4) (i9) (i14) (i19)) : Array Std.U64 4#usize),
        (Array.make 4#usize [ i24, i29, i34, i39 ] (PV_B3P_Length227.size4 (i24) (i29) (i34) (i39)) : Array Std.U64 4#usize),
        (Array.make 4#usize [ i44, i49, i54, i59 ] (PV_B3P_Length227.size4 (i44) (i49) (i54) (i59)) : Array Std.U64 4#usize),
        (Array.make 4#usize [ i64, i69, i74, i79 ] (PV_B3P_Length227.size4 (i64) (i69) (i74) (i79)) : Array Std.U64 4#usize)
        ] (PV_B3P_Length227.size4 ((Array.make 4#usize [ i4, i9, i14, i19 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)) ((Array.make 4#usize [ i24, i29, i34, i39 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)) ((Array.make 4#usize [ i44, i49, i54, i59 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)) ((Array.make 4#usize [ i64, i69, i74, i79 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)))) 2#usize
  let _ : U64 ← Array.index_usize a26 0#usize
  let _ : U64 ← Array.index_usize a26 1#usize
  let _ : U64 ← Array.index_usize a26 2#usize
  let _ : U64 ← Array.index_usize a26 3#usize
  let a27 ←
    Array.index_usize
      (Array.make 4#usize [
        (Array.make 4#usize [ i4, i9, i14, i19 ] (PV_B3P_Length227.size4 (i4) (i9) (i14) (i19)) : Array Std.U64 4#usize),
        (Array.make 4#usize [ i24, i29, i34, i39 ] (PV_B3P_Length227.size4 (i24) (i29) (i34) (i39)) : Array Std.U64 4#usize),
        (Array.make 4#usize [ i44, i49, i54, i59 ] (PV_B3P_Length227.size4 (i44) (i49) (i54) (i59)) : Array Std.U64 4#usize),
        (Array.make 4#usize [ i64, i69, i74, i79 ] (PV_B3P_Length227.size4 (i64) (i69) (i74) (i79)) : Array Std.U64 4#usize)
        ] (PV_B3P_Length227.size4 ((Array.make 4#usize [ i4, i9, i14, i19 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)) ((Array.make 4#usize [ i24, i29, i34, i39 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)) ((Array.make 4#usize [ i44, i49, i54, i59 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)) ((Array.make 4#usize [ i64, i69, i74, i79 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)))) 3#usize
  let _ : U64 ← Array.index_usize a27 0#usize
  let _ : U64 ← Array.index_usize a27 1#usize
  let _ : U64 ← Array.index_usize a27 2#usize
  let _ : U64 ← Array.index_usize a27 3#usize
  let i81 : U64 ← Array.index_usize a24 0#usize
  let i82 : U64 ← lift (Std.U64.wrapping_mul 5#u64 i80)
  let i83 : U64 ← lift (Std.U64.wrapping_add i81 i82)
  let i84 : U64 ← Array.index_usize a25 1#usize
  let i85 : U64 ← lift (Std.U64.wrapping_sub i83 i84)
  let i86 : U64 ← Array.index_usize a26 2#usize
  let i87 : U64 ← lift (Std.U64.wrapping_mul 2#u64 i86)
  let i88 : U64 ← lift (Std.U64.wrapping_add i85 i87)
  let i89 : U64 ← Array.index_usize a26 3#usize
  let i90 : U64 ← lift (Std.U64.wrapping_sub i88 i89)
  let i91 : U64 ← Array.index_usize a27 2#usize
  let i92 : U64 ← lift (Std.U64.wrapping_sub i90 i91)
  let i93 : U64 ← Array.index_usize a27 3#usize
  let i94 : U64 ← lift (Std.U64.wrapping_mul 2#u64 i93)
  let i95 : U64 ← lift (Std.U64.wrapping_sub i92 i94)
  let i96 : U64 ← Array.index_usize a24 1#usize
  let i97 : U64 ← Array.index_usize a25 0#usize
  let i98 : U64 ← lift (Std.U64.wrapping_add i96 i97)
  let i99 : U64 ← Array.index_usize a26 2#usize
  let i100 : U64 ← lift (Std.U64.wrapping_add i98 i99)
  let i101 : U64 ← Array.index_usize a26 3#usize
  let i102 : U64 ← lift (Std.U64.wrapping_mul 2#u64 i101)
  let i103 : U64 ← lift (Std.U64.wrapping_add i100 i102)
  let i104 : U64 ← Array.index_usize a27 2#usize
  let i105 : U64 ← lift (Std.U64.wrapping_mul 2#u64 i104)
  let i106 : U64 ← lift (Std.U64.wrapping_add i103 i105)
  let i107 : U64 ← lift (Std.U64.wrapping_add i106 i80)
  let i108 : U64 ← Array.index_usize a27 3#usize
  let i109 : U64 ← lift (Std.U64.wrapping_sub i107 i108)
  let i110 : U64 ← Array.index_usize a24 2#usize
  let i111 : U64 ← lift (Std.U64.wrapping_mul 2#u64 i80)
  let i112 : U64 ← lift (Std.U64.wrapping_add i110 i111)
  let i113 : U64 ← Array.index_usize a25 3#usize
  let i114 : U64 ← lift (Std.U64.wrapping_sub i112 i113)
  let i115 : U64 ← Array.index_usize a26 0#usize
  let i116 : U64 ← lift (Std.U64.wrapping_add i114 i115)
  let i117 : U64 ← Array.index_usize a27 1#usize
  let i118 : U64 ← lift (Std.U64.wrapping_sub i116 i117)
  let i119 : U64 ← Array.index_usize a24 3#usize
  let i120 : U64 ← Array.index_usize a25 2#usize
  let i121 : U64 ← lift (Std.U64.wrapping_add i119 i120)
  let i122 : U64 ← Array.index_usize a26 1#usize
  let i123 : U64 ← lift (Std.U64.wrapping_add i121 i122)
  let i124 : U64 ← Array.index_usize a27 0#usize
  let i125 : U64 ← lift (Std.U64.wrapping_add i123 i124)
  ok (Array.make 4#usize [ i95, i109, i118, i125 ] (PV_B3P_Length227.size4 (i95) (i109) (i118) (i125)))

    ) = raw_reference_tail0_550 a a1 a2 a3 := by
  unfold raw_reference_tail0_550
  apply bind_equal9
  intro a4
  apply bind_equal9
  intro i
  apply bind_equal9
  intro a5
  apply bind_equal9
  intro a6
  apply bind_equal9
  intro i1
  apply bind_equal9
  intro b
  apply bind_equal9
  intro a7
  apply bind_equal9
  intro i2
  apply bind_equal9
  intro c
  apply bind_equal9
  intro a8
  apply bind_equal9
  intro i3
  apply bind_equal9
  intro d
  apply bind_equal9
  intro i4
  apply bind_equal9
  intro i5
  apply bind_equal9
  intro a9
  apply bind_equal9
  intro i6
  apply bind_equal9
  intro b1
  apply bind_equal9
  intro i7
  apply bind_equal9
  intro c1
  apply bind_equal9
  intro i8
  apply bind_equal9
  intro d1
  apply bind_equal9
  intro i9
  apply bind_equal9
  intro i10
  apply bind_equal9
  intro a10
  apply bind_equal9
  intro i11
  apply bind_equal9
  intro b2
  apply bind_equal9
  intro i12
  apply bind_equal9
  intro c2
  apply bind_equal9
  intro i13
  apply bind_equal9
  intro d2
  apply bind_equal9
  intro i14
  apply bind_equal9
  intro i15
  apply bind_equal9
  intro a11
  apply bind_equal9
  intro i16
  apply bind_equal9
  intro b3
  apply bind_equal9
  intro i17
  apply bind_equal9
  intro c3
  apply bind_equal9
  intro i18
  apply bind_equal9
  intro d3
  apply bind_equal9
  intro i19
  exact raw_reference_tail1_factor550 a4 a6 a7 a8 i4 i9 i14 i19

#print axioms raw_reference_tail0_factor550
end PV_B3P_Association550227
