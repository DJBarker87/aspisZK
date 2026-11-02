import PV_B3P_RawSuffix550227
import PV_B3P_P227_03d
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227 Result
set_option autoImplicit false

attribute [local irreducible] Array.index_usize reference_poseidon.extension_limbs
  reference_poseidon.raw_limb227 U64.wrapping_add U64.wrapping_sub U64.wrapping_mul
  core.convert.num.FromU64U32.from

def raw_reference_tail4_550 (i4 i9 i14 i19 i24 i29 i34 i39 i44 i49 i54 i59 i64 i69 i74 i79 : U64) : Result Limbs64_550 := do
  let a24 ←
    Array.index_usize
      (Array.make 4#usize [
        (Array.make 4#usize [ i4, i9, i14, i19 ] (PV_B3P_Length227.size4 (i4) (i9) (i14) (i19)) : Array Std.U64 4#usize),
        (Array.make 4#usize [ i24, i29, i34, i39 ] (PV_B3P_Length227.size4 (i24) (i29) (i34) (i39)) : Array Std.U64 4#usize),
        (Array.make 4#usize [ i44, i49, i54, i59 ] (PV_B3P_Length227.size4 (i44) (i49) (i54) (i59)) : Array Std.U64 4#usize),
        (Array.make 4#usize [ i64, i69, i74, i79 ] (PV_B3P_Length227.size4 (i64) (i69) (i74) (i79)) : Array Std.U64 4#usize)
        ] (PV_B3P_Length227.size4 ((Array.make 4#usize [ i4, i9, i14, i19 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)) ((Array.make 4#usize [ i24, i29, i34, i39 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)) ((Array.make 4#usize [ i44, i49, i54, i59 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)) ((Array.make 4#usize [ i64, i69, i74, i79 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)))) 0#usize
  let _ ← Array.index_usize a24 0#usize
  let i80 ← reference_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND
  let _ ← Array.index_usize a24 1#usize
  let _ ← Array.index_usize a24 2#usize
  let _ ← Array.index_usize a24 3#usize
  let a25 ←
    Array.index_usize
      (Array.make 4#usize [
        (Array.make 4#usize [ i4, i9, i14, i19 ] (PV_B3P_Length227.size4 (i4) (i9) (i14) (i19)) : Array Std.U64 4#usize),
        (Array.make 4#usize [ i24, i29, i34, i39 ] (PV_B3P_Length227.size4 (i24) (i29) (i34) (i39)) : Array Std.U64 4#usize),
        (Array.make 4#usize [ i44, i49, i54, i59 ] (PV_B3P_Length227.size4 (i44) (i49) (i54) (i59)) : Array Std.U64 4#usize),
        (Array.make 4#usize [ i64, i69, i74, i79 ] (PV_B3P_Length227.size4 (i64) (i69) (i74) (i79)) : Array Std.U64 4#usize)
        ] (PV_B3P_Length227.size4 ((Array.make 4#usize [ i4, i9, i14, i19 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)) ((Array.make 4#usize [ i24, i29, i34, i39 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)) ((Array.make 4#usize [ i44, i49, i54, i59 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)) ((Array.make 4#usize [ i64, i69, i74, i79 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)))) 1#usize
  let _ ← Array.index_usize a25 0#usize
  let _ ← Array.index_usize a25 1#usize
  let _ ← Array.index_usize a25 2#usize
  let _ ← Array.index_usize a25 3#usize
  let a26 ←
    Array.index_usize
      (Array.make 4#usize [
        (Array.make 4#usize [ i4, i9, i14, i19 ] (PV_B3P_Length227.size4 (i4) (i9) (i14) (i19)) : Array Std.U64 4#usize),
        (Array.make 4#usize [ i24, i29, i34, i39 ] (PV_B3P_Length227.size4 (i24) (i29) (i34) (i39)) : Array Std.U64 4#usize),
        (Array.make 4#usize [ i44, i49, i54, i59 ] (PV_B3P_Length227.size4 (i44) (i49) (i54) (i59)) : Array Std.U64 4#usize),
        (Array.make 4#usize [ i64, i69, i74, i79 ] (PV_B3P_Length227.size4 (i64) (i69) (i74) (i79)) : Array Std.U64 4#usize)
        ] (PV_B3P_Length227.size4 ((Array.make 4#usize [ i4, i9, i14, i19 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)) ((Array.make 4#usize [ i24, i29, i34, i39 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)) ((Array.make 4#usize [ i44, i49, i54, i59 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)) ((Array.make 4#usize [ i64, i69, i74, i79 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)))) 2#usize
  let _ ← Array.index_usize a26 0#usize
  let _ ← Array.index_usize a26 1#usize
  let _ ← Array.index_usize a26 2#usize
  let _ ← Array.index_usize a26 3#usize
  let a27 ←
    Array.index_usize
      (Array.make 4#usize [
        (Array.make 4#usize [ i4, i9, i14, i19 ] (PV_B3P_Length227.size4 (i4) (i9) (i14) (i19)) : Array Std.U64 4#usize),
        (Array.make 4#usize [ i24, i29, i34, i39 ] (PV_B3P_Length227.size4 (i24) (i29) (i34) (i39)) : Array Std.U64 4#usize),
        (Array.make 4#usize [ i44, i49, i54, i59 ] (PV_B3P_Length227.size4 (i44) (i49) (i54) (i59)) : Array Std.U64 4#usize),
        (Array.make 4#usize [ i64, i69, i74, i79 ] (PV_B3P_Length227.size4 (i64) (i69) (i74) (i79)) : Array Std.U64 4#usize)
        ] (PV_B3P_Length227.size4 ((Array.make 4#usize [ i4, i9, i14, i19 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)) ((Array.make 4#usize [ i24, i29, i34, i39 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)) ((Array.make 4#usize [ i44, i49, i54, i59 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)) ((Array.make 4#usize [ i64, i69, i74, i79 ] (by simp only [List.length_cons,List.length_nil]; rfl) : Array Std.U64 4#usize)))) 3#usize
  let _ ← Array.index_usize a27 0#usize
  let _ ← Array.index_usize a27 1#usize
  let _ ← Array.index_usize a27 2#usize
  let _ ← Array.index_usize a27 3#usize
  let i81 ← Array.index_usize a24 0#usize
  let i82 ← lift (Std.U64.wrapping_mul 5#u64 i80)
  let i83 ← lift (Std.U64.wrapping_add i81 i82)
  let i84 ← Array.index_usize a25 1#usize
  let i85 ← lift (Std.U64.wrapping_sub i83 i84)
  let i86 ← Array.index_usize a26 2#usize
  let i87 ← lift (Std.U64.wrapping_mul 2#u64 i86)
  let i88 ← lift (Std.U64.wrapping_add i85 i87)
  let i89 ← Array.index_usize a26 3#usize
  let i90 ← lift (Std.U64.wrapping_sub i88 i89)
  let i91 ← Array.index_usize a27 2#usize
  let i92 ← lift (Std.U64.wrapping_sub i90 i91)
  let i93 ← Array.index_usize a27 3#usize
  let i94 ← lift (Std.U64.wrapping_mul 2#u64 i93)
  let i95 ← lift (Std.U64.wrapping_sub i92 i94)
  let i96 ← Array.index_usize a24 1#usize
  let i97 ← Array.index_usize a25 0#usize
  let i98 ← lift (Std.U64.wrapping_add i96 i97)
  let i99 ← Array.index_usize a26 2#usize
  let i100 ← lift (Std.U64.wrapping_add i98 i99)
  let i101 ← Array.index_usize a26 3#usize
  let i102 ← lift (Std.U64.wrapping_mul 2#u64 i101)
  let i103 ← lift (Std.U64.wrapping_add i100 i102)
  let i104 ← Array.index_usize a27 2#usize
  let i105 ← lift (Std.U64.wrapping_mul 2#u64 i104)
  let i106 ← lift (Std.U64.wrapping_add i103 i105)
  let i107 ← lift (Std.U64.wrapping_add i106 i80)
  let i108 ← Array.index_usize a27 3#usize
  let i109 ← lift (Std.U64.wrapping_sub i107 i108)
  let i110 ← Array.index_usize a24 2#usize
  let i111 ← lift (Std.U64.wrapping_mul 2#u64 i80)
  let i112 ← lift (Std.U64.wrapping_add i110 i111)
  let i113 ← Array.index_usize a25 3#usize
  let i114 ← lift (Std.U64.wrapping_sub i112 i113)
  let i115 ← Array.index_usize a26 0#usize
  let i116 ← lift (Std.U64.wrapping_add i114 i115)
  let i117 ← Array.index_usize a27 1#usize
  let i118 ← lift (Std.U64.wrapping_sub i116 i117)
  let i119 ← Array.index_usize a24 3#usize
  let i120 ← Array.index_usize a25 2#usize
  let i121 ← lift (Std.U64.wrapping_add i119 i120)
  let i122 ← Array.index_usize a26 1#usize
  let i123 ← lift (Std.U64.wrapping_add i121 i122)
  let i124 ← Array.index_usize a27 0#usize
  let i125 ← lift (Std.U64.wrapping_add i123 i124)
  ok (Array.make 4#usize [ i95, i109, i118, i125 ] (PV_B3P_Length227.size4 (i95) (i109) (i118) (i125)))

def raw_reference_tail3_550 (a4 a6 a7 a8 : Limbs32_550) (i4 i9 i14 i19 i24 i29 i34 i39 i44 i49 i54 i59 : U64) : Result Limbs64_550 := do
  let i60 ← Array.index_usize a4 0#usize
  let a20 ← lift (core.convert.num.FromU64U32.from i60)
  let i61 ← Array.index_usize a6 0#usize
  let b12 ← lift (core.convert.num.FromU64U32.from i61)
  let i62 ← Array.index_usize a7 0#usize
  let c12 ← lift (core.convert.num.FromU64U32.from i62)
  let i63 ← Array.index_usize a8 0#usize
  let d12 ← lift (core.convert.num.FromU64U32.from i63)
  let i64 ← reference_poseidon.raw_limb227 3#usize a20 b12 c12 d12
  let i65 ← Array.index_usize a4 1#usize
  let a21 ← lift (core.convert.num.FromU64U32.from i65)
  let i66 ← Array.index_usize a6 1#usize
  let b13 ← lift (core.convert.num.FromU64U32.from i66)
  let i67 ← Array.index_usize a7 1#usize
  let c13 ← lift (core.convert.num.FromU64U32.from i67)
  let i68 ← Array.index_usize a8 1#usize
  let d13 ← lift (core.convert.num.FromU64U32.from i68)
  let i69 ← reference_poseidon.raw_limb227 3#usize a21 b13 c13 d13
  let i70 ← Array.index_usize a4 2#usize
  let a22 ← lift (core.convert.num.FromU64U32.from i70)
  let i71 ← Array.index_usize a6 2#usize
  let b14 ← lift (core.convert.num.FromU64U32.from i71)
  let i72 ← Array.index_usize a7 2#usize
  let c14 ← lift (core.convert.num.FromU64U32.from i72)
  let i73 ← Array.index_usize a8 2#usize
  let d14 ← lift (core.convert.num.FromU64U32.from i73)
  let i74 ← reference_poseidon.raw_limb227 3#usize a22 b14 c14 d14
  let i75 ← Array.index_usize a4 3#usize
  let a23 ← lift (core.convert.num.FromU64U32.from i75)
  let i76 ← Array.index_usize a6 3#usize
  let b15 ← lift (core.convert.num.FromU64U32.from i76)
  let i77 ← Array.index_usize a7 3#usize
  let c15 ← lift (core.convert.num.FromU64U32.from i77)
  let i78 ← Array.index_usize a8 3#usize
  let d15 ← lift (core.convert.num.FromU64U32.from i78)
  let i79 ← reference_poseidon.raw_limb227 3#usize a23 b15 c15 d15
  raw_reference_tail4_550 i4 i9 i14 i19 i24 i29 i34 i39 i44 i49 i54 i59 i64 i69 i74 i79

def raw_reference_tail2_550 (a4 a6 a7 a8 : Limbs32_550) (i4 i9 i14 i19 i24 i29 i34 i39 : U64) : Result Limbs64_550 := do
  let i40 ← Array.index_usize a4 0#usize
  let a16 ← lift (core.convert.num.FromU64U32.from i40)
  let i41 ← Array.index_usize a6 0#usize
  let b8 ← lift (core.convert.num.FromU64U32.from i41)
  let i42 ← Array.index_usize a7 0#usize
  let c8 ← lift (core.convert.num.FromU64U32.from i42)
  let i43 ← Array.index_usize a8 0#usize
  let d8 ← lift (core.convert.num.FromU64U32.from i43)
  let i44 ← reference_poseidon.raw_limb227 2#usize a16 b8 c8 d8
  let i45 ← Array.index_usize a4 1#usize
  let a17 ← lift (core.convert.num.FromU64U32.from i45)
  let i46 ← Array.index_usize a6 1#usize
  let b9 ← lift (core.convert.num.FromU64U32.from i46)
  let i47 ← Array.index_usize a7 1#usize
  let c9 ← lift (core.convert.num.FromU64U32.from i47)
  let i48 ← Array.index_usize a8 1#usize
  let d9 ← lift (core.convert.num.FromU64U32.from i48)
  let i49 ← reference_poseidon.raw_limb227 2#usize a17 b9 c9 d9
  let i50 ← Array.index_usize a4 2#usize
  let a18 ← lift (core.convert.num.FromU64U32.from i50)
  let i51 ← Array.index_usize a6 2#usize
  let b10 ← lift (core.convert.num.FromU64U32.from i51)
  let i52 ← Array.index_usize a7 2#usize
  let c10 ← lift (core.convert.num.FromU64U32.from i52)
  let i53 ← Array.index_usize a8 2#usize
  let d10 ← lift (core.convert.num.FromU64U32.from i53)
  let i54 ← reference_poseidon.raw_limb227 2#usize a18 b10 c10 d10
  let i55 ← Array.index_usize a4 3#usize
  let a19 ← lift (core.convert.num.FromU64U32.from i55)
  let i56 ← Array.index_usize a6 3#usize
  let b11 ← lift (core.convert.num.FromU64U32.from i56)
  let i57 ← Array.index_usize a7 3#usize
  let c11 ← lift (core.convert.num.FromU64U32.from i57)
  let i58 ← Array.index_usize a8 3#usize
  let d11 ← lift (core.convert.num.FromU64U32.from i58)
  let i59 ← reference_poseidon.raw_limb227 2#usize a19 b11 c11 d11
  raw_reference_tail3_550 a4 a6 a7 a8 i4 i9 i14 i19 i24 i29 i34 i39 i44 i49 i54 i59

def raw_reference_tail1_550 (a4 a6 a7 a8 : Limbs32_550) (i4 i9 i14 i19 : U64) : Result Limbs64_550 := do
  let i20 ← Array.index_usize a4 0#usize
  let a12 ← lift (core.convert.num.FromU64U32.from i20)
  let i21 ← Array.index_usize a6 0#usize
  let b4 ← lift (core.convert.num.FromU64U32.from i21)
  let i22 ← Array.index_usize a7 0#usize
  let c4 ← lift (core.convert.num.FromU64U32.from i22)
  let i23 ← Array.index_usize a8 0#usize
  let d4 ← lift (core.convert.num.FromU64U32.from i23)
  let i24 ← reference_poseidon.raw_limb227 1#usize a12 b4 c4 d4
  let i25 ← Array.index_usize a4 1#usize
  let a13 ← lift (core.convert.num.FromU64U32.from i25)
  let i26 ← Array.index_usize a6 1#usize
  let b5 ← lift (core.convert.num.FromU64U32.from i26)
  let i27 ← Array.index_usize a7 1#usize
  let c5 ← lift (core.convert.num.FromU64U32.from i27)
  let i28 ← Array.index_usize a8 1#usize
  let d5 ← lift (core.convert.num.FromU64U32.from i28)
  let i29 ← reference_poseidon.raw_limb227 1#usize a13 b5 c5 d5
  let i30 ← Array.index_usize a4 2#usize
  let a14 ← lift (core.convert.num.FromU64U32.from i30)
  let i31 ← Array.index_usize a6 2#usize
  let b6 ← lift (core.convert.num.FromU64U32.from i31)
  let i32 ← Array.index_usize a7 2#usize
  let c6 ← lift (core.convert.num.FromU64U32.from i32)
  let i33 ← Array.index_usize a8 2#usize
  let d6 ← lift (core.convert.num.FromU64U32.from i33)
  let i34 ← reference_poseidon.raw_limb227 1#usize a14 b6 c6 d6
  let i35 ← Array.index_usize a4 3#usize
  let a15 ← lift (core.convert.num.FromU64U32.from i35)
  let i36 ← Array.index_usize a6 3#usize
  let b7 ← lift (core.convert.num.FromU64U32.from i36)
  let i37 ← Array.index_usize a7 3#usize
  let c7 ← lift (core.convert.num.FromU64U32.from i37)
  let i38 ← Array.index_usize a8 3#usize
  let d7 ← lift (core.convert.num.FromU64U32.from i38)
  let i39 ← reference_poseidon.raw_limb227 1#usize a15 b7 c7 d7
  raw_reference_tail2_550 a4 a6 a7 a8 i4 i9 i14 i19 i24 i29 i34 i39

def raw_reference_tail0_550 (a a1 a2 a3 : Limbs32_550) : Result Limbs64_550 := do
  let a4 ← Array.index_usize (Array.make 4#usize [ a, a1, a2, a3 ] (PV_B3P_Length227.size4 (a) (a1) (a2) (a3))) 0#usize
  let i ← Array.index_usize a4 0#usize
  let a5 ← lift (core.convert.num.FromU64U32.from i)
  let a6 ← Array.index_usize (Array.make 4#usize [ a, a1, a2, a3 ] (PV_B3P_Length227.size4 (a) (a1) (a2) (a3))) 1#usize
  let i1 ← Array.index_usize a6 0#usize
  let b ← lift (core.convert.num.FromU64U32.from i1)
  let a7 ← Array.index_usize (Array.make 4#usize [ a, a1, a2, a3 ] (PV_B3P_Length227.size4 (a) (a1) (a2) (a3))) 2#usize
  let i2 ← Array.index_usize a7 0#usize
  let c ← lift (core.convert.num.FromU64U32.from i2)
  let a8 ← Array.index_usize (Array.make 4#usize [ a, a1, a2, a3 ] (PV_B3P_Length227.size4 (a) (a1) (a2) (a3))) 3#usize
  let i3 ← Array.index_usize a8 0#usize
  let d ← lift (core.convert.num.FromU64U32.from i3)
  let i4 ← reference_poseidon.raw_limb227 0#usize a5 b c d
  let i5 ← Array.index_usize a4 1#usize
  let a9 ← lift (core.convert.num.FromU64U32.from i5)
  let i6 ← Array.index_usize a6 1#usize
  let b1 ← lift (core.convert.num.FromU64U32.from i6)
  let i7 ← Array.index_usize a7 1#usize
  let c1 ← lift (core.convert.num.FromU64U32.from i7)
  let i8 ← Array.index_usize a8 1#usize
  let d1 ← lift (core.convert.num.FromU64U32.from i8)
  let i9 ← reference_poseidon.raw_limb227 0#usize a9 b1 c1 d1
  let i10 ← Array.index_usize a4 2#usize
  let a10 ← lift (core.convert.num.FromU64U32.from i10)
  let i11 ← Array.index_usize a6 2#usize
  let b2 ← lift (core.convert.num.FromU64U32.from i11)
  let i12 ← Array.index_usize a7 2#usize
  let c2 ← lift (core.convert.num.FromU64U32.from i12)
  let i13 ← Array.index_usize a8 2#usize
  let d2 ← lift (core.convert.num.FromU64U32.from i13)
  let i14 ← reference_poseidon.raw_limb227 0#usize a10 b2 c2 d2
  let i15 ← Array.index_usize a4 3#usize
  let a11 ← lift (core.convert.num.FromU64U32.from i15)
  let i16 ← Array.index_usize a6 3#usize
  let b3 ← lift (core.convert.num.FromU64U32.from i16)
  let i17 ← Array.index_usize a7 3#usize
  let c3 ← lift (core.convert.num.FromU64U32.from i17)
  let i18 ← Array.index_usize a8 3#usize
  let d3 ← lift (core.convert.num.FromU64U32.from i18)
  let i19 ← reference_poseidon.raw_limb227 0#usize a11 b3 c3 d3
  raw_reference_tail1_550 a4 a6 a7 a8 i4 i9 i14 i19

def raw_native_tail4_550 (r0 r1 r2 r3 : Limbs64_550) : Result Limbs64_550 := do
  let rows := Array.make 4#usize [r0,r1,r2,r3] (by simp only [List.length_cons,List.length_nil]; rfl)
  let bound ← reference_poseidon.EXTERNAL_LOCAL_LIMB_MODULUS_BOUND
  let _ ← source_debug_matrix550 bound rows
  let p0 ← raw_pack0_550 r0 r1 r2 r3 bound
  let p1 ← raw_pack1_550 r0 r1 r2 r3 bound
  let p2 ← raw_pack2_550 r0 r1 r2 r3 bound
  let p3 ← raw_pack3_550 r0 r1 r2 r3 bound
  .ok (Array.make 4#usize [p0,p1,p2,p3] (by simp only [List.length_cons,List.length_nil]; rfl))

def raw_native_tail3_550 (a b c d : Limbs32_550) (r0 r1 r2 : Limbs64_550) : Result Limbs64_550 := do
  let r3 ← raw_row550 a b c d 3#usize
  raw_native_tail4_550 r0 r1 r2 r3

def raw_native_tail2_550 (a b c d : Limbs32_550) (r0 r1 : Limbs64_550) : Result Limbs64_550 := do
  let r2 ← raw_row550 a b c d 2#usize
  raw_native_tail3_550 a b c d r0 r1 r2

def raw_native_tail1_550 (a b c d : Limbs32_550) (r0 : Limbs64_550) : Result Limbs64_550 := do
  let r1 ← raw_row550 a b c d 1#usize
  raw_native_tail2_550 a b c d r0 r1

def raw_native_tail0_550 (a b c d : Limbs32_550) : Result Limbs64_550 := do
  let r0 ← raw_row550 a b c d 0#usize
  raw_native_tail1_550 a b c d r0

/-- Pure delta refactoring of the exact emission, with every primitive opaque.
No recurrence, raw arithmetic or numerical cell is evaluated here. -/
theorem raw_reference_factor550 (input : Array aspis_core.field.QM31 4#usize) :
    reference_poseidon.external_local_packed_raw input = (do
  let q ← Array.index_usize input 0#usize
  let a ← reference_poseidon.extension_limbs q
  let q1 ← Array.index_usize input 1#usize
  let a1 ← reference_poseidon.extension_limbs q1
  let q2 ← Array.index_usize input 2#usize
  let a2 ← reference_poseidon.extension_limbs q2
  let q3 ← Array.index_usize input 3#usize
  let a3 ← reference_poseidon.extension_limbs q3
  raw_reference_tail0_550 a a1 a2 a3) := by
  rfl

#print axioms raw_reference_factor550
end PV_B3P_Association550227
