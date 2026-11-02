import PV_B3P_RawRefTail4550227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227 Result PV_B3P_Binding9227
set_option autoImplicit false
attribute [local irreducible] Array.index_usize reference_poseidon.extension_limbs
  reference_poseidon.raw_limb227 U64.wrapping_add U64.wrapping_sub U64.wrapping_mul
  core.convert.num.FromU64U32.from

theorem raw_reference_tail3_factor550 (a4 a6 a7 a8 : Limbs32_550) (i4 i9 i14 i19 i24 i29 i34 i39 i44 i49 i54 i59 : U64) :
    (do
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
    ) = raw_reference_tail3_550 a4 a6 a7 a8 i4 i9 i14 i19 i24 i29 i34 i39 i44 i49 i54 i59 := by
  unfold raw_reference_tail3_550
  apply bind_equal9
  intro i60
  apply bind_equal9
  intro a20
  apply bind_equal9
  intro i61
  apply bind_equal9
  intro b12
  apply bind_equal9
  intro i62
  apply bind_equal9
  intro c12
  apply bind_equal9
  intro i63
  apply bind_equal9
  intro d12
  apply bind_equal9
  intro i64
  apply bind_equal9
  intro i65
  apply bind_equal9
  intro a21
  apply bind_equal9
  intro i66
  apply bind_equal9
  intro b13
  apply bind_equal9
  intro i67
  apply bind_equal9
  intro c13
  apply bind_equal9
  intro i68
  apply bind_equal9
  intro d13
  apply bind_equal9
  intro i69
  apply bind_equal9
  intro i70
  apply bind_equal9
  intro a22
  apply bind_equal9
  intro i71
  apply bind_equal9
  intro b14
  apply bind_equal9
  intro i72
  apply bind_equal9
  intro c14
  apply bind_equal9
  intro i73
  apply bind_equal9
  intro d14
  apply bind_equal9
  intro i74
  apply bind_equal9
  intro i75
  apply bind_equal9
  intro a23
  apply bind_equal9
  intro i76
  apply bind_equal9
  intro b15
  apply bind_equal9
  intro i77
  apply bind_equal9
  intro c15
  apply bind_equal9
  intro i78
  apply bind_equal9
  intro d15
  apply bind_equal9
  intro i79
  exact raw_reference_tail4_factor550 i4 i9 i14 i19 i24 i29 i34 i39 i44 i49 i54 i59 i64 i69 i74 i79

#print axioms raw_reference_tail3_factor550
end PV_B3P_Association550227
