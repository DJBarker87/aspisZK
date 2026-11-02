import PV_B3P_RawTails550227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227 Result PV_B3P_Binding9227
set_option autoImplicit false
attribute [local irreducible] Array.index_usize reference_poseidon.extension_limbs
  reference_poseidon.raw_limb227 U64.wrapping_add U64.wrapping_sub U64.wrapping_mul
  core.convert.num.FromU64U32.from

theorem raw_reference_tail4_factor550 (i4 i9 i14 i19 i24 i29 i34 i39 i44 i49 i54 i59 i64 i69 i74 i79 : U64) :
    (do
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
    ) = raw_reference_tail4_550 i4 i9 i14 i19 i24 i29 i34 i39 i44 i49 i54 i59 i64 i69 i74 i79 := by
  unfold raw_reference_tail4_550
  rfl

#print axioms raw_reference_tail4_factor550
end PV_B3P_Association550227
