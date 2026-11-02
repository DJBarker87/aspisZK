import PV_B3P_RawRows550227
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

def limb_at550 (row : Limbs64_550) (i : Usize) (bound : i.val < 4) : U64 :=
  row.val[i.val]'(by rw [row.property]; exact bound)

def raw_pack0_550 (a b c d : Limbs64_550) (bound : U64) : Result U64 := do
  let i81 ← Array.index_usize a 0#usize
  let i82 ← lift (Std.U64.wrapping_mul 5#u64 bound)
  let i83 ← lift (Std.U64.wrapping_add i81 i82)
  let i84 ← Array.index_usize b 1#usize
  let i85 ← lift (Std.U64.wrapping_sub i83 i84)
  let i86 ← Array.index_usize c 2#usize
  let i87 ← lift (Std.U64.wrapping_mul 2#u64 i86)
  let i88 ← lift (Std.U64.wrapping_add i85 i87)
  let i89 ← Array.index_usize c 3#usize
  let i90 ← lift (Std.U64.wrapping_sub i88 i89)
  let i91 ← Array.index_usize d 2#usize
  let i92 ← lift (Std.U64.wrapping_sub i90 i91)
  let i93 ← Array.index_usize d 3#usize
  let i94 ← lift (Std.U64.wrapping_mul 2#u64 i93)
  let i95 ← lift (Std.U64.wrapping_sub i92 i94)
  .ok i95

attribute [local irreducible] U64.wrapping_add U64.wrapping_sub U64.wrapping_mul

theorem raw_pack0_value550 (a b c d : Limbs64_550) (bound : U64) :
    raw_pack0_550 a b c d bound =
      .ok (U64.wrapping_sub (U64.wrapping_sub (U64.wrapping_sub (U64.wrapping_add (U64.wrapping_sub (U64.wrapping_add (limb_at550 a 0#usize (by decide)) (U64.wrapping_mul 5#u64 bound)) (limb_at550 b 1#usize (by decide))) (U64.wrapping_mul 2#u64 (limb_at550 c 2#usize (by decide)))) (limb_at550 c 3#usize (by decide))) (limb_at550 d 2#usize (by decide))) (U64.wrapping_mul 2#u64 (limb_at550 d 3#usize (by decide)))) := by
  unfold raw_pack0_550
  simp only [lift, bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value a 0#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value b 1#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value c 2#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value c 3#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value d 2#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value d 3#usize (by decide)]
  simp only [bind_tc_ok]
  rfl

#print axioms raw_pack0_value550
end PV_B3P_Association550227
