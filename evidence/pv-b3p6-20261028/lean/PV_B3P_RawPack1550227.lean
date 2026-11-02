import PV_B3P_RawPack0550227
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

def raw_pack1_550 (a b c d : Limbs64_550) (bound : U64) : Result U64 := do
  let i96 ← Array.index_usize a 1#usize
  let i97 ← Array.index_usize b 0#usize
  let i98 ← lift (Std.U64.wrapping_add i96 i97)
  let i99 ← Array.index_usize c 2#usize
  let i100 ← lift (Std.U64.wrapping_add i98 i99)
  let i101 ← Array.index_usize c 3#usize
  let i102 ← lift (Std.U64.wrapping_mul 2#u64 i101)
  let i103 ← lift (Std.U64.wrapping_add i100 i102)
  let i104 ← Array.index_usize d 2#usize
  let i105 ← lift (Std.U64.wrapping_mul 2#u64 i104)
  let i106 ← lift (Std.U64.wrapping_add i103 i105)
  let i107 ← lift (Std.U64.wrapping_add i106 bound)
  let i108 ← Array.index_usize d 3#usize
  let i109 ← lift (Std.U64.wrapping_sub i107 i108)
  .ok i109

attribute [local irreducible] U64.wrapping_add U64.wrapping_sub U64.wrapping_mul

theorem raw_pack1_value550 (a b c d : Limbs64_550) (bound : U64) :
    raw_pack1_550 a b c d bound =
      .ok (U64.wrapping_sub (U64.wrapping_add (U64.wrapping_add (U64.wrapping_add (U64.wrapping_add (U64.wrapping_add (limb_at550 a 1#usize (by decide)) (limb_at550 b 0#usize (by decide))) (limb_at550 c 2#usize (by decide))) (U64.wrapping_mul 2#u64 (limb_at550 c 3#usize (by decide)))) (U64.wrapping_mul 2#u64 (limb_at550 d 2#usize (by decide)))) bound) (limb_at550 d 3#usize (by decide))) := by
  unfold raw_pack1_550
  simp only [lift, bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value a 1#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value b 0#usize (by decide)]
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

#print axioms raw_pack1_value550
end PV_B3P_Association550227
