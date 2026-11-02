import PV_B3P_RawPack2550227
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

def raw_pack3_550 (a b c d : Limbs64_550) (bound : U64) : Result U64 := do
  let i119 ← Array.index_usize a 3#usize
  let i120 ← Array.index_usize b 2#usize
  let i121 ← lift (Std.U64.wrapping_add i119 i120)
  let i122 ← Array.index_usize c 1#usize
  let i123 ← lift (Std.U64.wrapping_add i121 i122)
  let i124 ← Array.index_usize d 0#usize
  let i125 ← lift (Std.U64.wrapping_add i123 i124)
  .ok i125

attribute [local irreducible] U64.wrapping_add U64.wrapping_sub U64.wrapping_mul

theorem raw_pack3_value550 (a b c d : Limbs64_550) (bound : U64) :
    raw_pack3_550 a b c d bound =
      .ok (U64.wrapping_add (U64.wrapping_add (U64.wrapping_add (limb_at550 a 3#usize (by decide)) (limb_at550 b 2#usize (by decide))) (limb_at550 c 1#usize (by decide))) (limb_at550 d 0#usize (by decide))) := by
  unfold raw_pack3_550
  simp only [lift, bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value a 3#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value b 2#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value c 1#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value d 0#usize (by decide)]
  simp only [bind_tc_ok]
  rfl

#print axioms raw_pack3_value550
end PV_B3P_Association550227
