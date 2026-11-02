import PV_B3P_RawPack1550227
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

def raw_pack2_550 (a b c d : Limbs64_550) (bound : U64) : Result U64 := do
  let i110 ← Array.index_usize a 2#usize
  let i111 ← lift (Std.U64.wrapping_mul 2#u64 bound)
  let i112 ← lift (Std.U64.wrapping_add i110 i111)
  let i113 ← Array.index_usize b 3#usize
  let i114 ← lift (Std.U64.wrapping_sub i112 i113)
  let i115 ← Array.index_usize c 0#usize
  let i116 ← lift (Std.U64.wrapping_add i114 i115)
  let i117 ← Array.index_usize d 1#usize
  let i118 ← lift (Std.U64.wrapping_sub i116 i117)
  .ok i118

attribute [local irreducible] U64.wrapping_add U64.wrapping_sub U64.wrapping_mul

theorem raw_pack2_value550 (a b c d : Limbs64_550) (bound : U64) :
    raw_pack2_550 a b c d bound =
      .ok (U64.wrapping_sub (U64.wrapping_add (U64.wrapping_sub (U64.wrapping_add (limb_at550 a 2#usize (by decide)) (U64.wrapping_mul 2#u64 bound)) (limb_at550 b 3#usize (by decide))) (limb_at550 c 0#usize (by decide))) (limb_at550 d 1#usize (by decide))) := by
  unfold raw_pack2_550
  simp only [lift, bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value a 2#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value b 3#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value c 0#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value d 1#usize (by decide)]
  simp only [bind_tc_ok]
  rfl

#print axioms raw_pack2_value550
end PV_B3P_Association550227
