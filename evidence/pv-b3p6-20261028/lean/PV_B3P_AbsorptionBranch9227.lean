import PV_B3P_P227_09
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.mul

theorem absorption_first_branch9 (lane : Usize)
    (low fixed chunk_two chunk_eight nodes opened : aspis_core.field.QM31) (h : lane<2#usize) :
    reference_terminal.absorption_lane227 lane low fixed chunk_two chunk_eight nodes opened =
      (do let product ← aspis_core.field.QM31.mul low fixed
          aspis_core.field.QM31.mul product opened) := by
  simp only [reference_terminal.absorption_lane227,h,↓reduceIte,bind_tc_ok]

theorem absorption_rate_branch9 (lane : Usize)
    (low fixed chunk_two chunk_eight nodes opened : aspis_core.field.QM31)
    (h : ¬lane<2#usize) (hr : lane<aspis_statement.poseidon2.RATE) :
    reference_terminal.absorption_lane227 lane low fixed chunk_two chunk_eight nodes opened =
      (do let blocks ← aspis_core.field.QM31.add fixed chunk_two
          let product ← aspis_core.field.QM31.mul low blocks
          aspis_core.field.QM31.mul product opened) := by
  simp only [reference_terminal.absorption_lane227,h,hr,↓reduceIte]

theorem absorption_capacity_branch9 (lane : Usize)
    (low fixed chunk_two chunk_eight nodes opened : aspis_core.field.QM31)
    (h : ¬lane<2#usize) (hr : ¬lane<aspis_statement.poseidon2.RATE) :
    reference_terminal.absorption_lane227 lane low fixed chunk_two chunk_eight nodes opened =
      (do let blocks ← (do
            let a ← aspis_core.field.QM31.add fixed chunk_two
            let b ← aspis_core.field.QM31.add a chunk_eight
            aspis_core.field.QM31.add b nodes)
          let product ← aspis_core.field.QM31.mul low blocks
          aspis_core.field.QM31.mul product opened) := by
  simp only [reference_terminal.absorption_lane227,h,hr,↓reduceIte]

#print axioms absorption_first_branch9
#print axioms absorption_rate_branch9
#print axioms absorption_capacity_branch9
end PV_B3P_Binding9227
