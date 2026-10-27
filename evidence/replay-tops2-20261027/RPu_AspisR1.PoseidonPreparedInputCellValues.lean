import RPu_AspisR1.PoseidonPreparedValueCells
import RPu_AspisR1PoseidonPreparedChannelRunStepLocal

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedInputCellValues
open Aeneas.Std AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev M31 := field.M31

def cell (p : Prepared) (c ch : Usize) (hc : c.val < 3) (hch : ch.val < 3) : M31 :=
  AspisR1PoseidonPreparedChannelRunStepLocal.at3
    (AspisR1PoseidonPreparedChannelRunStepLocal.at3 p.components c hc) ch hch

theorem prepared_cell_values (p : Prepared) (x : QM)
    (hp : AspisR1.ExtractedMaskPreparedState.PreparedFor p x) :
    ∃ t s0 s1 s2,
      field.CM31.add x.c0 x.c1 = .ok t ∧
      cell p 0#usize 0#usize (by scalar_tac) (by scalar_tac) = x.c0.a ∧
      cell p 0#usize 1#usize (by scalar_tac) (by scalar_tac) = x.c0.b ∧
      cell p 0#usize 2#usize (by scalar_tac) (by scalar_tac) = s0 ∧
      cell p 1#usize 0#usize (by scalar_tac) (by scalar_tac) = x.c1.a ∧
      cell p 1#usize 1#usize (by scalar_tac) (by scalar_tac) = x.c1.b ∧
      cell p 1#usize 2#usize (by scalar_tac) (by scalar_tac) = s1 ∧
      cell p 2#usize 0#usize (by scalar_tac) (by scalar_tac) = t.a ∧
      cell p 2#usize 1#usize (by scalar_tac) (by scalar_tac) = t.b ∧
      cell p 2#usize 2#usize (by scalar_tac) (by scalar_tac) = s2 ∧
      s0.val = (x.c0.a.val + x.c0.b.val) % 2147483647 ∧
      s1.val = (x.c1.a.val + x.c1.b.val) % 2147483647 ∧
      s2.val = (t.a.val + t.b.val) % 2147483647 := by
  obtain ⟨t,s0,s1,s2,hcomp,hsum,hs0,hs1,hs2⟩ :=
    AspisR1PoseidonPreparedValueCells.prepared_components p x hp
  refine ⟨t,s0,s1,s2,hsum,?_,?_,?_,?_,?_,?_,?_,?_,?_,hs0,hs1,hs2⟩ <;>
    simp [cell, AspisR1PoseidonPreparedChannelRunStepLocal.at3, hcomp, Array.make]

#print axioms prepared_cell_values
end AspisR1.PoseidonPreparedInputCellValues
