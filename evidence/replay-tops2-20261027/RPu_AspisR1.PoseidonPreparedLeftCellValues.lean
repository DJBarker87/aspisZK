import RPu_AspisR1.PoseidonPreparedInputCellValues
import RPu_AspisR1PoseidonPreparedChannelArraySpecs
import RPu_AspisR1.PoseidonPreparedIndexProductBounds

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedLeftCellValues
open Aeneas.Std Result AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev PreparedArray := Array Prepared 3#usize
abbrev M31 := field.M31

private def at3 {α : Type} (a : Array α 3#usize) (i : Usize) (hi : i.val < 3) : α :=
  AspisR1PoseidonPreparedChannelRunStepLocal.at3 a i hi

private def leftCell (left : PreparedArray) (index component channel : Usize)
    (hi : index.val < 3) (hc : component.val < 3) (hch : channel.val < 3) : M31 :=
  at3 (at3 (at3 left index hi).components component hc) channel hch

private def leftAt (left : PreparedArray) (i : Fin 3) : Prepared :=
  left.val[(AspisR1PoseidonPreparedIndexProductBounds.uFin i).val]'(by
    have hu := AspisR1PoseidonPreparedIndexProductBounds.uFin_val i
    simpa [left.property, hu] using i.isLt)

theorem left_cells (left : PreparedArray) (i : Fin 3) (x : QM)
    (hprepared : AspisR1.ExtractedMaskPreparedState.PreparedFor (leftAt left i) x) :
    ∃ t s0 s1 s2,
      field.CM31.add x.c0 x.c1 = .ok t ∧
      leftCell left (AspisR1PoseidonPreparedIndexProductBounds.uFin i) 0#usize 0#usize
        (by rw [AspisR1PoseidonPreparedIndexProductBounds.uFin_val]; exact i.isLt)
        (by scalar_tac) (by scalar_tac) = x.c0.a ∧
      leftCell left (AspisR1PoseidonPreparedIndexProductBounds.uFin i) 0#usize 1#usize
        (by rw [AspisR1PoseidonPreparedIndexProductBounds.uFin_val]; exact i.isLt)
        (by scalar_tac) (by scalar_tac) = x.c0.b ∧
      leftCell left (AspisR1PoseidonPreparedIndexProductBounds.uFin i) 0#usize 2#usize
        (by rw [AspisR1PoseidonPreparedIndexProductBounds.uFin_val]; exact i.isLt)
        (by scalar_tac) (by scalar_tac) = s0 ∧
      leftCell left (AspisR1PoseidonPreparedIndexProductBounds.uFin i) 1#usize 0#usize
        (by rw [AspisR1PoseidonPreparedIndexProductBounds.uFin_val]; exact i.isLt)
        (by scalar_tac) (by scalar_tac) = x.c1.a ∧
      leftCell left (AspisR1PoseidonPreparedIndexProductBounds.uFin i) 1#usize 1#usize
        (by rw [AspisR1PoseidonPreparedIndexProductBounds.uFin_val]; exact i.isLt)
        (by scalar_tac) (by scalar_tac) = x.c1.b ∧
      leftCell left (AspisR1PoseidonPreparedIndexProductBounds.uFin i) 1#usize 2#usize
        (by rw [AspisR1PoseidonPreparedIndexProductBounds.uFin_val]; exact i.isLt)
        (by scalar_tac) (by scalar_tac) = s1 ∧
      leftCell left (AspisR1PoseidonPreparedIndexProductBounds.uFin i) 2#usize 0#usize
        (by rw [AspisR1PoseidonPreparedIndexProductBounds.uFin_val]; exact i.isLt)
        (by scalar_tac) (by scalar_tac) = t.a ∧
      leftCell left (AspisR1PoseidonPreparedIndexProductBounds.uFin i) 2#usize 1#usize
        (by rw [AspisR1PoseidonPreparedIndexProductBounds.uFin_val]; exact i.isLt)
        (by scalar_tac) (by scalar_tac) = t.b ∧
      leftCell left (AspisR1PoseidonPreparedIndexProductBounds.uFin i) 2#usize 2#usize
        (by rw [AspisR1PoseidonPreparedIndexProductBounds.uFin_val]; exact i.isLt)
        (by scalar_tac) (by scalar_tac) = s2 ∧
      s0.val = (x.c0.a.val + x.c0.b.val) % 2147483647 ∧
      s1.val = (x.c1.a.val + x.c1.b.val) % 2147483647 ∧
      s2.val = (t.a.val + t.b.val) % 2147483647 := by
  obtain ⟨p,hread,hget⟩ := AspisR1PoseidonPreparedChannelArraySpecs.index_ok left
    (AspisR1PoseidonPreparedIndexProductBounds.uFin i)
    (by rw [AspisR1PoseidonPreparedIndexProductBounds.uFin_val]; exact i.isLt)
  have hpeq : p = leftAt left i := by
    simpa [leftAt] using hget
  subst p
  have hleftAt : leftAt left i = left.val[i.val]'(by simpa [left.property] using i.isLt) := by
    simpa [leftAt, AspisR1PoseidonPreparedIndexProductBounds.uFin_val] using hget
  obtain ⟨t,s0,s1,s2,hsum,h00,h01,h02,h10,h11,h12,h20,h21,h22,hs0,hs1,hs2⟩ :=
    AspisR1.PoseidonPreparedInputCellValues.prepared_cell_values (leftAt left i) x hprepared
  refine ⟨t,s0,s1,s2,hsum,?_,?_,?_,?_,?_,?_,?_,?_,?_,hs0,hs1,hs2⟩
  · simpa [leftCell, at3, AspisR1PoseidonPreparedChannelRunStepLocal.at3,
      leftAt, AspisR1PoseidonPreparedIndexProductBounds.uFin_val,
      AspisR1.PoseidonPreparedInputCellValues.cell] using h00
  · simpa [leftCell, at3, AspisR1PoseidonPreparedChannelRunStepLocal.at3,
      leftAt, AspisR1PoseidonPreparedIndexProductBounds.uFin_val,
      AspisR1.PoseidonPreparedInputCellValues.cell] using h01
  · simpa [leftCell, at3, AspisR1PoseidonPreparedChannelRunStepLocal.at3,
      leftAt, AspisR1PoseidonPreparedIndexProductBounds.uFin_val,
      AspisR1.PoseidonPreparedInputCellValues.cell] using h02
  · simpa [leftCell, at3, AspisR1PoseidonPreparedChannelRunStepLocal.at3,
      leftAt, AspisR1PoseidonPreparedIndexProductBounds.uFin_val,
      AspisR1.PoseidonPreparedInputCellValues.cell] using h10
  · simpa [leftCell, at3, AspisR1PoseidonPreparedChannelRunStepLocal.at3,
      leftAt, AspisR1PoseidonPreparedIndexProductBounds.uFin_val,
      AspisR1.PoseidonPreparedInputCellValues.cell] using h11
  · simpa [leftCell, at3, AspisR1PoseidonPreparedChannelRunStepLocal.at3,
      leftAt, AspisR1PoseidonPreparedIndexProductBounds.uFin_val,
      AspisR1.PoseidonPreparedInputCellValues.cell] using h12
  · simpa [leftCell, at3, AspisR1PoseidonPreparedChannelRunStepLocal.at3,
      leftAt, AspisR1PoseidonPreparedIndexProductBounds.uFin_val,
      AspisR1.PoseidonPreparedInputCellValues.cell] using h20
  · simpa [leftCell, at3, AspisR1PoseidonPreparedChannelRunStepLocal.at3,
      leftAt, AspisR1PoseidonPreparedIndexProductBounds.uFin_val,
      AspisR1.PoseidonPreparedInputCellValues.cell] using h21
  · simpa [leftCell, at3, AspisR1PoseidonPreparedChannelRunStepLocal.at3,
      leftAt, AspisR1PoseidonPreparedIndexProductBounds.uFin_val,
      AspisR1.PoseidonPreparedInputCellValues.cell] using h22

#print axioms left_cells
end AspisR1.PoseidonPreparedLeftCellValues
