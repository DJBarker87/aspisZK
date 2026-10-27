import RPv_AspisR1PoseidonPreparedChannelArraySpecs
import RPv_AspisR1PoseidonPreparedChannelUpdateInvariantV2

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedSum3AccumulatorReads
open Aeneas.Std Result AspisR1SelectedMaskProbe

abbrev U64 := UScalar UScalarTy.U64
abbrev Sums := AspisR1PoseidonPreparedChannelUpdateInvariantV2.Sums

/-- The converter's checked pair of nested reads is the exact accumulator
cell used by the recurrence invariant. -/
theorem nested_read_eq_sumCell (sums : Sums) (component channel : Usize)
    (hc : component.val < 3) (hch : channel.val < 3) (row : Array U64 3#usize) (value : U64)
    (hrow : Array.index_usize sums component = .ok row)
    (hvalue : Array.index_usize row channel = .ok value) :
    AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums component channel hc hch = value := by
  obtain ⟨row', hrow', hrowVal⟩ := AspisR1PoseidonPreparedChannelArraySpecs.index_ok sums component hc
  have hrowEq : row' = row := Result.ok.inj (hrow'.symm.trans hrow)
  obtain ⟨value', hvalue', hvalueVal⟩ := AspisR1PoseidonPreparedChannelArraySpecs.index_ok row channel hch
  have hvalueEq : value' = value := Result.ok.inj (hvalue'.symm.trans hvalue)
  have hrowValue : row = sums.val[component.val]'(by simpa [sums.property] using hc) :=
    hrowEq.symm.trans hrowVal
  have hvalueValue : value = row.val[channel.val]'(by simpa [row.property] using hch) :=
    hvalueEq.symm.trans hvalueVal
  change (sums.val[component.val]'(by simpa [sums.property] using hc)).val[channel.val]'(by
    simpa [row.property] using hch) = value
  rw [← hrowValue, ← hvalueValue]

#print axioms nested_read_eq_sumCell
end AspisR1.PoseidonPreparedSum3AccumulatorReads
