import WeightsFieldExplicitDecoder
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_SelectorModel
/-- No decoder law is hidden: this theorem exposes both checked offset arithmetic
and the exact selected Slice passed to the same supplied decoder. -/
theorem field_cut {T : Type} (decode : Slice U8 → Result (Option T))
    (bytes : Slice U8) (i lo next hi : Usize) (selected : Slice U8) (value : T)
    (hlo : i * 32#usize = ok lo) (hn : i + 1#usize = ok next)
    (hhi : next * 32#usize = ok hi)
    (hs : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
      {start := lo, «end» := hi} = ok selected)
    (hd : decode selected = ok (some value)) :
    AspisR1WeightsFieldCurrent.weights.field decode bytes i = ok value := by
  change core.slice.index.SliceIndexRangeUsizeSlice.index
    {start := lo, «end» := hi} bytes = ok selected at hs
  simp [AspisR1WeightsFieldCurrent.weights.field,hlo,hn,hhi,hs,hd,
    core.option.Option.unwrap]
#print axioms field_cut
end NDD_SelectorModel
