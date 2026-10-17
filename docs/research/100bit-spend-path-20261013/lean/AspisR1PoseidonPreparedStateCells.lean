import ExtractedMaskPreparedState
import AspisR1PoseidonPreparedChannelArraySpecs

set_option autoImplicit false
namespace AspisR1PoseidonPreparedStateCells
open Aeneas.Std Result AspisR1SelectedMaskProbe

abbrev P : Nat := 2147483647
abbrev CM := field.CM31
abbrev QM := field.QM31
abbrev M31 := field.M31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev Component := Array M31 3#usize
abbrev CanonicalCM := AspisR1.ExtractedMaskTowerAdd.CanonicalCM
abbrev CanonicalQM := AspisR1.ExtractedMaskTowerAdd.CanonicalQM

private def at3 {α : Type} (a : Array α 3#usize) (i : Usize) (hi : i.val < 3) : α :=
  a.val[i.val]'(by simpa [a.property] using hi)

private theorem component_cell_canonical (a : Component) (x : CM)
    (hx : CanonicalCM x) (ha : AspisR1.ExtractedMaskPreparedState.ComponentFor a x)
    (ch : Usize) (hch : ch.val < 3) :
    (at3 a ch hch).val < P := by
  rcases ha with ⟨s, heq, hs, hscan⟩
  have hcases : ch.val = 0 ∨ ch.val = 1 ∨ ch.val = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · have hch' : ch = 0#usize := UScalar.eq_of_val_eq h0
    subst ch
    simpa [at3, heq, Array.make] using hx.1
  · have hch' : ch = 1#usize := UScalar.eq_of_val_eq h1
    subst ch
    simpa [at3, heq, Array.make] using hx.2
  · have hch' : ch = 2#usize := UScalar.eq_of_val_eq h2
    subst ch
    simpa [at3, heq, Array.make] using hscan

theorem prepared_cells_canonical (p : Prepared) (x : QM)
    (hx : CanonicalQM x) (hp : AspisR1.ExtractedMaskPreparedState.PreparedFor p x) :
    ∀ (c ch : Usize) (hc : c.val < 3) (hch : ch.val < 3),
      (at3 (at3 p.components c hc) ch hch).val < P := by
  rcases hp with ⟨t,a,b,d,ht,htcan,ha,hb,hd,hcomponents⟩
  intro c ch hc hch
  have hcases : c.val = 0 ∨ c.val = 1 ∨ c.val = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · have hc' : c = 0#usize := UScalar.eq_of_val_eq h0
    subst c
    simpa [at3, hcomponents, Array.make] using
      component_cell_canonical a x.c0 hx.1 ha ch hch
  · have hc' : c = 1#usize := UScalar.eq_of_val_eq h1
    subst c
    simpa [at3, hcomponents, Array.make] using
      component_cell_canonical b x.c1 hx.2 hb ch hch
  · have hc' : c = 2#usize := UScalar.eq_of_val_eq h2
    subst c
    simpa [at3, hcomponents, Array.make] using
      component_cell_canonical d t htcan hd ch hch

#print axioms prepared_cells_canonical
end AspisR1PoseidonPreparedStateCells
