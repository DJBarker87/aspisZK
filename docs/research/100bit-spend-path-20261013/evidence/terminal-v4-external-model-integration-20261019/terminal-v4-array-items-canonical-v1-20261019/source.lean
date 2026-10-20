import TerminalV4CompositionLoopPolynomialV6

set_option autoImplicit false
namespace AspisR1.TerminalV4CompositionLoopArrayItemsCanonical
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev CanonicalQM := AspisR1.TerminalV4TowerAdd.CanonicalQM

private theorem listLoopCanonicalModel_of_array
    (semantic : Aeneas.Std.Array QM 24#usize)
    (hcanonical : ∀ i : Fin 24,
      CanonicalQM (semantic.val[i.val]'(by simpa [semantic.property] using i.isLt))) :
    AspisR1.TerminalV4CompositionLoopCanonical.listLoopCanonicalModel
      (AspisR1.TerminalV4CompositionLoopArrayHorner.decode 0)
      semantic.val.reverse := by
  intro x hx
  have hx' : x ∈ semantic.val := List.mem_reverse.mp hx
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hx'
  have hi24 : i < 24 := by simpa [semantic.property] using hi
  have hci := hcanonical ⟨i, hi24⟩
  simpa [hget] using hci
end AspisR1.TerminalV4CompositionLoopArrayItemsCanonical
