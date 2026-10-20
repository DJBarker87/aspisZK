import TerminalV4CompositionPartsCallerChunk07dV2

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

noncomputable section
namespace AspisR1.TerminalV4SelectedClaimCanonicalV1
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev Canonical := AspisR1.TerminalV4QM31Exact.CurrentCanonicalQM

theorem index_ok_canonical
    (claims : Array QM 84#usize) (index : Std.Usize) (value : QM)
    (hindex : Array.index_usize claims index = .ok value)
    (hclaims : ∀ i : Fin 84, Canonical (claims.val[i.val]'(by simpa [claims.property] using i.isLt))) :
    Canonical value := by
  unfold Array.index_usize at hindex
  cases hget : claims.val[index.val]? with
  | none => simp [hget] at hindex
  | some x =>
    simp only [hget] at hindex
    injection hindex with hv
    subst value
    have hlt : index.val < claims.val.length := by
      by_contra hn
      have hnone : claims.val[index.val]? = none := List.getElem?_eq_none.mpr (by omega)
      rw [hnone] at hget
      contradiction
    have hcanon := hclaims ⟨index.val, by simpa [claims.property] using hlt⟩
    simpa using hcanon

end AspisR1.TerminalV4SelectedClaimCanonicalV1
end
