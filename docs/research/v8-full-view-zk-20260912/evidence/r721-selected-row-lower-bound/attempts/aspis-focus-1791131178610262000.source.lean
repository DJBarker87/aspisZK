import AspisV8R19.R720QueryActiveCoreImage
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R721SelectedRowLowerBound
open AspisV8R19.R698ActiveCoreLayout
open AspisV8R19.R707FullActiveDeterminant
open AspisV8R19.R710SelectedActivePolynomial

lemma no_highActive_88_113 (i : Fin 26) :
    (⟨88+i.val, by omega⟩ : Fin 1024) ∉ highActive := by
  revert i
  decide

lemma rowCode_ge_114 (i : J) : 114 ≤ rowCode i := by
  cases i with
  | inr u => cases u; simp [rowCode]
  | inl i =>
    change 114 ≤ i.val.val
    have hb := highActive_bounds i.val i.property
    by_contra hn
    have hlow : 88 ≤ i.val.val := hb.1
    let k : Fin 26 := ⟨i.val.val-88, by omega⟩
    have heq : (⟨88+k.val, by omega⟩ : Fin 1024) = i.val := by
      apply Fin.ext
      dsimp [k]
      omega
    have hno := no_highActive_88_113 k
    exact hno (heq.symm ▸ i.property)

#print axioms no_highActive_88_113
#print axioms rowCode_ge_114
end AspisV8R19.R721SelectedRowLowerBound
