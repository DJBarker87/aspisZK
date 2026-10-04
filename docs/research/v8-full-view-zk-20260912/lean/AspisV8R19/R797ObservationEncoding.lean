import AspisV8R19.R746SelectedJointMinor
import AspisV8R19.R707FullActiveDeterminant

set_option autoImplicit false
namespace AspisV8R19.R797ObservationEncoding
open AspisV8R19.R698ActiveCoreLayout
open AspisV8R19.R702ActiveScalarEmbedding
open AspisV8R19.R707FullActiveDeterminant
abbrev Obs := AspisV8R19.R746SelectedJointMinor.ObservationRow

theorem active_rowCode_injective : Function.Injective rowCode := by
  intro x y h
  rcases x with x | x <;> rcases y with y | y
  · apply Sum.inl.inj_iff.mpr
    apply Subtype.ext
    apply Fin.ext
    exact h
  · have hx := highActive_bounds x.val x.property
    simp only [rowCode] at h
    omega
  · have hy := highActive_bounds y.val y.property
    simp only [rowCode] at h
    omega
  · congr

def observationKey : Obs → Nat × Nat
  | .inl j => (0, rowCode j)
  | .inr (.inl p) => (1, p.val)
  | .inr (.inr k) => (2, k.val)

theorem observationKey_injective : Function.Injective observationKey := by
  intro x y h
  rcases x with x | (p | k) <;> rcases y with y | (q | l) <;>
    simp only [observationKey, Prod.mk.injEq] at h
  · exact congrArg Sum.inl (active_rowCode_injective h.2)
  · omega
  · omega
  · omega
  · exact congrArg (fun p => Sum.inr (Sum.inl p)) (Fin.ext h.2)
  · omega
  · omega
  · omega
  · exact congrArg (fun k => Sum.inr (Sum.inr k)) (Fin.ext h.2)

#print axioms active_rowCode_injective
#print axioms observationKey_injective
end AspisV8R19.R797ObservationEncoding
