import NCM_DigestWindows

set_option autoImplicit false
namespace AspisR1.NCM_PartsWindows
open Aeneas Aeneas.Std CheckpointBytes5Effect

instance : Inhabited (Slice U8) := ⟨⟨[],by simp⟩⟩

/-- Literal nested-slice equality from every arbitrary per-part byte window.
The actual source buffer and returned parts stay fixed across all offsets. -/
theorem exact (actual expected : Parts)
    (arity : actual.val.length=expected.val.length)
    (sizes : ∀ j, j<expected.val.length →
      (actual.val[j]!).val.length=(expected.val[j]!).val.length)
    (windows : ∀ j, j<expected.val.length → ∀ i, i<(expected.val[j]!).val.length →
      (actual.val[j]!).val[i]! = (expected.val[j]!).val[i]!) : actual=expected := by
  apply Subtype.ext
  apply NCM_DigestWindows.slice actual.val expected.val arity
  intro j hj
  apply Subtype.ext
  exact NCM_DigestWindows.slice _ _ (sizes j hj) (windows j hj)

#print axioms exact
end AspisR1.NCM_PartsWindows
