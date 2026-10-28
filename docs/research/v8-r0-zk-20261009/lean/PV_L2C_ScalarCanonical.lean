import PV_L2C_ScalarBalance
set_option autoImplicit false
namespace PV_L2C_ScalarCanonical
open Aeneas Aeneas.Std Result PV_L2C_M31 PV_L2C_NativeFold PV_L2C_ScalarBalance

theorem lookup_canonical (table : Fin 1024 → word) (hc : ∀ i, canonical (table i)) (r : Usize) :
    canonical (lookup table r) := by
  unfold lookup
  split
  · exact hc _
  · unfold canonical p
    decide
#print axioms lookup_canonical

theorem selected_canonical (table : Fin 1024 → word) (active : Fin 1024 → Bool)
    (hc : ∀ i, canonical (table i)) (d : Usize) (rows : List Usize) :
    ∀ q ∈ selected table active d rows, canonical q := by
  intro q hq
  obtain ⟨r,hr,he⟩ := List.mem_filterMap.mp hq
  split at he
  · cases he
    exact lookup_canonical table hc r
  · cases he
#print axioms selected_canonical

/-- The extracted scalar balancing store preserves every raw canonical limb. -/
theorem output_canonical (table : Fin 1024 → word) (active : Fin 1024 → Bool)
    (hc : ∀ i,canonical (table i)) (d : Usize) :
    ∀ i,canonical (output table active d i) := by
  intro i
  unfold output
  split
  · exact (negate_decode _ (selected_canonical table active hc d _)).1
  · exact hc i
#print axioms output_canonical
end PV_L2C_ScalarCanonical
