import RPv_FJa_ExpandCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_Expansion
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
/-- Canonicality for the installed expansion from its actual seed and actual
coordinate slice. Bounds are derived from successful writes. -/
theorem canonical_result (N : Usize) (coordinates : Slice NQ) (out : Array NQ N)
    (hc : ∀ x∈coordinates.val,Canon x)
    (run : pool_v1.pair_forest_copy_terminal.Selectors.expand N coordinates=ok out) : canonical out := by
  unfold pool_v1.pair_forest_copy_terminal.Selectors.expand at run
  obtain ⟨seed,hs,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨iterator,hi,run⟩ := FIv_Map.bind_success _ _ _ run
  have cz : canonical (Array.repeat N field.QM31.ZERO) := by
    intro x hx
    have eq : x=field.QM31.ZERO := (List.mem_replicate.mp hx).2
    rw [eq]
    exact FIv_NativeValue.zero.1
  have cs := FJa_ArrayUpdate.canonical_write _ seed 0#usize field.QM31.ONE cz FIv_NativeValue.one.1 hs
  have same : iterator=⟨coordinates,0⟩ := (Result.ok.inj hi).symm
  rw [same] at run
  exact FJa_ExpandCanonical.loop _ seed out 1#usize hc cs run
#print axioms canonical_result
end AspisR1.FJa_Expansion
end
