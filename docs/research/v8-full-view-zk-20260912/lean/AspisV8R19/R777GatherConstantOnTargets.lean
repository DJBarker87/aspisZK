import AspisV8R17.ScatterDual
import AspisV8R19.R774WeightedScheduleMass

/-! Constant preservation along the explicit, finite source gather targets. -/
set_option autoImplicit false
namespace AspisV8R19.R777GatherConstantOnTargets

open AspisV8R17
open AspisV8R19.R774WeightedScheduleMass

theorem source_gather_constant_on_targets
    {F : Type*} [CommRing F] (half : F) (hhalf : half + half = 1)
    (j : Nat) (hj : j < 512) (w : Nat → F) (C : F)
    (hw : ∀ r ∈ indexTargets j, w r = C) :
    sourceGather half w j = C := by
  obtain ⟨edges, he, _⟩ :=
    weighted_schedule_bounds half 512 j schedule512_bounded hj
  have htargets : edges.map Prod.fst = indexTargets j := by
    rw [← weighted_targets half j]
    simp only [he, Option.getD_some]
  have hedge : ∀ e ∈ edges, w e.1 = C := by
    intro e hem
    apply hw e.1
    rw [← htargets]
    exact List.mem_map.mpr ⟨e, hem, rfl⟩
  have hmass := weighted_index_loop_constant_mass half hhalf 10 j 0 1 edges he w C hedge
  simpa only [sourceGather, he, Option.getD_some, one_mul] using hmass

theorem source_gather_double_constant_on_targets
    {F : Type*} [CommRing F] (half : F) (hhalf : half + half = 1)
    (j : Nat) (hj : j < 512) (w : Nat → F) (C : F)
    (houter : ∀ r ∈ indexTargets j, r < 512)
    (hw : ∀ r ∈ (indexTargets j).flatMap indexTargets, w r = C) :
    sourceGather half (sourceGather half w) j = C := by
  apply source_gather_constant_on_targets half hhalf j hj (sourceGather half w) C
  intro r hr
  apply source_gather_constant_on_targets half hhalf r (houter r hr) w C
  intro x hx
  apply hw x
  exact List.mem_flatMap.mpr ⟨r, hr, hx⟩

#print axioms source_gather_constant_on_targets
#print axioms source_gather_double_constant_on_targets

end AspisV8R19.R777GatherConstantOnTargets
