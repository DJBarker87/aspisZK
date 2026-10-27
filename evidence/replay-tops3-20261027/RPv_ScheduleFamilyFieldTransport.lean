import RPv_PathFamilyFieldTransport
import R0P.Schedule

/-! Generic field transport for the retained schedule family, preserving its
variant and complete source operation order. No concrete field reduction. -/
set_option autoImplicit false
namespace AspisR1.ScheduleFamilyFieldTransport
open AspisR1.ValueFamilyFieldTransport
open AspisR1.PathFamilyFieldTransport
variable {K L : Type} [Field K] [Field L]
attribute [local irreducible] R0P.g2High R0P.g2Low R0P.g2SumHigh

theorem nodes_two_sums (sel : R0P.Sel K) :
    R0P.scheduleNodes sel = R0P.g2SumHigh sel 4 21 (by omega) +
      R0P.g2SumHigh sel 33 24 (by omega) := by
  simp only [R0P.scheduleNodes, R0P.g2SumHigh, R0P.g2_fold_add,
    List.sum_append, zero_add]

theorem map_nodes (g : K →+* L) (sel : R0P.Sel K) :
    g (R0P.scheduleNodes sel) = R0P.scheduleNodes (fun i => g (sel i)) := by
  rw [nodes_two_sums, nodes_two_sums, map_add, map_sumHigh, map_sumHigh]

theorem map_initial (g : K →+* L) (v : R0P.Variant)
    (o : R0P.Openings K) (sel : R0P.Sel K) (i : Fin 16) :
    g (R0P.scheduleInitial v o sel i) =
      R0P.scheduleInitial v (mapOpenings g o) (fun j => g (sel j)) i := by
  cases v <;>
    dsimp only [R0P.scheduleInitial, R0P.scheduleVariantSelectors, mapOpenings] <;>
    split_ifs <;>
    simp only [map_sub, map_mul, map_add, map_ofNat, map_zero,
      map_high, map_low, map_nodes]

theorem map_absorptionLiteral (g : K →+* L) (low fixed two eight nodes : K)
    (z : Fin 16 → K) (i : Fin 16) :
    g (R0P.scheduleAbsorptionLiteral low fixed two eight nodes z i) =
      R0P.scheduleAbsorptionLiteral (g low) (g fixed) (g two) (g eight) (g nodes)
        (fun j => g (z j)) i := by
  unfold R0P.scheduleAbsorptionLiteral
  split_ifs <;> simp only [map_mul, map_add]

theorem map_absorption (g : K →+* L) (v : R0P.Variant)
    (o : R0P.Openings K) (sel : R0P.Sel K) (i : Fin 16) :
    g (R0P.scheduleAbsorption v o sel i) =
      R0P.scheduleAbsorption v (mapOpenings g o) (fun j => g (sel j)) i := by
  cases v <;>
    dsimp only [R0P.scheduleAbsorption, R0P.scheduleVariantSelectors, mapOpenings] <;>
    simp only [map_absorptionLiteral, map_add, map_high, map_low, map_nodes, map_zero]

theorem map_family (g : K →+* L) (pub : R0P.Public K) (pub' : R0P.Public L)
    (o : R0P.Openings K) (sel : R0P.Sel K) (hv : pub.variant = pub'.variant) :
    ((R0P.scheduleFamily (K := K)).residuals pub o sel).map g =
      (R0P.scheduleFamily (K := L)).residuals pub' (mapOpenings g o)
        (fun i => g (sel i)) := by
  simp only [R0P.scheduleFamily, List.map_append, List.map_ofFn, Function.comp_def]
  congr 1
  · congr 1
    funext i
    rw [map_initial, hv]
  · congr 1
    funext i
    rw [map_absorption, hv]

#print axioms nodes_two_sums
#print axioms map_nodes
#print axioms map_initial
#print axioms map_absorptionLiteral
#print axioms map_absorption
#print axioms map_family
end AspisR1.ScheduleFamilyFieldTransport
