import RPu_ValueFamilyFieldTransport
import R0P.Path

/-! Exact transport of the retained path selector and residual family.
The high/low marginal sums and contiguous source residual lists are preserved. -/
set_option autoImplicit false
namespace AspisR1.PathFamilyFieldTransport
open AspisR1.ValueFamilyFieldTransport
variable {K L : Type} [Field K] [Field L]

theorem map_high (g : K →+* L) (sel : R0P.Sel K) (h : Fin 64) :
    g (R0P.g2High sel h) = R0P.g2High (fun i => g (sel i)) h := by
  simp only [R0P.g2High, map_sum]

theorem map_low (g : K →+* L) (sel : R0P.Sel K) (l : Fin 16) :
    g (R0P.g2Low sel l) = R0P.g2Low (fun i => g (sel i)) l := by
  simp only [R0P.g2Low, map_sum]

theorem map_sumHigh (g : K →+* L) (sel : R0P.Sel K)
    (start count : Nat) (bound : start + count ≤ 64) :
    g (R0P.g2SumHigh sel start count bound) =
      R0P.g2SumHigh (fun i => g (sel i)) start count bound := by
  simp only [R0P.g2SumHigh, R0P.g2_fold_add, zero_add, List.sum_ofFn,
    map_sum, map_high]

theorem map_selector (g : K →+* L) (sel : R0P.Sel K) :
    g (R0P.pathSelector sel) = R0P.pathSelector (fun i => g (sel i)) := by
  simp only [R0P.pathSelector, map_mul, map_add, map_sumHigh, map_low]

theorem map_lanes (g : K →+* L) (selector : K) (o : R0P.Openings K) :
    (R0P.pathLanes selector o).map g =
      R0P.pathLanes (g selector) (mapOpenings g o) := by
  simp only [R0P.pathLanes, List.map_append, List.map_cons, List.map_nil,
    List.map_ofFn, Function.comp_def, map_mul, map_sub, map_one, mapOpenings]

theorem map_family (g : K →+* L) (pub : R0P.Public K) (pub' : R0P.Public L)
    (o : R0P.Openings K) (sel : R0P.Sel K) :
    ((R0P.pathFamily (K := K)).residuals pub o sel).map g =
      (R0P.pathFamily (K := L)).residuals pub' (mapOpenings g o)
        (fun i => g (sel i)) := by
  simp only [R0P.pathFamily, map_lanes, map_selector]

#print axioms map_high
#print axioms map_low
#print axioms map_sumHigh
#print axioms map_selector
#print axioms map_lanes
#print axioms map_family
end AspisR1.PathFamilyFieldTransport
