import R0P.Occupancy
import RPv_ValueFamilyFieldTransport
import RPv_DigestFamilyFieldTransport
set_option autoImplicit false
namespace AspisR1.FJk_OccupancyMap
variable {K L : Type} [Field K] [Field L]
theorem lanes (g : K →+* L) (input output expected : K) (o : Fin 16 → K) :
    (R0P.occupancyLanesLiteral input output expected o).map g =
    R0P.occupancyLanesLiteral (g input) (g output) (g expected) (fun i=>g (o i)) := by
  simp only [R0P.occupancyLanesLiteral,List.map_append,List.map_cons,List.map_nil,
    List.map_ofFn,Function.comp_def,map_add,map_sub,map_mul,map_one]
/-- Exact field transport for the existing family and mapped public. -/
theorem value (g : K →+* L) (pub : R0P.Public K) (o : R0P.Openings K) (sel : R0P.Sel K) :
    (R0P.occupancyFamily.residuals pub o sel).map g =
    R0P.occupancyFamily.residuals (SpendDataMap.mapPublic g pub)
      (ValueFamilyFieldTransport.mapOpenings g o) (fun i=>g (sel i)) := by
  unfold R0P.occupancyFamily
  rw [lanes]
  have expected : g (R0P.occupancyExpected pub.variant)=
      R0P.occupancyExpected pub.variant := by
    cases pub.variant <;> simp only [R0P.occupancyExpected,map_one,map_zero]
  rw [expected]
  rfl
#print axioms lanes
#print axioms value
end AspisR1.FJk_OccupancyMap
