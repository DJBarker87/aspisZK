import RPv_ValueFamilyFieldTransport
import R0P.Asset

/-! Generic field transport for both actual asset/withdrawal scalar residuals.
Only the public fields actually used by this family require correspondence. -/
set_option autoImplicit false
namespace AspisR1.AssetFamilyFieldTransport
open AspisR1.ValueFamilyFieldTransport
variable {K L : Type} [Field K] [Field L]

theorem map_scalar_lanes (g : K →+* L) (v : R0P.Variant) (present : Bool)
    (input output privateTerm withdrawalTerm : K) :
    (R0P.assetScalarLanes v present input output privateTerm withdrawalTerm).map g =
      R0P.assetScalarLanes v present (g input) (g output) (g privateTerm) (g withdrawalTerm) := by
  cases v <;> cases present <;>
    simp only [R0P.assetScalarLanes, List.map_cons, List.map_nil, map_add,
      Bool.false_eq_true, ↓reduceIte]

theorem map_option_getD_zero (g : K →+* L) (amount : Option K) :
    g (amount.getD 0) = (amount.map g).getD 0 := by
  cases amount <;> simp only [Option.getD_none, Option.getD_some,
    Option.map_none, Option.map_some, map_zero]

theorem map_option_isSome (g : K →+* L) (amount : Option K) :
    (amount.map g).isSome = amount.isSome := by
  cases amount <;> rfl

theorem map_family (g : K →+* L) (pub : R0P.Public K) (pub' : R0P.Public L)
    (o : R0P.Openings K) (sel : R0P.Sel K)
    (hv : pub'.variant = pub.variant) (ha : pub'.assetId = g pub.assetId)
    (hw : pub'.withdrawalAmount = pub.withdrawalAmount.map g) :
    ((R0P.assetFamily (K := K)).residuals pub o sel).map g =
      (R0P.assetFamily (K := L)).residuals pub' (mapOpenings g o) (fun i => g (sel i)) := by
  simp only [R0P.assetFamily, map_scalar_lanes, hv, ha, hw, map_option_isSome,
    map_mul, map_sub, map_option_getD_zero, mapOpenings]

#print axioms map_scalar_lanes
#print axioms map_option_getD_zero
#print axioms map_option_isSome
#print axioms map_family
end AspisR1.AssetFamilyFieldTransport
