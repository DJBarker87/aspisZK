import RPv_FIy_ValueRangeList
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_ValueFamilyList
open Aeneas Aeneas.Std
open FIv_NativeValue (K)
open FIy_ValueTail (Openings)
open FIy_FrontierStep (Selectors)

theorem value (p : FIw_PublicModel.Public) (o : Openings) (s : Selectors) :
    List.ofFn (FIy_ValuePacked.rangeModel o s)++List.ofFn (FIy_ValuePacked.conservation o s)=
      R0P.valueFamily.residuals (FIw_PublicModel.ofPublic p) (FIw_PublicModel.openings o) (FIw_PublicModel.selector s) := by
  have mapped : List.ofFn (FIy_ValuePacked.rangeModel o s)=
      (List.ofFn (FIy_ValueRangeShape.unweighted o)).map (fun x=>FIy_ValuePacked.selector s*x) := by
    rw [List.map_ofFn]
    rfl
  rw [mapped,FIy_ValueRangeList.value,FIy_ValueRangeShape.selector]
  rfl
#print axioms value
end AspisR1.FIy_ValueFamilyList
end
