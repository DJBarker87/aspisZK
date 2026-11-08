import NNH_Run5bGeometrySlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_GeometryStdSlots
open Aeneas Aeneas.Std Result NNH_Run5bGeometrySlots
variable (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
theorem array : @(ops m env err r).op0 = @canonical.op0 := rfl
theorem iterator : @(ops m env err r).op1 = @canonical.op1 := rfl
theorem any : @(ops m env err r).op3 = @canonical.op3 := rfl
theorem empty : @(ops m env err r).op4 = @canonical.op4 := rfl
theorem equal (x y : U32) : (ops m env err r).op5 x y = canonical.op5 x y := rfl
theorem zero : (ops m env err r).op6 = canonical.op6 := rfl
theorem prefixes (s : Slice U32) : (ops m env err r).op13 s = canonical.op13 s := rfl
theorem mapped : @(ops m env err r).mapIterator = @canonical.mapIterator := rfl
#print axioms array
#print axioms iterator
#print axioms any
#print axioms empty
#print axioms equal
#print axioms zero
#print axioms prefixes
#print axioms mapped
end AspisR1.NNV_GeometryStdSlots
end
