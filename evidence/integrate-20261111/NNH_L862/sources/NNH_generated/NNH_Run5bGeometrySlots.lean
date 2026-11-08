import NNH_Run5bGeometryUnits
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bGeometrySlots
open Aeneas Aeneas.Std Result
variable (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
abbrev ops := Port5Q1_GeometryTerminal.install (NNH_CorrectConfiguration.configuration m env err r).geometry
abbrev canonical := NFN_NEW_GeometryDictionary.adopted

theorem point (u : Usize) : (ops m env err r).op15 u = canonical.op15 u := rfl
theorem line (u : Usize) : (ops m env err r).op14 u = canonical.op14 u := rfl
theorem one : (ops m env err r).op7 = canonical.op7 := by
 apply Eq.trans (b := (.ok 1#u32 : Result U32))
 · exact NNH_Run5bGeometryUnits.installed_one err _
 · exact NNH_Run5bGeometryUnits.canonical_one.symm
theorem subtract (x y : U32) : (ops m env err r).op8 x y = canonical.op8 x y := rfl
theorem multiply (x y : U32) : (ops m env err r).op9 x y = canonical.op9 x y := rfl
theorem double (x : U32) : (ops m env err r).op10 x = canonical.op10 x := rfl
theorem inverse (x : U32) : (ops m env err r).op11 x = canonical.op11 x :=
 by
 calc
  (ops m env err r).op11 x = Port4C_InverseExecution.inverse_owned x :=
   NNH_Run5bGeometryUnits.installed_inverse err _ x
  _ = canonical.op11 x := rfl
#print axioms point
#print axioms line
#print axioms one
#print axioms subtract
#print axioms multiply
#print axioms double
#print axioms inverse
end AspisR1.NNH_Run5bGeometrySlots
end
