import NNH_Tx2OpenSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bQuerySlots
open Aeneas Aeneas.Std Result AspisR1Stage2
variable (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
abbrev actual := Port3_QueryStage.release (Port4C_RowStd.install
 (Port5Q1_QueryPorts.install (NNH_CorrectConfiguration.configuration m env err r).query))
abbrev model := NFS_QueryOps.installed NJJ_QueryOps.concrete

theorem decode (proof : Slice U8) (i : Usize) :
 (actual m env err r).op21 proof i = model.op21 proof i := rfl

theorem dots (proof : Slice U8) (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
 (actual m env err r).op20 proof g = model.op20 proof g := rfl

theorem circle (v : aspis_core.field.wide_exact.WideExact)
 (q : Array aspis_core.field.wide_exact.WideExact 4#usize) (g : Array U32 5#usize) :
 (actual m env err r).op17 v q g = model.op17 v q g := rfl

theorem line (v : aspis_core.field.wide_exact.WideExact)
 (q : Array aspis_core.field.wide_exact.WideExact 4#usize) (g : Array U32 5#usize) :
 (actual m env err r).op16 v q g = model.op16 v q g := rfl

theorem geometry (g : verifier.QueryGeometry) (i : Usize) :
 (actual m env err r).op18 g i = model.op18 g i := rfl

theorem equality (x y : aspis_core.field.wide_exact.WideExact) :
 (actual m env err r).widePartialEq.eq x y = model.widePartialEq.eq x y := rfl
#print axioms decode
#print axioms dots
#print axioms circle
#print axioms line
#print axioms geometry
#print axioms equality
end AspisR1.NNH_Run5bQuerySlots
end
