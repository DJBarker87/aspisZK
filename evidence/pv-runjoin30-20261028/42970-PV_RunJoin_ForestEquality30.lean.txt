import R1Z.PV_RunJoin_RuntimePrimitives30
import R1Z.BuilderForestAdmissionPort
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ForestEquality30
open Aeneas Aeneas.Std Result

theorem dictionary : BuilderForestAdmissionPort.aspis_core.field.M31.Insts.CoreCmpPartialEqM31 =
    AspisBuilderAdmissionSource.aspis_core.field.M31.Insts.CoreCmpPartialEqM31 := rfl
#print axioms dictionary

theorem digest_ne (a b : Array U32 8#usize) :
    core.array.equality.PartialEqArray.ne BuilderForestAdmissionPort.aspis_core.field.M31.Insts.CoreCmpPartialEqM31
      a b = ok (decide (a≠b)) := by
  rw [dictionary]
  exact PV_RunJoin_RuntimePrimitives30.array_ne a b
#print axioms digest_ne

theorem equal (a b : Array U32 8#usize)
    (h : core.array.equality.PartialEqArray.ne BuilderForestAdmissionPort.aspis_core.field.M31.Insts.CoreCmpPartialEqM31
      a b = ok false) : a=b := by
  rw [digest_ne] at h
  simpa only [Result.ok.injEq,decide_eq_false_iff_not,not_not] using h
#print axioms equal
end R1Z.PV_RunJoin_ForestEquality30
