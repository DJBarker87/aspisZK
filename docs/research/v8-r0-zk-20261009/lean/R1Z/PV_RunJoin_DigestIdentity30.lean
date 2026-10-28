import R1Z.BuilderForestAdmissionPort
set_option autoImplicit false
namespace R1Z.PV_RunJoin_DigestIdentity30
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort

theorem map_loop (xs : List U32) :
    BuilderForestStd.mapLoop (BuiltinFnMut U32 U32) xs aspis_core.field.M31Ctor =
      ok (xs,aspis_core.field.M31Ctor) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hf : (BuiltinFnMut U32 U32).call_mut aspis_core.field.M31Ctor x =
        ok (x,aspis_core.field.M31Ctor) := rfl
    rw [BuilderForestStd.mapLoop,hf]
    simp only [bind_tc_ok,ih]
#print axioms map_loop

theorem digest (d : Array U32 8#usize) : pool_v1.pair_forest_copy_builder.digest d = ok d := by
  unfold pool_v1.pair_forest_copy_builder.digest
  change BuilderForestStd.arrayMap (BuiltinFnMut U32 U32) d aspis_core.field.M31Ctor = ok d
  unfold BuilderForestStd.arrayMap
  rw [map_loop]
  simp only [bind_tc_ok]
  rw [if_pos d.property]
#print axioms digest
end R1Z.PV_RunJoin_DigestIdentity30
