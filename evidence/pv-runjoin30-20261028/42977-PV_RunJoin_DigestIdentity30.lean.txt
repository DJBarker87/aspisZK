import R1Z.BuilderForestAdmissionPort
set_option autoImplicit false
namespace R1Z.PV_RunJoin_DigestIdentity30
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort

theorem digest (d : Array U32 8#usize) : pool_v1.pair_forest_copy_builder.digest d = ok d := by
  unfold pool_v1.pair_forest_copy_builder.digest
  change BuilderForestStd.arrayMap (BuiltinFnMut U32 U32) d aspis_core.field.M31Ctor = ok d
  rw [BuilderForestStd.arrayMap_pure _ (fun x : U32 => x) (by intro c x; rfl)]
  congr 1
  apply Subtype.ext
  exact List.map_id d.val
#print axioms digest
end R1Z.PV_RunJoin_DigestIdentity30
