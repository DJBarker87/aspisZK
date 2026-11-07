import NND_RegistryScalarOps
set_option autoImplicit false
noncomputable section
namespace NND_RegistryFlagValues
open Aeneas Aeneas.Std Result AdapterRw aspis_statement.pool_v1.verifier_registry

theorem paused1 (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env) (r : VerifierRegistryV1) :
 (NND_RegistryOps.install base D env).op25 r = ok (r.flags &&& 1#u8 != 0#u8) := by
 change NHY_RegistryReference.flag_ref r.flags 1#u8 = _
 simp only [NHY_RegistryReference.flag_ref,lift,bind_tc_ok]

theorem immutable1 (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env) (r : VerifierRegistryV1) :
 (NND_RegistryOps.install base D env).op26 r = ok (r.flags &&& 2#u8 != 0#u8) := by
 change NHY_RegistryReference.flag_ref r.flags 2#u8 = _
 simp only [NHY_RegistryReference.flag_ref,lift,bind_tc_ok]

theorem paused2 (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env) (r : VerifierRegistryV2) :
 (NND_RegistryOps.install base D env).op27 r = ok (r.flags &&& 1#u8 != 0#u8) := by
 change NHY_RegistryReference.flag_ref r.flags 1#u8 = _
 simp only [NHY_RegistryReference.flag_ref,lift,bind_tc_ok]

theorem immutable2 (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env) (r : VerifierRegistryV2) :
 (NND_RegistryOps.install base D env).op28 r = ok (r.flags &&& 2#u8 != 0#u8) := by
 change NHY_RegistryReference.flag_ref r.flags 2#u8 = _
 simp only [NHY_RegistryReference.flag_ref,lift,bind_tc_ok]

#print axioms paused1
#print axioms immutable1
#print axioms paused2
#print axioms immutable2
end NND_RegistryFlagValues
end
