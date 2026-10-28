import NDO_NCX_EntryFields
set_option autoImplicit false
namespace NCX_EntryValue
open Aeneas Aeneas.Std Result AspisR1
open NCX_EntryFields

def value : NCX_Reference.VerifierRegistryEntryV2 :=
  ⟨.Active,1#u8,254#u8,pool,verifier,profile,release,loader,programdata,254#u8,executable_hash,upgrade_authority,activation,retirement,policy⟩
theorem nz_pool : NCX_Reference.required_binding_is_zero pool=ok false := by
  unfold NCX_Reference.required_binding_is_zero
  simp only [lift,bind_tc_ok]
  apply NCX_ZeroLaws.nonzero
  · change pool.val.length ≤ 768;rw [pool.property];scalar_tac
  · change NCV_ZeroStep.byte pool.to_slice 0 ≠ 0#u8
    decide
  · change 0 < pool.val.length;rw [pool.property];scalar_tac
#print axioms nz_pool
theorem nz_verifier : NCX_Reference.required_binding_is_zero verifier=ok false := by
  unfold NCX_Reference.required_binding_is_zero
  simp only [lift,bind_tc_ok]
  apply NCX_ZeroLaws.nonzero
  · change verifier.val.length ≤ 768;rw [verifier.property];scalar_tac
  · change NCV_ZeroStep.byte verifier.to_slice 0 ≠ 0#u8
    decide
  · change 0 < verifier.val.length;rw [verifier.property];scalar_tac
#print axioms nz_verifier
theorem nz_profile : NCX_Reference.required_binding_is_zero profile=ok false := by
  unfold NCX_Reference.required_binding_is_zero
  simp only [lift,bind_tc_ok]
  apply NCX_ZeroLaws.nonzero
  · change profile.val.length ≤ 768;rw [profile.property];scalar_tac
  · change NCV_ZeroStep.byte profile.to_slice 0 ≠ 0#u8
    decide
  · change 0 < profile.val.length;rw [profile.property];scalar_tac
#print axioms nz_profile
theorem nz_release : NCX_Reference.required_binding_is_zero release=ok false := by
  unfold NCX_Reference.required_binding_is_zero
  simp only [lift,bind_tc_ok]
  apply NCX_ZeroLaws.nonzero
  · change release.val.length ≤ 768;rw [release.property];scalar_tac
  · change NCV_ZeroStep.byte release.to_slice 0 ≠ 0#u8
    decide
  · change 0 < release.val.length;rw [release.property];scalar_tac
#print axioms nz_release
theorem nz_loader : NCX_Reference.required_binding_is_zero loader=ok false := by
  unfold NCX_Reference.required_binding_is_zero
  simp only [lift,bind_tc_ok]
  apply NCX_ZeroLaws.nonzero
  · change loader.val.length ≤ 768;rw [loader.property];scalar_tac
  · change NCV_ZeroStep.byte loader.to_slice 0 ≠ 0#u8
    decide
  · change 0 < loader.val.length;rw [loader.property];scalar_tac
#print axioms nz_loader
theorem nz_programdata : NCX_Reference.required_binding_is_zero programdata=ok false := by
  unfold NCX_Reference.required_binding_is_zero
  simp only [lift,bind_tc_ok]
  apply NCX_ZeroLaws.nonzero
  · change programdata.val.length ≤ 768;rw [programdata.property];scalar_tac
  · change NCV_ZeroStep.byte programdata.to_slice 0 ≠ 0#u8
    decide
  · change 0 < programdata.val.length;rw [programdata.property];scalar_tac
#print axioms nz_programdata
theorem nz_executable_hash : NCX_Reference.required_binding_is_zero executable_hash=ok false := by
  unfold NCX_Reference.required_binding_is_zero
  simp only [lift,bind_tc_ok]
  apply NCX_ZeroLaws.nonzero
  · change executable_hash.val.length ≤ 768;rw [executable_hash.property];scalar_tac
  · change NCV_ZeroStep.byte executable_hash.to_slice 0 ≠ 0#u8
    decide
  · change 0 < executable_hash.val.length;rw [executable_hash.property];scalar_tac
#print axioms nz_executable_hash
theorem nz_policy : NCX_Reference.required_binding_is_zero policy=ok false := by
  unfold NCX_Reference.required_binding_is_zero
  simp only [lift,bind_tc_ok]
  apply NCX_ZeroLaws.nonzero
  · change policy.val.length ≤ 768;rw [policy.property];scalar_tac
  · change NCV_ZeroStep.byte policy.to_slice 0 ≠ 0#u8
    decide
  · change 0 < policy.val.length;rw [policy.property];scalar_tac
#print axioms nz_policy
theorem z_upgrade_authority : NCX_Reference.required_binding_is_zero upgrade_authority=ok true := by
  unfold NCX_Reference.required_binding_is_zero
  simp only [lift,bind_tc_ok]
  apply NCX_ZeroLaws.zero _ 32 rfl (by omega)
#print axioms z_upgrade_authority
theorem valid : NCX_Reference.validate_verifier_registry_entry_v2 value=ok (.Ok ()) := by
  simp only [NCX_Reference.validate_verifier_registry_entry_v2,value,NCX_Reference.POOL_V1_VERIFIER_REGISTRY_FLAGS_MASK,
    nz_pool,nz_verifier,nz_profile,nz_release,nz_loader,nz_programdata,nz_executable_hash,nz_policy,z_upgrade_authority,lift,bind_tc_ok]
  rfl
#print axioms valid
end NCX_EntryValue
