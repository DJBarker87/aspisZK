import NCX_RegistryFields
set_option autoImplicit false
namespace NCX_RegistryValue
open Aeneas Aeneas.Std Result AspisR1
open NCX_RegistryFields

def value : NCX_Reference.VerifierRegistryV2 :=
  ⟨2#u8,255#u8,pool,authority,policy,generation,delay,program,loader,programdata,255#u8,executable_hash⟩
theorem nz_pool : NCX_Reference.required_binding_is_zero pool=ok false := by
  unfold NCX_Reference.required_binding_is_zero
  simp only [lift,bind_tc_ok]
  apply NCX_ZeroLaws.nonzero
  · change pool.val.length ≤ 768;rw [pool.property];scalar_tac
  · change NCV_ZeroStep.byte pool.to_slice 0 ≠ 0#u8
    decide
  · change 0 < pool.val.length;rw [pool.property];scalar_tac
#print axioms nz_pool
theorem nz_policy : NCX_Reference.required_binding_is_zero policy=ok false := by
  unfold NCX_Reference.required_binding_is_zero
  simp only [lift,bind_tc_ok]
  apply NCX_ZeroLaws.nonzero
  · change policy.val.length ≤ 768;rw [policy.property];scalar_tac
  · change NCV_ZeroStep.byte policy.to_slice 0 ≠ 0#u8
    decide
  · change 0 < policy.val.length;rw [policy.property];scalar_tac
#print axioms nz_policy
theorem nz_program : NCX_Reference.required_binding_is_zero program=ok false := by
  unfold NCX_Reference.required_binding_is_zero
  simp only [lift,bind_tc_ok]
  apply NCX_ZeroLaws.nonzero
  · change program.val.length ≤ 768;rw [program.property];scalar_tac
  · change NCV_ZeroStep.byte program.to_slice 0 ≠ 0#u8
    decide
  · change 0 < program.val.length;rw [program.property];scalar_tac
#print axioms nz_program
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
theorem z_authority : NCX_Reference.required_binding_is_zero authority=ok true := by
  unfold NCX_Reference.required_binding_is_zero
  simp only [lift,bind_tc_ok]
  apply NCX_ZeroLaws.zero _ 32 rfl (by omega)
#print axioms z_authority
theorem valid : NCX_Reference.validate_verifier_registry_v2 value=ok (.Ok ()) := by
  simp only [NCX_Reference.validate_verifier_registry_v2,value,NCX_Reference.POOL_V1_VERIFIER_REGISTRY_FLAGS_MASK,
    nz_pool,nz_policy,nz_program,nz_loader,nz_programdata,nz_executable_hash,z_authority,lift,bind_tc_ok]
  rfl
#print axioms valid
end NCX_RegistryValue
