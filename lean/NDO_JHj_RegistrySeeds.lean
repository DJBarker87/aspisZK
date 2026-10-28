import NDO_JHj_RegistryValue
set_option autoImplicit false
namespace AspisR1.JHj_RegistrySeeds
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

def registry : Slice (Slice U8) := (Array.make 3#usize [
  r1_pool_adapter.VERIFIER_REGISTRY_V2_SEED,JHj_Seeds.key.to_slice,
  (Array.make 1#usize [JHj_RegistryValue.registry.bump]).to_slice]).to_slice

def registryProgramdata : Slice (Slice U8) := (Array.make 2#usize [
  JHb_Programs.registry.to_slice,
  (Array.make 1#usize [JHj_RegistryValue.registry.programdata_bump]).to_slice]).to_slice

def entry : Slice (Slice U8) := (Array.make 5#usize [
  r1_pool_adapter.VERIFIER_ENTRY_V2_SEED,JHj_Seeds.key.to_slice,
  r1_pool_adapter.PROFILE_BINDING.to_slice,r1_pool_adapter.RELEASE_BINDING.to_slice,
  (Array.make 1#usize [JHj_RegistryValue.entry.bump]).to_slice]).to_slice

def verifierProgramdata : Slice (Slice U8) := (Array.make 2#usize [
  CPH_Program.verifier.to_slice,
  (Array.make 1#usize [JHj_RegistryValue.entry.programdata_bump]).to_slice]).to_slice

theorem registry_count : registry.val.length=3 := rfl
#print axioms registry_count
theorem registry_programdata_count : registryProgramdata.val.length=2 := rfl
#print axioms registry_programdata_count
theorem entry_count : entry.val.length=5 := rfl
#print axioms entry_count
theorem verifier_programdata_count : verifierProgramdata.val.length=2 := rfl
#print axioms verifier_programdata_count
end AspisR1.JHj_RegistrySeeds
