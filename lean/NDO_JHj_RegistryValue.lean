import NDO_JHj_Seeds
import NDO_JHg_BindingsRegistry
set_option autoImplicit false
namespace AspisR1.JHj_RegistryValue
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

/-- Expected raw fields only. No successful decoder callback is defined. -/
def loader : Array U8 32#usize :=
  ⟨(JHb_DataRegistry.bytes.drop 152).take 32,by rw [JHg_AuditRegistry.loader];decide⟩
def registryProgramdata : Array U8 32#usize :=
  ⟨(JHb_DataRegistry.bytes.drop 184).take 32,by rw [JHg_AuditRegistry.programdata];decide⟩
def verifierProgramdata : Array U8 32#usize :=
  ⟨(JHb_DataEntry.bytes.drop 168).take 32,by rw [JHg_AuditEntry.programdata];decide⟩

def registry : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2 :=
  {flags:=2#u8,bump:=255#u8,pool:=JHj_Seeds.key,authority:=Array.repeat 32#usize 0#u8,
   policy_binding:=r1_pool_adapter.AUDIT_POLICY_BINDING,generation:=1#u64,
   minimum_activation_delay_slots:=1#u64,registry_program:=JHb_Programs.registry,
   loader_program:=loader,programdata_address:=registryProgramdata,programdata_bump:=255#u8,
   executable_hash:=Array.repeat 32#usize 165#u8}

def entry : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2 :=
  {status:=.Active,statement_version:=1#u8,bump:=254#u8,pool:=JHj_Seeds.key,
   verifier_program:=CPH_Program.verifier,profile_binding:=r1_pool_adapter.PROFILE_BINDING,
   release_binding:=r1_pool_adapter.RELEASE_BINDING,loader_program:=loader,
   programdata_address:=verifierProgramdata,programdata_bump:=254#u8,
   executable_hash:=Array.repeat 32#usize 90#u8,expected_upgrade_authority:=Array.repeat 32#usize 0#u8,
   activation_slot:=0#u64,retirement_slot:=18446744073709551615#u64,
   policy_binding:=r1_pool_adapter.AUDIT_POLICY_BINDING}

theorem registry_pool_bytes : (JHb_DataRegistry.bytes.drop 8).take 32=registry.pool.val :=
  JHg_BindingsRegistry.pool
#print axioms registry_pool_bytes

theorem entry_pool_bytes : (JHb_DataEntry.bytes.drop 8).take 32=entry.pool.val :=
  JHg_BindingsRegistry.entry_pool
#print axioms entry_pool_bytes

theorem entry_verifier_bytes : (JHb_DataEntry.bytes.drop 40).take 32=entry.verifier_program.val :=
  JHg_BindingsRegistry.verifier
#print axioms entry_verifier_bytes
end AspisR1.JHj_RegistryValue
