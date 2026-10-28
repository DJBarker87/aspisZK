import NCX_CallerDomains
import NCX_Carrier
import NCX_EntryFields
import NCX_EntryFixture
import NCX_EntryValue
import NCX_FieldLaws
import NCX_FixtureCarriers
import NCX_FixtureObservations
import NCX_Install
import NCX_JHuObservations
import NCX_LengthRejection
import NCX_Observations
import NCX_ParsedBodies
import NCX_RegistryFields
import NCX_RegistryFixture
import NCX_RegistryValue
import NCX_ResultObservations
import NCX_Status
import NCX_StatusSpec
import NCX_WindowFrames
import NCX_ZeroLaws
import NCX_Reference.Types
import NCX_Reference.Funs
#print axioms NCX_CallerDomains.registry_array
#print axioms NCX_CallerDomains.entry_array
#print axioms NCX_CallerDomains.registry_word
#print axioms NCX_CallerDomains.entry_word
#print axioms NCX_CallerDomains.registry_byte
#print axioms NCX_CallerDomains.entry_byte
#print axioms NCX_CallerDomains.registry_reserved
#print axioms NCX_CallerDomains.entry_reserved
#print axioms NCX_CallerDomains.binding_scan
#print axioms NCX_Carrier.status_roundtrip
#print axioms NCX_Carrier.status_surjective
#print axioms NCX_Carrier.error_roundtrip
#print axioms NCX_Carrier.error_surjective
#print axioms NCX_Carrier.registry_roundtrip
#print axioms NCX_Carrier.registry_surjective
#print axioms NCX_Carrier.entry_roundtrip
#print axioms NCX_Carrier.entry_surjective
#print axioms NCX_EntryFields.read_version
#print axioms NCX_EntryFields.read_status
#print axioms NCX_EntryFields.read_statement_version
#print axioms NCX_EntryFields.read_mode
#print axioms NCX_EntryFields.read_pool
#print axioms NCX_EntryFields.read_verifier
#print axioms NCX_EntryFields.read_profile
#print axioms NCX_EntryFields.read_release
#print axioms NCX_EntryFields.read_loader
#print axioms NCX_EntryFields.read_programdata
#print axioms NCX_EntryFields.read_executable_hash
#print axioms NCX_EntryFields.read_upgrade_authority
#print axioms NCX_EntryFields.read_activation
#print axioms NCX_EntryFields.read_retirement
#print axioms NCX_EntryFields.read_policy
#print axioms NCX_EntryFields.read_bump
#print axioms NCX_EntryFields.read_programdata_bump
#print axioms NCX_EntryFixture.source
#print axioms NCX_EntryValue.nz_pool
#print axioms NCX_EntryValue.nz_verifier
#print axioms NCX_EntryValue.nz_profile
#print axioms NCX_EntryValue.nz_release
#print axioms NCX_EntryValue.nz_loader
#print axioms NCX_EntryValue.nz_programdata
#print axioms NCX_EntryValue.nz_executable_hash
#print axioms NCX_EntryValue.nz_policy
#print axioms NCX_EntryValue.z_upgrade_authority
#print axioms NCX_EntryValue.valid
#print axioms NCX_FieldLaws.equal
#print axioms NCX_FieldLaws.zero
#print axioms NCX_FieldLaws.read32
#print axioms NCX_FieldLaws.word
#print axioms NCX_FixtureCarriers.registry_pool
#print axioms NCX_FixtureCarriers.registry_policy
#print axioms NCX_FixtureCarriers.registry_program
#print axioms NCX_FixtureCarriers.registry_loader
#print axioms NCX_FixtureCarriers.registry_programdata
#print axioms NCX_FixtureCarriers.registry
#print axioms NCX_FixtureCarriers.entry_pool
#print axioms NCX_FixtureCarriers.entry_verifier
#print axioms NCX_FixtureCarriers.entry_profile
#print axioms NCX_FixtureCarriers.entry_release
#print axioms NCX_FixtureCarriers.entry_policy
#print axioms NCX_FixtureCarriers.entry_loader
#print axioms NCX_FixtureCarriers.entry_programdata
#print axioms NCX_FixtureCarriers.entry
#print axioms NCX_FixtureObservations.registry
#print axioms NCX_FixtureObservations.entry
#print axioms NCX_FixtureObservations.installed_registry
#print axioms NCX_FixtureObservations.installed_entry
#print axioms NCX_Install.selected
#print axioms NCX_Install.op33_result
#print axioms NCX_Install.op34_result
#print axioms NCX_JHuObservations.commute
#print axioms NCX_JHuObservations.registry
#print axioms NCX_JHuObservations.entry
#print axioms NCX_JHuObservations.runtime_retained
#print axioms NCX_JHuObservations.ncv_retained
#print axioms NCX_LengthRejection.registry
#print axioms NCX_LengthRejection.entry
#print axioms NCX_Observations.registry_injective
#print axioms NCX_Observations.entry_injective
#print axioms NCX_ParsedBodies.registry
#print axioms NCX_ParsedBodies.entry
#print axioms NCX_RegistryFields.read_version
#print axioms NCX_RegistryFields.read_flags
#print axioms NCX_RegistryFields.read_mode
#print axioms NCX_RegistryFields.read_bump
#print axioms NCX_RegistryFields.read_pool
#print axioms NCX_RegistryFields.read_authority
#print axioms NCX_RegistryFields.read_policy
#print axioms NCX_RegistryFields.read_generation
#print axioms NCX_RegistryFields.read_delay
#print axioms NCX_RegistryFields.read_program
#print axioms NCX_RegistryFields.read_loader
#print axioms NCX_RegistryFields.read_programdata
#print axioms NCX_RegistryFields.read_executable_hash
#print axioms NCX_RegistryFields.read_programdata_bump
#print axioms NCX_RegistryFixture.source
#print axioms NCX_RegistryValue.nz_pool
#print axioms NCX_RegistryValue.nz_policy
#print axioms NCX_RegistryValue.nz_program
#print axioms NCX_RegistryValue.nz_loader
#print axioms NCX_RegistryValue.nz_programdata
#print axioms NCX_RegistryValue.nz_executable_hash
#print axioms NCX_RegistryValue.z_authority
#print axioms NCX_RegistryValue.valid
#print axioms NCX_ResultObservations.registry_injective
#print axioms NCX_ResultObservations.entry_injective
#print axioms NCX_Status.active
#print axioms NCX_StatusSpec.value
#print axioms NCX_WindowFrames.read32_local
#print axioms NCX_WindowFrames.word_local
#print axioms NCX_WindowFrames.registry_disjoint
#print axioms NCX_WindowFrames.entry_disjoint
#print axioms NCX_WindowFrames.registry_commute
#print axioms NCX_WindowFrames.entry_commute
#print axioms NCX_WindowFrames.outside
#print axioms NCX_ZeroLaws.zero
#print axioms NCX_ZeroLaws.nonzero
#print axioms NCX_ZeroLaws.magic
#print axioms NCX_Reference.decode_verifier_registry_v2
#print axioms NCX_Reference.decode_verifier_registry_entry_v2
#print axioms NCX_Reference.validate_verifier_registry_v2
#print axioms NCX_Reference.validate_verifier_registry_entry_v2
#print axioms NCX_Reference.read32
#print axioms NCX_Reference.word
#print axioms NCX_Reference.zero
#print axioms NCX_Reference.equal
#print axioms NCX_Reference.status
