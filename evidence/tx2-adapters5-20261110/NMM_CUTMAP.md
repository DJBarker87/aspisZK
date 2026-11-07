# NMM cut-to-packet inventory

Target not yet established. This is an inventory, not a validated clause map. Full law/footprint/domain matching remains pending for each cut. No implemented stub is credited.

## TX2:217

- TX2:146 `crates/aspis-statement/src/atomic_statement.rs::decode_digest_canonical`: CLOSED; roots `NFY_NEQ_DecodeScalar.digest_result_state_effects`, `NFY_NEQ_DecodeScalar.digest_word_domain`, `NGE_NEQ_ParserCanonical.some_canonical`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

## TX2:233

- TX2:016 `crates/aspis-core/src/field.rs::M31::to_le_bytes`: CLOSED; roots `NFY_NEE_M31SerializerDomain.primitive`, `NFY_NEE_M31SerializerDomain.width`, `NFY_NEE_M31SerializerDomain.widths_distinct`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:039 `crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes`: CLOSED; roots `NFY_NFD_WideSerialization.carrier_roundtrip`, `NFY_NFD_WideSerialization.result_state_effects`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:216 `programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_checkpoint_box`: CLOSED; roots `AspisR1.NKY_BoxSource.checkpoint`, `AspisR1.NKY_BoxTotal.checkpoint`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:217 `programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_lane_from_pool_release`: OPEN; roots ``. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:218 `programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_master_box`: CLOSED; roots `AspisR1.NKY_BoxSource.master`, `AspisR1.NKY_BoxTotal.master`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:229 `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data`: CLOSED; roots `NHJ_DataPacket.substitute`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:231 `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::key`: CLOSED; roots `NFU_AdapterGetters.key`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:234 `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_invariant_release_registry`: OPEN; roots ``. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:235 `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_distinct_accounts`: CLOSED; roots `NHJ_DistinctPacket.seven`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:236 `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_account`: CLOSED; roots `NHJ_ReadonlyPacket.readonly`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:237 `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_buffer`: CLOSED; roots `NFU_AdapterGetters.readonly`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:238 `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_verifier_checkpoint`: CLOSED; roots `NHJ_CheckpointPacket.substitute`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

## TX2:234

- TX2:151 `crates/aspis-statement/src/pool_v1/format.rs::validate_verifier_policy_v1`: CLOSED; roots `NHY_PolicyModel.actual_slot`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:194 `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::is_active_at`: CLOSED; roots `NIJ_ActiveSlots.op30_exact`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:196 `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::is_active_at`: CLOSED; roots `NIJ_ActiveSlots.op29_exact`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:197 `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_immutable`: CLOSED; roots `NHY_RegistryPipeline.immutable_v1`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:198 `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_paused`: CLOSED; roots `NHY_RegistryPipeline.paused_v1`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:199 `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_immutable`: CLOSED; roots `NHY_RegistryPipeline.immutable_v2`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:200 `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_paused`: CLOSED; roots `NHY_RegistryPipeline.paused_v2`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:201 `crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v1`: CLOSED; roots `NJY_Roots.entry`, `NJQ_Entry.source`, `NJQ_Canonical.entry_result`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:202 `crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v2`: CLOSED; roots `NIJ_EntryJoin.cohort`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:203 `crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v1`: CLOSED; roots `NJY_Roots.registry`, `NJQ_Registry.source`, `NJQ_Canonical.registry_result`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:204 `crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v2`: CLOSED; roots `NHY_RegistryJoin.cohort`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:220 `programs/r1-cost-probe/src/r1_pool_adapter.rs::pool_program_id`: CLOSED; roots `NHJ_DeployedIds.pool_actual`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:225 `programs/r1-cost-probe/src/r1_pool_adapter.rs::registry_program_id`: CLOSED; roots `NHJ_DeployedIds.registry_actual`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:229 `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data`: CLOSED; roots `NHJ_DataPacket.substitute`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:231 `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::key`: CLOSED; roots `NFU_AdapterGetters.key`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

- TX2:236 `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_account`: CLOSED; roots `NHJ_ReadonlyPacket.readonly`. Cut clause status: NOT YET TRANSCRIBED OR VALIDATED.

## Binding interpretation under (bl)

No callee packet law will be translated into a Rust assume. Pure child replies, including error variants, are arbitrary Rust values; argument/reply logging and full parent comparison establish native plumbing only. Lean instantiates CLOSED roots at those exact calls. Allocation failures stop with the prior event prefix; allocation metadata, pure Box ownership bookkeeping and pure Drop are outside the obligation. Returned Box payloads remain full typed values. Account/return-data writes from Drop remain in scope. These classifications supersede allocator/cleanup blockers in the earlier NMM_FAILING_STEP draft.

For immutable slice children, a candidate existing-argument channel is a real harness-local backing allocation containing the original input region and disjoint UnsafeCell log regions. Raw derived pointers must stay in that allocation, and shared input bytes remain immutable. This channel is unvalidated and earns no credit until controls pass. No integer-address reconstruction, writable static or function pointer is permitted.
