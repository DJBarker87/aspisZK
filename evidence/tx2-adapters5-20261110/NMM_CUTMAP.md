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

## Native 217 channel and limits

The real repr(C,align(4)) harness allocation contains bytes[768], a disjoint UnsafeCell byte-argument region[768], a disjoint eight-word reply region per32-byte input window, and a disjoint tag region[768]. The digest input reference borrows directly from the original carrier. Pointer addition retains that allocation's provenance; no integer/address reconstruction or writable static is used. Logs are harness instrumentation, not account writes. Every child Result arm is represented (seven AtomicStatementError variants or eight arbitrary u32 words mapped to valid M31 tuple values); no canonicality or decoder law is assumed. The root-error branch restricts ONLY the reply discriminant to Err and includes all seven error variants. An arbitrary input observer establishes immutable-frame equality; a log observer rejects unmatched call records. No mutable child argument exists. The stopped branch has no observable event before this pure decoder and no SBF unwinding catch.

K002 (whole unrestricted returning-reply shape) and K003 (header predicate with the same full reference) timed out90s; retired. K004/K005 root-error plumbing passes are local branch evidence only. K006's overly broad reply mutant timed out90s and is retired; a changed local outcome-tag mutant is being tested, not retried unchanged. Pure return error codes all map to InvalidAccountData, so dependence is on the child Result discriminant/call prefix, not on the discarded error variant.

The observed-frontier shape removes the second reference Box allocation and checks one arbitrary frontier row, retaining complete Result discrimination, all scalars and root fields. Existing NKF_LaneConstructor.constructor supplies frontier extensionality if that shape passes. This is a changed proof shape after K002, not a rename or cap increase.

## Literal obligation classifications (bl)(4), (bf)(2)

The inventory's U16 whole-spend prose remains visible in every baseline. Its seven-account admission, proof58295 scan, request relation and ASF8 reconstruction are caller obligations. They are not predicates on217's sole byte-slice argument or234's registry-only arguments.233 owns its seven input descriptors/authentication fields; proof scanning and reconstruction belong to242. This is a scope classification, not removal of those obligations.

The opaque cuts carry no Rust packet assumptions. Their closed-law instantiations occur in Lean, at the recorded arguments:217's decoder binds `NLK_LaneDigest.source`, which directly uses `NFY_NEQ_DecodeScalar.digest_result_state_effects`; `NMM_LaneReplies.run_closed/closed/adopted` compose all21 occurrence slots. Byte-array extent32 follows from the actual source slice conversions. Canonical words follow from the CLOSED decoder on Ok, not from an input assumption or a Rust assume.

234's data-error cuts map to `NHJ_DataPacket.substitute`: exact receiver, its `OwnedAccount::data` view/Err payload, immutable account fields, and no other writes. K017/K022 use only the explicitly selected finite Custom(u32) error-reply branch; their original input snapshots are Ok byte vectors, so composition with the CLOSED data law would rule out that particular cut-reply branch. They are universal plumbing controls, not evidence of an actual data-error execution or a234 certificate. Other returned-error families and Ok data replies remain separate obligations.

The legacy registry prototype havocs complete V1 registry/entry Results and all four typed `VerifierEntryStatusV1` variants (Pending, Active, Paused, Retired). `NIJ_ActiveSlots.op30_exact`/`op29_exact` are total on that typed enum; no status<=2 premise is introduced. No parser/registry/PDA law is encoded in Rust. Already-CLOSED scalar, key, policy and readonly functions execute their actual frozen bodies in these prototypes; this is stronger local execution evidence, but it is not represented as a fully audited all-cut234 packet.

For immutable borrowed data replies, a real typed local byte carrier supplies arbitrary contents at the selected original extent; the program neither returns that reference nor uses its allocation identity or mutates it. The row's value/frame view is therefore the relevant observation. The original owned Vec bytes and the independently havoced reply bytes are not identified in Rust. Their equality, when required, comes only from the CLOSED data packet in Lean. No SDK guard is fabricated.

PDA laws remain the existing quantified runtime op38, not a seed-to-key value assumption. Legacy calls receive the retained master-key pointer and can recover a disjoint local record. V2's registry ProgramData call instead receives the stack-local registry-program bytes and one-byte bump, with a stack-local loader program. Those arguments carry no retained harness context. No static, integer-address search, write through shared key bytes or invented global runtime log is used to bridge that gap.

`NMM_PdaProjection` is the bounded argument-window composition: seed count<=5, every seed<=32 bytes, program32. Native logs capture an arbitrary seed/byte window and the full typed reply; the source-order counter preserves the call prefix. It earns no credit until its current proof and native/control gates are green.

The returning-Err and returning-Ok checks are an internal exhaustive case split. A success/endpoint condition may not appear in a row root. `NMM_OutcomeCases.complete` requires both cases before deriving a total returning relation. K032 covers all returning Err outcomes at768 bytes; the attempted Ok case K033 timed out. No accepted-only packet is emitted.

No mutation, cleanup or account-data/return-data write is hidden in these pure helper prototypes. Allocator internals and pure cleanup are excluded by (bl); returned payloads are not discarded. Source-stopped arms retain their prefix only, and no post-abort heap state is asserted.
