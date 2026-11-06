# NJI scope

All eight baseline rows OPEN. Exact original obligations retained in NJI_BASELINE_ROWS.json.xz, derived from authoritative NIU_LEDGER.json.xz.

Cohort boundary: canonical AdapterRwModel from NER headline closure; policy validator op15, registry V1 decoder op31, entry V1 decoder op32, master/checkpoint op48/op49. V1 internal validators use full record/error carriers. op43/op44 are digest/error. NBN_U04 higher interpretations stay OPEN until these source associations are installed.

## TX2:150 decode_verifier_policy_v1

Frozen body SHA256: 8516a1eb481df9fc0f25414e72629d0fefb1620c5d93ed375e4c3a5c577fc668.

Callees: crates/aspis-statement/src/pool_v1/format.rs::validate_verifier_policy_v1. Resolve each current status against NIU, never stale embedded local_status.

Analogue method: TX2:151 NHY_PolicyModel.actual_slot: native policy contract plus extracted-reference equality and installed-slot carrier law.

Domain: 384-byte master,192-byte Pool checkpoint,128/256-byte registries and192/320-byte entries; both version/flag alternatives; canonical digests, immutable/unpaused policy and active-at-slot checks. This is the Pool checkpoint, not the1768-byte verifier checkpoint.

Caller clauses: complete same-input/carrier/Result/state/effects and exact Std constructors, windows, unwrap safety. No acceptance-only claim. Root hypotheses restricted by (aq)(2).

## TX2:152 decode_pool_v1_pair_forest_checkpoint_v1

Frozen body SHA256: c32073d5d44e6ac99ff318d8c5597fa30101d458de3f1f13beda2b4af25168b4.

Callees: crates/aspis-statement/src/atomic_statement.rs::decode_digest_canonical. Resolve each current status against NIU, never stale embedded local_status.

Analogue method: TX2:154/155 NFY_Part053: canonical digest scanner complete Result and native loop step/frame, symbolic induction; no whole-buffer native proof.

Domain: 384-byte master,192-byte Pool checkpoint,128/256-byte registries and192/320-byte entries; both version/flag alternatives; canonical digests, immutable/unpaused policy and active-at-slot checks. This is the Pool checkpoint, not the1768-byte verifier checkpoint.

Caller clauses: complete same-input/carrier/Result/state/effects and exact Std constructors, windows, unwrap safety. No acceptance-only claim. Root hypotheses restricted by (aq)(2).

## TX2:153 decode_pool_v1_pair_forest_master_v1

Frozen body SHA256: 3df9c97adf58c2cfa319b984f63fe744062826cd7229148b2f205866c8c4bdaf.

Callees: crates/aspis-statement/src/pool_v1/format.rs::decode_pool_identity_v1, crates/aspis-statement/src/pool_v1/format.rs::decode_verifier_policy_v1, crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::validate_master. Resolve each current status against NIU, never stale embedded local_status.

Analogue method: TX2:204 NHY_RegistryJoin.cohort: exact header/range/window native cuts, CLOSED child instantiation, complete Result pipeline/cohort join.

Domain: 384-byte master,192-byte Pool checkpoint,128/256-byte registries and192/320-byte entries; both version/flag alternatives; canonical digests, immutable/unpaused policy and active-at-slot checks. This is the Pool checkpoint, not the1768-byte verifier checkpoint.

Caller clauses: complete same-input/carrier/Result/state/effects and exact Std constructors, windows, unwrap safety. No acceptance-only claim. Root hypotheses restricted by (aq)(2).

## TX2:157 validate_master

Frozen body SHA256: 99d9dc42a2881ad9422eccec887f19ea0be2cf9695b964b55ceb8fc8a48004f9.

Callees: crates/aspis-statement/src/pool_v1/format.rs::validate_verifier_policy_v1. Resolve each current status against NIU, never stale embedded local_status.

Analogue method: TX2:151 NHY_PolicyModel.actual_slot: scalar guard cuts and CLOSED policy child, full error order.

Domain: 384-byte master,192-byte Pool checkpoint,128/256-byte registries and192/320-byte entries; both version/flag alternatives; canonical digests, immutable/unpaused policy and active-at-slot checks. This is the Pool checkpoint, not the1768-byte verifier checkpoint.

Caller clauses: complete same-input/carrier/Result/state/effects and exact Std constructors, windows, unwrap safety. No acceptance-only claim. Root hypotheses restricted by (aq)(2).

## TX2:201 decode_verifier_registry_entry_v1

Frozen body SHA256: cfaf776818741077d96a8a4e9cad524e0abcc762480ece06bed6da9dd1be168f.

Callees: crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierEntryStatusV1::try_from, crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_entry_v1. Resolve each current status against NIU, never stale embedded local_status.

Analogue method: TX2:202 NIS_EntryJoin (namespace NIJ_EntryJoin.cohort): complete record constructor/arguments, status decode, validator cut, original-buffer windows, native pass/control and emitted pipeline/cohort join.

Domain: 384-byte master,192-byte Pool checkpoint,128/256-byte registries and192/320-byte entries; both version/flag alternatives; canonical digests, immutable/unpaused policy and active-at-slot checks. This is the Pool checkpoint, not the1768-byte verifier checkpoint.

Caller clauses: complete same-input/carrier/Result/state/effects and exact Std constructors, windows, unwrap safety. No acceptance-only claim. Root hypotheses restricted by (aq)(2).

## TX2:203 decode_verifier_registry_v1

Frozen body SHA256: cccb29d6dc204872c46d4ad48e725796ef2537a9c6a160f9dce8c82667cb18b9.

Callees: crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_v1. Resolve each current status against NIU, never stale embedded local_status.

Analogue method: TX2:204 NHY_RegistryJoin.cohort: all-input first-error header/parser pipeline, original-buffer window transport, complete validator Result and carrier.

Domain: 384-byte master,192-byte Pool checkpoint,128/256-byte registries and192/320-byte entries; both version/flag alternatives; canonical digests, immutable/unpaused policy and active-at-slot checks. This is the Pool checkpoint, not the1768-byte verifier checkpoint.

Caller clauses: complete same-input/carrier/Result/state/effects and exact Std constructors, windows, unwrap safety. No acceptance-only claim. Root hypotheses restricted by (aq)(2).

## TX2:206 validate_verifier_registry_entry_v1

Frozen body SHA256: 2e288c482f3969c007bd30ad4480b326bc77fa933431b2008aa7243e90b570cb.

Callees: crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::has_no_retirement_slot, crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::has_no_retirement_slot, crates/aspis-statement/src/pool_v1/verifier_registry.rs::required_binding_is_zero. Resolve each current status against NIU, never stale embedded local_status.

Analogue method: TX2:207 NHY_NCXValidators.entry_source: actual native/reference identity, complete two-sided record/error carrier, CLOSED zero/status/retirement children.

Domain: 384-byte master,192-byte Pool checkpoint,128/256-byte registries and192/320-byte entries; both version/flag alternatives; canonical digests, immutable/unpaused policy and active-at-slot checks. This is the Pool checkpoint, not the1768-byte verifier checkpoint.

Caller clauses: complete same-input/carrier/Result/state/effects and exact Std constructors, windows, unwrap safety. No acceptance-only claim. Root hypotheses restricted by (aq)(2).

## TX2:208 validate_verifier_registry_v1

Frozen body SHA256: e1e005ed5c21403af7594059c6e6158fcc14b1b60d9ac071d897fcfa3e949318.

Callees: crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_immutable, crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_immutable, crates/aspis-statement/src/pool_v1/verifier_registry.rs::required_binding_is_zero. Resolve each current status against NIU, never stale embedded local_status.

Analogue method: TX2:209 NHY_NCXValidators.registry_source: actual native/reference identity, complete two-sided record/error carrier, CLOSED immutable/zero children.

Domain: 384-byte master,192-byte Pool checkpoint,128/256-byte registries and192/320-byte entries; both version/flag alternatives; canonical digests, immutable/unpaused policy and active-at-slot checks. This is the Pool checkpoint, not the1768-byte verifier checkpoint.

Caller clauses: complete same-input/carrier/Result/state/effects and exact Std constructors, windows, unwrap safety. No acceptance-only claim. Root hypotheses restricted by (aq)(2).

## Current callee resolution

TX2:146 digest decode CLOSED;151 policy validator CLOSED;192 status CLOSED;193/195 retirement CLOSED;197/199 immutable CLOSED;205 zero-binding CLOSED. TX2:149 identity decoder OPEN and outside this job: TX2:153 cannot close without that slice-boundary packet. Internal150/157/206/208 depend on this job.

## Extraction finding NJI-F1

Single Charon run produced all eight LLBC roots. Aeneas0 omitted decoder152/153/201/203 after the missing Iterator.any warning. No emitted-body closure for those rows; no hidden replacement. Master157 emitted but capacity parameter propagation and library IterMut ABI prevent aggregate compilation. Core split retains policy150 and validators206/208 without altered bodies. Raw artifacts and L003 failure retained.

## Final model and method resolution

| Row | Emitted/model association | Final state |
|---|---|---|
|150|NJI_PolicyParser.source, natural body with canonical CLOSED NHY_PolicyModel op15 through NJI_PolicyPort; NJI_PolicyTotal.native_source combines exact coordinate cut and unrestricted length stage|Local audited candidate; next ledger gate required|
|152|No emitted definition; native checkpoint iteration and Lean NJI_CheckpointLoop support reuse NFY/NHY frame/extensionality method|OPEN, missing body/full decoder composition|
|153|No emitted definition; policy150/master157 candidate children; identity149 outside slice OPEN|OPEN|
|157|NJI_MasterModel.source full guards/Result; NJI_MasterCut.native_source and child_arguments; NJI_MasterIteration.source_association instantiates emitted capacity callback and canonical std source induction|Local audited candidate; next ledger gate required|
|201|No emitted definition; entry coordinate/status/validator/input-frame cut follows NIS method but lacks complete parser/op32 join|OPEN|
|203|No emitted definition; registry coordinate/validator/input-frame cut follows NHY method but lacks complete parser/op31 join|OPEN|
|206|NJI_V1Models.entry_source and NJI_V1Join.entry_source/entry_domain; complete canonical AdapterRw record/error carrier, actual native full Result contract|Local audited candidate; next ledger gate required|
|208|NJI_V1Models.registry_source and NJI_V1Join.registry_source/registry_domain; complete canonical AdapterRw record/error carrier, actual native full Result contract|Local audited candidate; next ledger gate required|

The authoritative row obligations do not name a pre-existing standalone internal policy-decoder/master-validator model definition; these explicit full-result definitions expose those internal semantics. Installed decoder slots31/32/48/49 are not claimed CLOSED by defining an internal helper. Full original row obligations and hashes remain in NJI_BASELINE_ROWS.json.xz. NJI_HYPOTHESES.json checks the four proposed root statements against(aq)(2); the raw statements and all58 roots are retained from the actual combined import.
