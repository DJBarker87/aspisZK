# NCC U04 bridge ledger

S2 OPEN; deployed 100-bit target not yet established. Every row is OPEN.
Frozen Rust: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.
Adopted headline: `AspisR1.RPx_Deployed.deployed`; op43/op44 are digest/error.
No XRn join kit, new trust item, model weakening or body-fidelity premise.

NBX modules/results and coherent SInt2 ownership are imported read-only via
NCC_IMPORTS.json. Existing field selection does not instantiate extraction.
The final specific job budget is 60 Kani and 60 Lean, superseding earlier
generic limits in the brief. Metadata runs are recorded separately.

| Slot | Actual native function | Exact SDK argument | Status / missing obligation |
|---|---|---|---|
| op15 | `validate_verifier_policy_v1` | full policy record | OPEN: two-run pending; actual authentication call-site pending. |
| op23 | `decode_pool_v1_pair_forest_terminal_request_v1` | instruction suffix slice | OPEN: slice two-run pending; successful payment-child/caller composition pending. |
| op25 | `VerifierRegistryV1::is_paused` | full registry V1 | OPEN: K001 positive; argument-change control pending; authentication call-site pending. |
| op26 | `VerifierRegistryV1::is_immutable` | full registry V1 | OPEN: two-run and actual SDK caller association pending. |
| op27 | `VerifierRegistryV2::is_paused` | full registry V2 | OPEN: two-run and actual SDK caller association pending. |
| op28 | `VerifierRegistryV2::is_immutable` | full registry V2 | OPEN: two-run and actual SDK caller association pending. |
| op29 | `VerifierRegistryEntryV2::is_active_at` | full entry V2, current_slot | OPEN: two-run and actual SDK caller association pending. |
| op30 | `VerifierRegistryEntryV1::is_active_at` | full entry V1, current_slot | OPEN: two-run and actual SDK caller association pending. |
| op31 | `decode_verifier_registry_v1` | registry account data slice | OPEN: slice two-run and authentication call-site pending. |
| op32 | `decode_verifier_registry_entry_v1` | entry account data slice | OPEN: slice two-run and authentication call-site pending. |
| op33 | `decode_verifier_registry_v2` | registry account data slice | OPEN: slice two-run and authentication call-site pending. |
| op34 | `decode_verifier_registry_entry_v2` | entry account data slice | OPEN: slice two-run and authentication call-site pending. |
| op48 | `decode_master_box` | master account data slice | OPEN: NBX loop induction reused; actual reader/iterator/Box/error/allocator association and caller pending. |
| op49 | `decode_checkpoint_box` | checkpoint account data slice | OPEN: NBX loop induction reused; original reader/canonical digest/Box/error/allocator association and caller pending. |

## Credit boundary

Stage 1 two-run native checks establish local dependence/frame only in their
stated typed or bounded-slice domains, with meaningful input-change controls.
They do not establish arbitrary runtime heap admission or caller extraction.
The private caller used to exercise contract substitution is not automatically
the authentication caller at an SDK opN point. No local check is promoted to
"instantiated by native function (ruling s)" without BOTH required components.

op48/op49 cannot be closed by re-proving NBX's one-row value/frame induction:
the missing piece is the actual original iterator/reader and wrapper execution,
including allocation and mapped errors. A whole-buffer replay is disallowed.
No independent new Lean wrapper can replace that native obligation.

No shipped source changed; ELF rebuild trigger has not fired. Inherited,
not reproduced: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
