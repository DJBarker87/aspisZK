# NCC U04 bridge ledger

PILOT RESULT: required contract controls behave correctly on the tested interface;
four actual native getter contracts and one real private native caller pair pass.
See NCC_CONTRACT_PILOT.md. **All fourteen whole-slot rows remain OPEN.**
S2 / deployed 100-bit target not yet established.

Frozen Rust: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
Headline: AspisR1.RPx_Deployed.deployed. op43/op44 are digest/error.
No XRn kit, new trust, body-fidelity premise, headline or metric change.

| Slot | Actual native function | Exact SDK argument | Checked component and remaining obligation |
|---|---|---|---|
| op15 | `validate_verifier_policy_v1` | master.verifier_policy | K053/K054: full typed two-run Result, every initialized field and arbitrary ambient coordinate; actual authentication caller/carrier association OPEN. |
| op23 | `decode_pool_v1_pair_forest_terminal_request_v1` | instruction suffix | K033/K034: two-run whole Result/backing byte, 0≤len≤321; arbitrary-length rejection and actual caller association OPEN. |
| op25 | `VerifierRegistryV1::is_paused` | full V1 registry | K041/K042 full field/ambient two-run; K055 native contract; actual SDK authentication point OPEN. |
| op26 | `VerifierRegistryV1::is_immutable` | full V1 registry | K043/K044 full field/ambient two-run; K056 native contract; K059/K060 private validator context only; SDK authentication point OPEN. |
| op27 | `VerifierRegistryV2::is_paused` | full V2 registry | K045/K046 full field/ambient two-run; K057 native contract; actual SDK authentication point OPEN. |
| op28 | `VerifierRegistryV2::is_immutable` | full V2 registry | K047/K048 full field/ambient two-run; K058 native contract; actual SDK authentication point OPEN. |
| op29 | `VerifierRegistryEntryV2::is_active_at` | full V2 entry, current_slot | K049/K050 full field/ambient two-run; actual SDK authentication point OPEN; native contract candidate not run. |
| op30 | `VerifierRegistryEntryV1::is_active_at` | full V1 entry, current_slot | K051/K052 full field/ambient two-run; actual SDK authentication point OPEN; native contract candidate not run. |
| op31 | `decode_verifier_registry_v1` | registry account data | K025/K026 whole Result/backing byte, 0≤len≤129; arbitrary lengths and actual authentication point OPEN. |
| op32 | `decode_verifier_registry_entry_v1` | entry account data | K027/K028 whole Result/backing byte, 0≤len≤193; arbitrary lengths and actual authentication point OPEN. |
| op33 | `decode_verifier_registry_v2` | registry account data | K029/K030 whole Result/backing byte, 0≤len≤257; arbitrary lengths and actual authentication point OPEN. |
| op34 | `decode_verifier_registry_entry_v2` | entry account data | K031/K032 whole Result/backing byte, 0≤len≤321; arbitrary lengths and actual authentication point OPEN. |
| op48 | `decode_master_box` | master account data | NBX original-reader row/scan/domain induction reused; actual iterator/reader, validation, Box/error/allocator and caller association OPEN. |
| op49 | `decode_checkpoint_box` | checkpoint account data | NBX original-reader row/scan/domain induction reused; actual iterator/canonical digest, Box/error/allocator and caller association OPEN. |

## Meaning of the checks

Every cited pair has a passing two-run check and a failing control changing one
meaningful argument byte, with matching native source, KMX, tool flags, semantic
environment and caps. The final typed-record checks observe an arbitrary field
(and arbitrary byte of each array field), scalar fields exactly, and independent
ambient states. They cover initialized Rust values on valid references, with
existing P6/runtime/ABI admission retained. They do not read padding as initialized
bytes or assert a theorem about invalid references/concurrent mutation.

The slice checks agree on exactly the passed prefix; independent bytes beyond
it may differ. Complete Result equality includes all decoded fields/errors.
K013–020/K023–024 are rejected memcmp unwinding failures with undetermined
properties, not decoder counterexamples or credited controls. K025–034 replace
the harness assumption with guarded per-byte constraints; native bodies and limits
are unchanged. No timed-out or memory-killed shape was replayed.

NCC_DOMAIN_FINDINGS.md records the bounded-slice caller gap. No contract requiring
those upper bounds is used. The real getter contracts have requires(true).

## Stage 3 / extraction

The installed candidate selection and unchanged missing-field retention are the
existing NBX_HeadlineSelection/HeadlineRetention/SeedAdapter results, reused
without re-proving them. Native getter behavior now has the additional local
checks above. No actual SDK authentication caller has been proved to invoke
those fields at its opN point with the same record from ONE native execution.
The private validator pilot is not that enclosing caller. No new per-slot
component of AeneasExtraction is discharged and no row is marked
"instantiated by native function (ruling s)".

op48/op49 cannot advance by repeating NBX's symbolic induction: the native
original iterator/wrapper association is missing. No whole-buffer replay or
unverified decoder/allocator stub is used. No standalone full decoder/Box closure
is inferred from row/value laws. No op53 work is attempted in this lane.

## Budget and next deliverable

Kani 60/60: 27 PASS, 23 semantic counterexamples (20 matching negative controls
plus three machinery controls), ten excluded unwinding failures. No Kani run
remains authorized. Lean reuse audit is recorded separately. No new theorem is
needed merely to restate the outstanding native conclusion as a hypothesis.

Remaining member-by-member native needs are in the table: getter/policy SDK
caller association; decoder arbitrary-length/caller association; original
master/checkpoint loop/Box/error/allocator/caller association. Each needs new
native/P6 evidence. All independent existing Lean selection/induction results
are reused. The next useful target is the actual authentication continuation
under the verified getter contract, with its same decoded-record prestate and
real lower-call domains established, then the source/SDK call-point composition.

No shipped file changed. Inherited ELF pins, NOT rebuilt/reproduced:
default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

## Final focused Lean reuse audit

NCC_L002 / NCC_ReuseAudit: exit0, wall2.125393630s, peakRSS5,580,244KiB, swap0; source revision bb2ac643ca24facb072417224e2b6a15552ed182 plus the exact dirty source hash in its receipt. All54 inherited NBX roots use only propext/Classical.choice/Quot.sound or none (NCC_AXIOMS.json). All NBX modules are imported without re-proving them. No new theorem, slot witness or extraction premise discharge is added. Actual resolved Aeneas objects are pinned; this is a focused reuse audit, not a new release manifest replay.

Budget: 60/60 Kani; one successful Lean compile, with two submission slots conservatively charged out of60 (L001 transport/no host setup observed; never resubmitted). Every remaining row above requires new native/P6 evidence, so there is no independent new Lean-only closure left to attempt. No further Kani launch is authorized.

Final retention/freeze: all584 imported private-cache files and all219 resolved Aeneas objects remain unchanged; the retained cache now has585 files, adding only NCC_ReuseAudit.olean. No own prover/controller is live. Own1,765,790,485-byte Rust target and empty temporary directory were removed; cache, source snapshots and receipts remain (NCC_CACHE_END.json / NCC_CLEANUP.json). Final repository audit confirms all496 crate/program files and root Cargo.toml/lock equal frozen source; host audit confirms492 unchanged files plus the four exact cfg-instrumented parent hashes used by K060 (NCC_FROZEN_FINAL.json / NCC_HOST_SOURCE_AUDIT.json). No evidence file exceeds20MB, no binary/object/ELF is committed, and no wallet/key operation or push occurred.
