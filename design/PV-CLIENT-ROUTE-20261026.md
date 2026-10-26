# Proof-account operational client — 26 October 2026

The operational planner is now wired to the selected64 proof-account route on
`codex/pv-client-20261026`. This implements owner LOG D162 decision 1 under the
lead's explicit continuation authorization. The earlier routing counterexample
at `149855299b` is superseded. **The privacy target is not yet established.**
No theorem, observer, simulator, error envelope or cryptographic assumption is
weakened. The soundness release ledger is unchanged.

## Before and after

| Entry | Before, `149855299b` | Current branch |
|---|---|---|
| `devnet_spend::main`, `action=prove` → `plan::run` → `plan::prove` | `prove_masked_retrying`, Generic96; independently supplied publication key | `RealR1_client::prove_for_proof_accounts`; ordered eight-key callback, S2, public nonce = retained proof-account key, two private 32-byte seeds |
| Python `r1_devnet_spend.py` orchestration | one independently selected proof account; saved plan could bypass mapping | `Client64_proof_accounts.proof_plan`, eight retained keys before invocation, exclusive claim, persisted original request, checked successful `attempts - 1` mapping and artifact hashes |
| Publication | independently supplied proof account | selected key appears at settlement index 10 and stage1 index 0; Python uses its retained key for account creation/upload |
| Error/resume path | legacy saved-plan reuse | legacy independent-key ABI rejected; failed/entered/interrupted mapping requires manual recovery; no automatic new ledger/key allocation after ambiguous invocation |
| Inventory | known flat key/recovery paths | nested attempt keys, generated/staging copies, manifests, legacy and selected recovery paths; discovery/IO/mode/symlink errors prevent completion before RPC |
| Generic96 library APIs and other probes | exported generic/fixture APIs | unchanged; no call/fallback from the operational runner/planner |

Eight reviewed production/test files were transplanted with `git show` from
parked candidate `1dfbd5711684d73fc2ff664cfae9ae78f7dd34f8`, rather than merging
its branch. They are the planner/account helper and the six Python
retention/inventory/driver/test files listed in `stage1-review.md`. The new
runner-route test and integration harness are this job's additions. No file
under `crates/` or `programs/` changes relative to `research`; no three-ELF
rebuild trigger is introduced.

## Concrete caller and observable boundary

The headline's `rust` must describe the complete operational execution rooted
at **`devnet_spend::main` with `action=prove`**, entered from
`scripts/r1_devnet_spend.py` through `Client64_proof_accounts.proof_plan` and
its subprocess callback. Its selected inner function is
`devnet_spend::plan::prove`. `client-pins.json` records the exact file:line chain
through the selected adapter, `generate_for_mask_nonce`, retry owner,
`prove_masked_attempt`, reservation and private prover body. A symbol name
alone is not an `FSExperiments`, `RunJoin`, or `RustRealRefinement` instance.

The implementation retains the selected adapter and all called crate bytes.
Only `Rejected` retries; entropy errors, malformed public serialization,
duplicate/reservation failures and other fatal errors keep their native order.
The new client ABI first checks the eight nonzero distinct account keys, before
statement processing. The proof directory and note-recovery write precede
opening the ledger and entropy/prover call. Reservation occurs before masks
and salts; rejected/fatal/interrupted/unused attempt keys and ledgers remain
retained. The ledger is scoped to the retained proof invocation. The production
helper allocates fresh keys and permanently claims that invocation, and never
re-enters an ambiguous run or silently resets its ledger. Arbitrarily replacing
private ledger storage is not certified; E2 remains explicit.

On success, `attempts`, selected index/key, `mask_audit`, proof length/count,
`prove_wall_seconds`, instruction accounts and order, statement/proof files and
manifest transitions remain observables of this client. Python adds subprocess
errors, saved requests/plans, signed receipts, creation/upload/stage1/settlement,
RPC errors/reconciliation and timing. Inventory has its own visible validation
failures. These must all be in the experiment's observer/effect image. We do
not erase error origins, retry counts, cleanup, ledger IO, oracle/TLS history,
output lengths, publication or the new retained mapping from the argument.

## Validation and integration

31 lifecycle/inventory Python tests pass. Three optimized Rust runner tests
pass: invalid ABI/duplicate account keys, first/retry/eighth-attempt mapping,
and lexical exclusion of alternative prover calls from the operational source.
The latter is a regression guard on the pinned runner/planner, not a general
machine-code call-graph absence theorem. Generic APIs remain elsewhere.

The runtime gate invokes the actual built `devnet_spend` subprocess to produce
proofs with OS entropy and the actual durable ledger. It checks the successful
key against retained ledger records, reopens that ledger, invokes the unchanged
selected adapter with the same nonce under a second valid statement, requires
`Semantic`, and verifies every durable record is unchanged. Thus reuse across
statements fails closed inside that ledger. Rust key-list tests separately
exercise rejection at the operational ABI boundary.

The gate executes actual signed LiteSVM transactions against all three pinned
ELFs: verifier stage1 writes a distinct checkpoint while leaving proof/public
inputs unchanged; stage2 must return the exact expected ASR8 without changing
inputs; the actual planner's Pool settlement must return that ASR8, and the
runner validates the resulting lane and consumed nullifier marker. Default
and devnet proofs bind their respective embedded Pool/Registry identities.
Raw proof/public carrier and authenticated state images are preloaded fixtures;
this is not network deployment, live registry provisioning, or carrier
create/upload evidence. No production wallet is used. Task keys and ledgers
remain on the host; no cleanup/refund transaction occurs.

All four fixture cases are accepted: default transfer/withdrawal and devnet
transfer/withdrawal, each on attempt 1, with the exact pinned Pool. The acceptance
record is [`runtime-02-public/acceptance.json`](../evidence/pv-client-20261026/runtime-02-public/acceptance.json).
Its scope receipt is [`runtime-02/receipt.json`](../evidence/pv-client-20261026/runtime-02/receipt.json):
source `ce5583a4a2`, exit 0, wall **195.957410694 s**, peak RSS **547352 KiB**,
**0 swaps**. Full source revision/argv/limits/input fingerprint are in that
receipt; each execution JSON includes instruction accounts, signed transaction
hash/length, CU, runtime logs and return hash. Binary/compiler/CPU/ELF SHA/size
pins are in [`runtime-bundle.json`](../evidence/pv-client-20261026/runtime-bundle.json).
The 1,295-file SHA-256/size source dictionary and exact file:line chain are in
[`client-pins.json`](../evidence/pv-client-20261026/client-pins.json), generated by
`python3 tools/pv-client-20261026/PV_client_pins.py`; use `--check` to verify.
It deliberately overapproximates called source rather than omitting transitive
crate/build/checker inputs. Cargo dependencies are pinned by the lockfiles;
this is not a new whole-machine dependency-closure proof.

The first runtime run retained a successful default transfer, then rejected
an incorrectly default-bound statement under the devnet ELF. The changed gate
uses the pinned devnet Pool/Registry IDs rather than changing the verifier or
misreporting the rejection. Its failed receipt and replacement, the initial
harness import error, and an overbroad lexical-test failure are all retained.
See [`README.md`](../evidence/pv-client-20261026/README.md) for every run's resources,
including the reservation refusal and the recorded wait-rule breach (110.6 s
instead of the required 180 s). The retry independently passed admission. No failed
run was repeated unchanged. Every Rust command uses optimized code and one admitted
6G/8G/no-swap/64-task scope at a time, four Cargo jobs. No Lean/Kani theorem is
changed or needed to establish this operational source/fixture condition.

## Release-ledger rows to pin

The lead should pin these **row shapes**, without treating this document as an
edit to `design/RELEASE-LEDGER-20261025.md`:

| Row | Identity / evidence fields | Disposition |
|---|---|---|
| Selected proof-account client route and caller-error behavior | client revision, `devnet_spend::main` action ABI, source dictionary digest, binary SHA/size, exact compiler/target/features/flags, configured signer, Python bundle SHA dictionary, ordered callback and retained key/ledger policy, positive/duplicate receipts | Operational Generic96 mismatch removed in this branch; source/fixture subgate closes, installation/adoption and full error/event refinement remain |
| Representable statement domain and publication/observer association | same client pins, complete request/public bytes image, successful attempt index/nonce/key, proof/statement hashes, create/upload/stage1/settlement instructions and program IDs, runtime ASR8/state effects | Informed by tested fixtures and mapping tests; universal statement/observer association remains |
| Freeze and all three ELF association | unchanged crate/program dictionary; default/devnet/Pool SHA/size and loaded Program/ProgramData readback; locked dependency and host binary pins | Current pinned-ELF fixture integration supplied; not a changed-verifier reproduction or live cluster attestation |
| Prover rewrite adoption | exact selected client + final prover/controller/Drop source pins, source/effect/native equivalence, fixed-coin 1000 whole-prover comparisons, all applicable artifact identities, quiet median <15s and H5 slowdown <=10% | Client wiring contributes one necessary condition; other gates remain |
| L1 outcome counts and joint mask/count/TLS/oracle transcript; E2 | manifest/claim/reservation effects, all retry/abort/error/publication/cleanup events on this exact client, producer-to-model and joint law evidence | Still open; mock fault tests and successful native fixtures do not discharge native event transport or E2 |
| L2/CT-v2; L3 platform; Real-prover refinement; final closure/axioms | exact final client/prover binary/compiler/CPU and complete observer, native two-run/source joins, coherent dependency replay and axioms | Retained obligations; no side-channel or refinement closure claimed |

Before: “operational planner uses Generic96; selected client route has no native
runner instance or current pinned-ELF acceptance receipt.” After: “operational
planner uses selected64, concrete retained-key mapping is pinned and tested,
and the measured fixture acceptance/duplicate subgate has evidence.” The exact
formal premise `RustRealRefinement` is **retained**, with no quantifier, carrier,
conclusion, simulator or bad-event change. E1/E2, seed/fuel/query-scan events,
complete real RunJoin, native owner/Drop/error bindings and all L1/L2/L3
requirements remain. This removes the checked source mismatch, not the deployed
privacy theorem's refinement hypothesis.

## Final handoff

Stage commits are separate: wiring `b7cd400a55`, source/test validation
`5270ce4bf3`, final successful runtime source `ce5583a4a2`, acceptance evidence
`5228877938`, followed by the source-pin and document commits. The preliminary
audit is retained in git and `source-audit.json`; its baseline guard intentionally
fails on the newly authorized wiring and is not the current pin checker.

`git diff --stat research.. -- crates programs` produces no output. No live
chain transaction, key cleanup, push, merge, existing Lean-module edit, Lean
compile, Kani run or launcher-range edit was made. Lean 0/10 (20500–20549
unused), Kani 0/10; seven capped Rust commands (two rejected builds/tests,
one runtime diagnostic failure, four successful commands), no overlapping
scopes. The implementation source mismatch is removed and the fixture
acceptance condition measured; additional theorem budget cannot turn those
facts into a complete native privacy refinement.

Next concrete deliverable: the lead adopts/pins the client bundle with its
configured signer and retained storage policy, then binds the complete native
client event/effect trace and its randomness/error marginals to `rust.real`,
`rust.observe` and RunJoin on the final prover pins. Live carrier publication,
installation attestation and all remaining adoption/performance/side-channel
rows still require their named evidence. No release-ledger row is silently
changed here.
