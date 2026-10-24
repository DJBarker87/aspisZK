# Cap16 source-owner certificate and next native boundary

Unmerged candidate `codex/cx-prover-rw-20261023`, continuation base
`ece5baabbc9c975d631aae8d5ca716e28ad4f268`. This is the new owner-stage
allocation; the exhausted stage3 ledger is unchanged. No native source,
protocol, feature, wire, security contract, wallet or key change.

## Established statement

`R1Z.ProverRwRngOwnerCertificate.universal_cap16` quantifies over **every**
32-byte nonce and typed finite `Tape`, with arbitrary full64-byte replies,
all u8 error tags, partial writes, rejected half patterns and initial cursor.
It first proves `old_owner nonce p = owner nonce p`. The returned value includes
both complete provider and `Result<Secrets,Error>`, including errors.

For each admitted extraction execution `owner nonce p = .ok (after,status)`,
it constructs one ordered sequence of actual body-invocation states that
replays both source owners. It proves immutable replies, cursor increment by
exact draw count, count <=16, full ordered replies at contiguous original
indices, a fresh zero64 input at each draw, all reply indices available, and
identical final suffix. `status` remains arbitrary: `.Err (.Os tag)` and
`.Err .RepeatedZeroBlock` are admitted just as `.Ok secrets` is. Tape
unavailability is extraction failure outside admission, never an OS error.
The common scan preserves nonce rejection before any draw. `body_progress`
proves retry<16 and an exact checked increment for every continuation;
`fill_event` proves the cursor increment cannot overflow on an available tape.
No tape enumeration or concrete32/64-byte reduction is used.

Before (historical): `concrete_zero_then_one` was only the all-one nonce,
a zero block followed by an all-one block, with arbitrary untouched suffix.
The Kani cut was only cap1 and prior draw count<128; the local differential
was only26,214 cases. After: arbitrary nonce, arbitrary typed finite tape,
universal concrete source-body induction and same-state replay. No old
premise was silently removed: this is a new stronger theorem with the same
explicit extraction/value-installation boundary. Native API remains
`generate_for_mask_nonce(nonce) -> Result<Secrets,Error>`; the isolated
prototype returns `(provider,Result<Secrets,Error>)`.

The complete statements of `Replay`, `OwnerReplay`, `events`, `afterFill`,
`ErasureFns`, provider and both source bodies are in the focused audit.
`Replay` contains actual single-body evaluation equations, not a desired
old/new owner-output conclusion. `OwnerReplay` contains only the actual
common nonce scan, replay and return-order conversion. There is no equality
premise hiding the theorem's conclusion.

## Source coverage and trust boundary

`tools/prover-rw-20261023/rng-owner/source-map.json` and the packet's
`source-coverage.json` bind the exact native owner to the borrowed source
adapter. Changes are only the extra mutable Tape argument, replacement of
`getrandom::fill(bytes.as_mut())?` with `tape.draw(&mut bytes)?`, naming,
and the already explicit u8 error carrier. The unchanged source-derived
owned cap16 implementation is also present byte-for-byte. Charon/Aeneas
extract the entire borrowed owner, rather than postulating a world meaning
for the old pure emitted interface. All8 local translated declarations are
transparent. The LLBC embedded source equals the prototype; LLBC hash is
`cfb6f9bec8a6d002ed6f1e141649334256af3d17d7837b27cbd811ddeedc364d`
(558149 bytes). The borrowed From/draw/body/loop/owner emission is retained
verbatim. The read-only event-source binding checks both actual guard/zero64/identity-
borrow prefixes and exactly one primitive call per active body; the full
source bodies are printed in audit11439. All13 shared emitted declarations match after removing only
comments/attributes/whitespace. The actual source-derived new and old body
are concretely instantiated in `body_same`, then `loops_same`, the replay,
and `universal_cap16`. `draw_factor` checks the mechanically selected full
tail cut against the actual new body. No generic theorem replaces this
concrete instantiation.

The historical Kani cut is **not** a Lean hypothesis, axiom or bridge premise.
The new checked symbolic body theorem supersedes its logical role. Its
prior-count<128 restriction is numerically sufficient for actual cap16
counts from zero (<=16, next<=17<65536), as separately checked in
`historical_cut_sufficient`. The universal result also permits larger initial
Tape cursors and proves checked usize increments from availability and the
finite vector bound, without applying the restricted Kani cut there.

Retained boundaries: existing pinned extraction/runtime primitive policy;
transparent value-level Zeroizing new/deref/deref_mut installation; two
unused `ErasureFns` callbacks; u8 prototype error carrier. No native error
layout association, error-to-model map, physical drop/zeroization,
world/refinement law, E1/E2, callback/cap8 or joint L1/L2 assumption is added.
Only standard axioms occur in the checked source theorems. The native source
still matches the manager base; the host native workspace and its historical
revision labels do not establish a new native identity. Exact source hashes,
LLBC source coverage and this branch's commits identify this proof packet.

## Validation and retained failures

The adaptation generator now strips the generated `maxHeartbeats1000000`
and `maxRecDepth2048` commands; raw generator evidence is unchanged. The
four original shared sources/objects were snapshotted before replacement;
Emission, Nonzero, Control and Tape were rebuilt in that order under default
options (11400–11403). Only the changed Emission and its affected closure
were rebuilt. New job modules were compiled individually, each after its
smallest required predecessor. The final source certificate passed11438;
the single focused final audit11439 passes against committed proof source
`ad9e91a840067eae7a44e8ab7f103b0e59b24698`, never a full frozen manifest.
It prints all22 new theorem axiom reports (only propext, Classical.choice,
Quot.sound) and the complete source/hidden-structure statements. Exit0,
wall1.79s, peak RSS3,847,484KiB, swap0. Every launch, including failed attempts, has an immutable
source/dependency receipt and full diagnostic/axiom output in `rng-owner/`.

The exhausted stage3 remains100/100 Lean. At the source-certificate stage,
this **new** ledger used39/60 actual Lean launches, cumulative139/160.
No new Kani run: cumulative44/60, all16 unused runs retained. Final audit11439 adds one: new40/60, remaining20; cumulative140/160 Lean.
Kani remains44/60, remaining16. There were14 successful and26 failed new
Lean launches, all retained. Lean scopes preserve5G/7G, Rust/extraction
6G/8G, zero swap, TasksMax64; launch reservations stay below55GiB. No memory
failure, cap increase, full-manifest launch, native gate or timing run.

Retained failures include all proof scripts and logs11405–11417,
11419–11421,11423–11429,11431,11435,11437. Tuple/uncurry normalization and
incorrect automation caused local proof failures;11411 and11420 reached
**default** heartbeat limits and were replaced with constrained/manual
symbolic steps, not higher limits. A proposed local reducibility attribute
was rejected by Lean and removed; no unsafe reducibility option was enabled.
The final sources contain no custom reduction tactic. Charon001 failed
before compilation because the process PATH lacked rustup; receipt
finalization also could not locate rustc. Its logs/time/preflight and a
recovered receipt are retained. The changed explicit-PATH launch succeeded.
A read-only common-declaration parser initially grouped following structures
with a preceding definition; corrected declaration boundaries now check13
shared declarations. No failed result is counted as accepted evidence.
All prior native changing-tape counterexamples, opaque extraction rejection,
Kani unwind34 failure, and preflight failures remain untouched.

## Next source-impact and extraction plan

This is a design/extraction plan only. No native change is authorized in this
stage. Next concrete producer is
`crates/aspis-r1-cost-probe/src/RealR1_client.rs:prove_for_proof_accounts`,
whose selected S2 callback calls `generate_for_mask_nonce(proof_account(k))`
and maps its error to `Error::Entropy`. The actual eight-attempt owner is
`prover.rs:prove_masked_retrying_with` and private `retry_attempt`
(lines611–639); `ATTEMPT_CAP=8` at542. Reservation is in
`StateOnlyAttemptSecrets::reserve_and_build_pool_v1_pair_forest_mask_material_v1`
(state_only_entropy.rs405–457), entered from `prove_masked_with_attempt`
(prover.rs181–191) through `prove_masked_attempt`.

Minimal proposed ownership plumbing:

1. Keep native `StateOnlyAttemptEntropyError::Os(getrandom::Error)` and the
   actual `getrandom::fill` leaf. Extend an isolated source-derived generic
   provider prototype to the real error carrier first. Do not replace it with
   u8 or assume a layout/association in the native proof. An explicit owned
   provider returns `(P, Result<(), getrandom::Error>)`, with partial buffer
   writes and provider state exposed on failure. Retain existing Zeroizing
   storage/drop calls; prove their separate installation obligation rather
   than inferring it from the value-level theorem.
2. Prototype a source-derived selected callback with signature
   `next_attempt(P, k) -> (P, Result<Secrets, Error>)`. Invoke the public
   nonce policy once at each entered attempt, preserving its mutable state.
   It remains arbitrary/adaptive. Thread P outside Result through
   `prove_masked_retrying_with` / `retry_attempt`. The cap/variant guards return
   P unchanged and never call the callback. Callback failure returns its
   advanced P with exactly `Error::Entropy`. No provider clone/reset per call.
3. On body success return P with the exact proof/audit/attempt count. On
   `Error::Rejected`, recurse at k+1 with the same advanced P and callback
   state. On any fatal body/reservation error return the same advanced P;
   do not roll back draws or durable nonce reservations. Duplicate nonce or
   reservation failure stays fatal in the current source; do not turn it into
   a retry or refund reservation. Preserve reserve-before-derivation and the
   pre-reserved single-use acknowledgment. The ledger remains one shared
   mutable durable store across all attempts and calls. No keys are created,
   destroyed or transferred by this design.
4. Extract the **actual** callback plus retry owner and relevant error/
   reservation branches into a new prefixed isolated module, with exact
   source spans/substitution manifests. Reuse this cap16 certificate only
   at its concrete entropy-call boundary. Prove the cap8 loop against actual
   body statuses and actual reservation effects, retaining rejected/fatal
   suffixes and nonce-policy state. A generic callback law or RunJoin
   structure containing the desired equality is not a source producer.
5. Associate the successful native64-byte return with the existing
   `ProverCommitPublicNonce40.Raw` and its schedule/error history. Existing
   `E1` stays literally `∀ context raw, law context raw =
   1 / (Fintype.card Raw : ℚ)`. It is conditional successful-return uniformity,
   not a world/refinement law. Prove source transport of the same event and
   context separately. Preserve E2's durable reservation requirement and
   all original error carriers. Do not add independence/freshness or a
   witness-independent retry law as a hypothesis to bridge a missing source
   refinement.

Expected native impact, once separately authorized: entropy owner/provider
leaf in `aspis-prover`; selected callback and cap8 owner in
`aspis-r1-cost-probe`; isolated extraction producers and focused proofs.
No protocol/wire/feature/security-contract change is proposed. Any actual
crates/programs/build-input edit triggers **all three** ELF rebuilds and
current identity gates, alongside the complete event/status and performance
gates. This job does not authorize or run them.

## Open release gates

The universal gate above establishes only this concrete source-derived
cap16 entropy-owner predecessor. Native provider/error-layout/E1 association,
physical cleanup, actual callback/cap8 source binding, body/duplicate/ledger
state, world/refinement and joint L1/L2 transport remain open. Other candidate
gates and H5 identity assessment remain open. Conjunct1 and the actual security
target are not established; candidate stays unadopted, unmerged and unpushed.

Current required ELF targets are default
`f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`,
devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`,
Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`.
They were not rebuilt or newly verified: no native source changed. Historical
artifact evidence is reused only under its original identity. Native adoption
still needs all current artifact/runtime/event gates, H5-aligned slowdown
<=10%, and quiet-host absolute time<15s. Peer jobs preclude a timing claim.

Canonical packet: `docs/research/100bit-spend-path-20261013/evidence/
prover-rw-20261023/rng-owner/summary.json`. Full source/dependency hashes and
commands are indexed there; every result retains exact raw receipts. Audit
log SHA256: `661b315ce63f9e8e5dea8b2ad707dd1a50c0cbcfc7db45c5835ab47a9c88b6e7`.
Summary SHA256: `d80161cb5833bfe0c36d29b6d70115e591baf6680d892ecfe2ffd272525ae7df`.
`artifact-hashes.json` inventories all evidence sizes/hashes. Generators were
rerun locally as normalization checks: all three checked emission/cut outputs
reproduced exact hashes, so no unchanged Lean replay followed. Derived JSON
files are each below5MB; no binaries or objects are committed.
