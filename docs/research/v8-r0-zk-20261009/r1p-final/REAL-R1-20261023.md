# Real retry/entropy/reservation owner, 2026-10-23

Branch `codex/cx-real-r1-20261023`, base `1bffe648cad26e07572e4e2e7ac2d4b33795a7de`.
Target not yet established. Only the real selected proof-account route is in
scope: public adversary-chosen nonce, 64-byte entropy, S2, eight attempts.
The per-attempt mask/semantic/commitment/transcript/opening/publication body
is an explicit contract for R2/R3. No simulator binding is attempted.

## Stage 1: source reuse

`RealR1_source_audit.py` compares function bodies with the historical source
revisions for parts 34 and 43, including the actual real retry and reservation
callers. This is a source-identity check, not a new native proof. Its JSON
record is under `../../100bit-spend-path-20261013/evidence/real-r1-20261023/`.
The historical native gates remain P6 boundaries. Existing standard-library
and E1/E2 trust items remain explicit; no new trust item is introduced.

No file under `crates/` or `programs/` is changed. The ELF rebuild trigger
therefore does not apply; no new artifact identity is claimed.

## Stage 2: selected outer control and faithful reservation gate

`RealR1_OuterOwner.outer_owner` composes the extracted 64-byte entropy
owner through S2 admission, the serializer, a public-prefix callee, faithful
reservation and eight retries. It preserves the complete extra state and
retains every rejected update. Nonces may be selected from the retained
extra state; no nonce distribution is assumed. `entropy_failure_stops`
also stops callback `Err(Rejected)`. Reservation errors and duplicates map
to Semantic before the private body runs, for arbitrary ledgers and faults.

This is a **conditional reference control theorem**, not the native C1
instance. Its two visible contracts identify the public-prefix and
post-reservation bodies pointwise. Native public-context/hash-call binding,
the R2/R3 body instance and the conversion to the fixed experiment remain
open. The extra-state carrier permits ordered oracle/TLS/leakage state;
it does not itself produce or certify native leakage events. The reservation
reference retains operation statuses; it does not claim to model partial
`write_all` syscalls or all durable file contents. E1/E2 are retained,
not discharged or replaced by successful fixtures.

J10908 accepts all seven theorems, exit 0, 2.32 s, peak RSS 4,288,660 KiB,
zero swaps; every printed axiom list is exactly
`[propext, Classical.choice, Quot.sound]`. J10901/2/4/5/6/7 are rejected
elaboration drafts. J10900/3 did not launch Lean (dependency-comment parser
and reservation preflight respectively). Sources, dependency fingerprints,
revision, exact commands, full output and time logs are committed under
`evidence/real-r1-20261023/lean/`. No shared predecessor module was replaced.

The external native reservation harness checks the verbatim
`reserve_fallible` and `StateOnlyMaskNonceStore::reserve` bodies with the E2
atomic membership primitive and byte-blind IO faults substituted. It checks
return status, `last_error`, retained membership, call order, requested write
lengths, and exact magic/digest/nonce bytes, including duplicate and every
failure prefix. Address hashing and OS primitives remain named boundaries;
this is not filesystem verification. Final `faithful-reservation-v4`:
exit 0, 8.717 s, peak RSS 327,712 KiB, zero swaps. Caps are 6G/8G/no swap/64
tasks; Cargo dev optimization is explicitly 3 and jobs 4.

Retained diagnostics: v1 rejected incompatible Kani output/jobs options
before compilation; v2 hit struct-wide memcmp unwinding. V3 replaced that
comparison with every individual bounded field and passed. V4 additionally
uses the exact shipped 16-byte reservation magic and checks all three write
sizes; it is a stronger changed-input gate, not an unchanged replay.

## Stage 3: contract only at actual body entries

`RealR1_ReachableRetry.outer_owner_reachable` replaces the stage-2 unrestricted
body equality premise with `PreparedBodyContract`. R2/R3 need to identify the
complete body result/state only where entropy and the actual serializer
succeeded, the common public prefix returned the reservation path, and
reservation succeeded. Failed callbacks, duplicate/fault paths and unentered
attempts require no body contract. The invariant is checked only at entry
and preserved only on entered retry transitions; no iid rejection law is used.

The explicit remaining premises are: the initial invariant, its preservation
after rejection, the reachable R2/R3 body contract and a concrete native
instance of the common public prefix. An invariant may carry an except-bad
condition, but this theorem neither proves its probability nor places new
events inside the fixed `realBad`/seed/fuel exception. This is a usable
deterministic caller interface, not removal of `RustRealRefinement`.

J10912: exit 0, 3.03 s, peak RSS 4,294,644 KiB, zero swaps; all three new
theorems have standard-only axioms. J10909–11 are retained elaboration drafts.

## Stage 4: retry hazards and first unclosed native binding

`RealR1_RetryHazards.selected_trace` connects the selected reference control
to the existing ordered L1 record under an explicit reachable per-step
erasure law. `entered_abort_hazard` applies the existing conditional hazard
to the actual entered record positions, including callback faults; it does
not assert a fixed or witness-independent rejection rate.
`entropy_count_state` retains the complete entropy-prefix state under any
permutation of successful private seed pairs, on arbitrary byte-blind fault
schedules. E1 is still needed to transport this symmetry to a probability
law. Native event production and the joint mask/count/TLS/oracle coupling
are not supplied by record erasure.

J10913 accepts all three theorems, exit 0, 2.01 s, peak RSS 4,282,584 KiB,
zero swaps; every axiom list is the three standard axioms.

**Stop: selected deployed caller instance is not pinned in this tree.** The
smallest source gate, `RealR1_caller_gate.py`, fails (exit 1): the actual R1
devnet driver `tools/r1-cost-probe/src/bin/devnet_spend/plan.rs:112` calls
`prove_masked_retrying`, whose callback uses 96-byte `generate()`. It contains
neither the selected retry call nor `generate_for_mask_nonce`. The complete
12-occurrence inventory is retained in `caller-gate.json`: the profiling
fixture does use the 64-byte callback, with an OS-chosen nonce, while the
live proof-account public-nonce tools call the older V7 prover. This confirms
the still-unresolved D161/F8 source gap; it is not a new privacy attack, a
formal call-graph absence proof, or permission to analyze another route.
No keys, funds, ledger files or live accounts were accessed.

The conditional theorem for the **selected design** is now available, but
it is not a theorem about that differently wired devnet caller. Work stops
at this concrete native-instance boundary, before inventing a production
callback, event producer or experiment conversion. The next deliverable is
the actual selected client/callback source pin and nonce-policy image, then
its native public-prefix and event-producer instance. R2/R3 fill the reachable
post-reservation body contract; the initial invariant and retry preservation
also need their concrete instances.

## Endpoint and trust boundary

Conjunct 1 of `RustProverRefinement` remains open. Neither conditional outer
theorem constructs its coupling or proves exact marginals. Besides the
caller/event/source-to-experiment binding, the part-40 private raw-seed memo
and zero-exhaustion envelope is not installed in the fixed headline. Those
events cannot silently be assumed to lie in the fixed realBad/simulator-seed/
five-draw-fuel exception, nor silently charged to a ledger collision term.
Public-nonce reads and arbitrary ledger collisions continue to couple
exactly; no nonce law or ledger cap is added. P1, P7, TrustedStd, E1/E2 and
the native P6 boundaries are retained. No security target, event definition,
headline bound, source module outside this prefix, or deployed ELF is changed.

The generic `Extra` carrier is not itself a publicness proof: its public
context projection, the nonce policy's witness independence, native
`last_error`/TLS/oracle image and all observable event payloads still need
their caller image. The prefix has no argument for the newly drawn raw
seeds, but the arbitrary carrier type alone does not establish a joint
adaptive privacy law. Likewise, equal errors/no proof bytes do not erase
failure-origin, count or timing observations.

## Final focused validation and handoff

J10914 imports the completed three-module closure once, prints the full
outer/body/ready/record contracts, and audits all 13 added theorems: exit 0,
1.78 s, peak RSS 4,263,048 KiB, zero swaps, standard axioms only. Exact
source/dependency hashes and revision are in its receipt. This is the final
focused audit, not a full frozen-manifest replay or a release result.

The dependency-source audit compares 444 locally available sources with the
host cache pins. Two differ: `AspisR1ProverCommit.Types` and
`R1Z.BuilderAdmissionExtracted`. In both cases the only text changes are
the D178 `ImportUnionNamedDiscriminant` import and
`import_union_discriminant` attributes; stripping exactly that migration
gives byte identity. All other compared dependency sources are identical.
Host snapshots and the comparison are retained in `dependency-audit/`.
No shared source/object was overwritten. This limits the result to the
pinned focused cache; it is not a claim of a coherent current-tree release
rebuild. New theorem source hashes match the final committed modules.

Budget used: 13 Lean compiler invocations, two preflight refusals, four Kani
commands (one CLI rejection, one memcmp unwind failure, two successful
changed-input gates). All build work used 6G/8G/no swap/64-task scopes;
no cap was raised. No Aeneas run, heavy arithmetic gate, full regression,
new trust assumption or shipped source change was made. Historical gates
were reused only after source-identity checks. `RealR1_collect.py` validates
the retained receipts and creates `summary.json` without launching a build.
Native source snapshots reproduce all four input hashes, including rejected
versions. The final gate uses the optimized profile and four jobs.

Commits through the substantive stages:

- `99e41399e3` Pin real retry and selected entropy source reuse
- `ee6f566cb4` Compose selected entropy and reservation outer control
- `f0cbdb80ff` Restrict real body contract to reachable reserved attempts
- `27cf1ad073` Connect retry hazards and record missing deployed caller pin

Target not yet established: deliver the selected native caller pin and
source/experiment/event image, fill the R2/R3 reachable body contract and
invariant instances, and explicitly resolve the fixed-event/marginal gap.
No push or merge was performed.

## Continuation stage 5: authorized host caller and artifact gate

The lead confirmed D162 authorizes the missing client. The historical caller
stop above is superseded by the new host-only
`aspis_r1_cost_probe::RealR1_client::prove_for_proof_accounts`. It hardcodes
S2 and calls `prove_masked_retrying_with` with
`generate_for_mask_nonce(proof_account(k))`, mapping entropy errors exactly.
The caller requests a retained proof-account **public key per entered attempt**;
using one key again after rejection correctly aborts at the durable duplicate
guard. The successful key is the client's retained key at `attempts - 1`.
There is no new key generation, funding, upload or transaction submission in
this function. Key lifecycle and any effects of client-supplied key selection
remain the client's responsibility, subject to the retained-key rule. The
nonce policy is public environment input, not an asserted uniform coin or a
witness-independence theorem about arbitrary Rust closures.

Both fixtures pass with real OS entropy, real P_R1, the D148 durable ledger,
strict tx1/tx2, authenticated tx2 and dense verification. Tests check exact
reservation magic/length/nonces and fail-closed reuse, and retain all ledgers.
The first gate tested both fixtures; the changed second gate additionally
compares contemporaneous direct calls. It passes four native correctness
tests, one attempt each. No forced checker/pole verdict is used.

**D168 performance stop:** direct/client transfer 47.276/60.227 s (+27.4%);
withdrawal 52.710/54.460 s (+3.32%). These are single shared-host measurements
with independent entropy, not a causal slowdown finding. The transfer sample
exceeds the 10% gate: further implementation/adoption stops, without an
unchanged timing rerun. The original two-fixture gate measured 48.805/51.615 s;
it is retained, not substituted for the failing comparison. The historical
under-15-second candidate is not this research prover. No performance claim
or adoption is made.

All three ELFs were rebuilt, then compared byte-for-byte with the retained
pinned artifacts (`cmp` exit 0), with full SHA-256 matches:

- default `40dc75742430dd198bd51d519aa5a41bad4a45e8f173ccbd51c6d5be344ac3f0`
- devnet `12cb0bc2f8ff3993643638080a3786fdcd941910e5e4dd65ae2937a99290c28f`
- Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`

Only a feature-gated host module, its tests and module declaration changed
under `crates/`; no verifier program source changed. The caller is a library
entry point ready for the client: the old devnet driver remains a different
route. No claim is made that it has been deployed or that accounts were
created. The 544-file build-source comparison includes the new working-tree
files and matches the private host workspace exactly. The build receipts,
full pins, toolchain, performance gate and source snapshots are in
`evidence/real-r1-20261023/client/` (relative to the 100bit research directory).
Every command used 6G/8G/no-swap/64-task scopes and optimized profiles.
Native-v1/v2: exits 0, wall 142.019/222.028 s, peak RSS 567456/580624 KiB,
zero swaps. Default/devnet/Pool: exits 0, wall 31.034/3.021/31.288 s,
peak RSS 648756/203788/645024 KiB, zero swaps. Rust/SBF axioms: N/A.

The verbatim new caller and unchanged native retry function also pass the
external owned-control gate. V1 checks arbitrary statuses and one arbitrary
public key; the stronger V2 supplies eight arbitrary full 32-byte keys, eight
arbitrary entropy-failure flags and arbitrary complete body outcomes/effects.
It verifies return/error/count, every retained store effect and ordered
account/entropy/body invocation, including rejected prefixes. V2: 652 checks,
exit 0, 202.029 s, peak RSS 4227940 KiB, zero swaps; v1: exit 0, 32.200 s,
882456 KiB, zero swaps. Callees are explicit boundaries: parts 41–43's
selected entropy owner, faithful-reservation-v4/E2, and R2/R3's complete body.
This is P6 control evidence, not proof of RNG/IO/crypto or native TLS events.
Both exact harness versions and hashes are retained in `native/client-owned-*`.
Cumulative Kani commands: six of 60. No source failure was rerun unchanged.

## Continuation stage 6: compiled owned caller bridge

`RealR1_ClientBinding.native_step` identifies one bounded iteration's
extracted owned policy with the real-attempt control. `client_control`
instantiates the extracted part-34 eight-attempt retry owner with the
selected 64-byte factory and reserved continuation, then uses the existing
Lean bounded induction. The P6 boundary is the verbatim caller/native-loop
Kani evidence above, alongside unchanged parts 41–43 entropy gates.
`client_outer` composes this caller control with
`RealR1_ReachableRetry.outer_owner_reachable`. Complete returned proof/audit,
errors and retained state are preserved under its visible reachable body
contract and invariant premises. It does not prove a publicness law for
arbitrary external key-selection code.

This closes the previously missing **library caller/control instance**, not
C1. The public-prefix hash/address instance, initial/retry invariant,
reachable R2/R3 body contract, native L1/TLS/oracle event image and exact
experimental marginals remain open. The function is not yet wired into a
network client. In particular, the theorem does not upgrade an arbitrary
Prefix parameter to the concrete native SHA-256 frame implementation.
E1/E2, P1/P7 and TrustedStd are retained; no trust field is added.

J10919: exit 0, 1.94 s, peak RSS 4289824 KiB, zero swaps; all three added
axiom lists are exactly `[propext, Classical.choice, Quot.sound]`.
J10915/10918 retain the rejected ambiguity/projection elaboration drafts;
no rejected draft is accepted evidence. Exact source revisions, source and
dependency hashes, commands, full axioms and resource logs are retained in
`evidence/real-r1-20261023/lean/109{15,18,19}/`. Compilation uses the pinned
focused J cache described above; no predecessor module was overwritten.
The new client module has no downstream shared consumer replaced here.
This is not a coherent final release/manifest replay. No Rust/SBF source
changed after the artifact gate, and no additional regression was launched.

## Continuation stage 7: first event-containment obstruction and stop

The already-prepared event check and queued proof were completed for review;
no further implementation or adoption gate was started after the D168 stop.
`RealR1_event_gate.py` checks the actual shipped source-seed domain against
`LayoutR1PBin.dSourceSeed`, then tests the proposed implication
`privateMemo -> simulatorSeedGuess or fiveDrawFuelExhaustion`. Expected and
actual exit are 1: a fixed byte-blind prior query can match a nonzero raw seed
while both added fixed events are false. The complete query and resource
receipt are in `event-gate.json`. This is a small byte-frame check, not a
native source execution or cryptographic attack.

`RealR1_EventBoundary.raw_query_hit` proves the private suffix event for
**every** public frame. `not_simulator_query` rules out the old simulator
seed event for every independent simulator seed: the actual source-seed
frame begins with ASCII `a`, the simulator coin prefix with `U`.
`fixed_extension_misses` supplies an explicit nonexhausted five-draw tape
and proves the same missed event under any old-event-safe model sample.
The old-event-safe sample is an explicit hypothesis, not a constructed
native execution outside actual `realBad`. This refutes silently folding
the memo exception into the seed/fuel extension. It does **not** refute
`RunJoin`, prove absence of native/model agreement on such samples, or rule
out a different valid coupling with exact marginals.

J10917: exit 0, 1.95 s, peak RSS 4178744 KiB, zero swaps. All three added
axiom lists are exactly `[propext, Classical.choice, Quot.sound]`.
J10916 is the retained rejected draft (Fin index elaboration); its diagnostic
`sorryAx` is not accepted evidence. Source/dependency/revision pins, exact
commands and full logs are in `lean/10916` and `lean/10917`.
The generic private-memo bounds from part 40 remain conditional; no new
term is installed in the frozen headline. No old event, statement domain,
nonce law, ledger cap, cryptographic assumption or security target changed.

**Target not yet established.** Conjunct 1 still needs the concrete public
prefix/hash-address binding, the R2/R3 reachable body and invariant instances,
complete native L1/L2/TLS/oracle event production and experimental conversion,
and exact E1/adaptive marginals. Private raw-seed memo and zero-exhaustion
paths must be proved to agree within the existing event carrier, or a changed
visible envelope must be explicitly composed. Equal errors and successful
fixture verification do not supply this. Public nonce inputs and arbitrary
ledger collisions continue to couple exactly with no collision charge.

Final cumulative counts: **18/100 Lean compiler invocations**, two earlier
preflight refusals, **6/60 Kani commands**. Latest accepted checks cover 19
added theorem axiom reports including the prior 13; every accepted theorem
has only the standard three axioms. The resumed work used five Lean attempts
(two accepted, three rejected elaboration drafts) and two successful changed
Kani gates. All retained receipt/source hashes validate with
`RealR1_collect.py`; it updates `summary.json` without running a build.
No full frozen-manifest replay, Aeneas extraction, cap increase, new trusted
item, key cleanup, push, merge or deployment was performed. No local target
or large generated artifact was created. Source diffs pass whitespace checks;
raw rejected compiler logs retain two compiler-emitted whitespace lines.

Continuation commits before this final event/report commit:

- `84b753b502` Add proof-account host caller and verify pinned verifier artifacts
- `cdd0da0d16` Bind proof-account caller control to the real outer owner

The immediate operational stop is the transfer's failed 10% timing gate;
its cause needs controlled diagnosis before adoption. The next proof work,
after that stop is resolved, is the concrete prefix/event image and fixed-event
transport above. Native simulator binding remains out of scope (D184).
