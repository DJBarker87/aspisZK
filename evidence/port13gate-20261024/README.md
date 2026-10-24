Port13GATE handoff

Concrete claim: `AspisR1.Port13GATE_Authenticated.accepted` retains the complete
indexed source acceptance-to-recovery conclusion of Port11PROV_Authenticated.
The full `sourceAccepted` premise and every subsequent witness/conclusion byte
are identical. The only assumption change is removal of native-D full P6Boundary
and the separate binary callback, retaining its occupied/sibling ParentGates at
rawOracle H and its LeafGate H directly. No replacement structure hides a batch
or recovery conclusion.

Before: `Port11PROV_accepted-statement.lean.txt`.
After: `Port13GATE_accepted-statement.lean.txt`.
Kernel full before/after, expanded hidden gates/dictionaries, seven full axioms
reports: `lean-005/stdout.log` (no printer ellipses).

Why sound: `Port13GATE_Canonical.dictionary H` is a total Unit dictionary with
answer `ok (rawOracle H input)`. Its `boundary` theorem constructs the old P6
boundary, with occupied also serving as the unused binary parent. Both actual
callback sourceBatch and frozen batch Programs are D/hash-independent. Thus
both_batches can use that proof-only witness to compare those same Programs.
The concrete consumer continues to use Port10AUTH_Installed.accepted with the
original D/hash/H, actual native successes, original logs and source witnesses.
The dictionary is never installed or sampled in the fixed source experiment.
Port9OR_Code.program still branches on D's existing success/fail/div policy;
its per-success Oracle fact is proved by Port9OR_Code.oracle. No unexecuted-read
success, native totality, conditioning, extra collision loss, or modified
oracle law is assumed.

Retained: decoder/adapter/ops/rest and unrestricted byte prover; TrustedStd's two
pure std semantics; unwrap success; occupied/sibling single-read ordered parent
contracts; leaf hash/dedup/write contract; source acceptance; strict parse;
query binding; committed-root association; first-read Q cap; no-hit; actual frame
read and selected root association. Parent/leaf lowering/adoption, parser/op7
sampled-query linkage, complete canonical checks/no-hit/failure domination,
StoredCarrierBinding and release identities remain separate obligations.

New validation: helper lean-001 exit 0, concrete consumer lean-002 exit 0,
expanded full audit lean-005 exit 0. Audit lean-003 failed solely on unsupported
pp.width; changed lean-004 passed but printed depth ellipses, prompting the
printer-only lean-005 change. All attempt sources/logs are retained. No resource
failure or unchanged Lean retry occurred. Standard axioms only. Commands,
revision, source/dependency hashes, exit/time/RSS/swap and full axioms are in
individual receipts and manifest.json. Peak successful RSS 4,498,392 KiB;
all swaps zero. No full frozen replay, runtime suite, Rust gate or ELF build.

Reused: exact unchanged Port10/11 source producer evidence and pinned imports.
`reuse-assessment.json` and `cache-source-assessment.json` record the assessment.
Six selected objects have matching adjacent host sources; P6Frozen2Stage has
exact source+object match to the historical successful receipt. This is cached
focused validation, not a new release identity gate or coherent closure replay.
Old resource admission claims are not repaired by today's corrected snapshots.

Resource correction: full /sys/fs/cgroup traversal, cgroup.events population,
system/Docker scopes, nested cap deduplication, uncapped background inventory,
required-data fail-closed handling; fixture evidence and five per-attempt fresh
admissions under the shared global lock. Each admission reports 24.375 GiB plus
8 GiB < 55 GiB; each scope verifies 6G/8G/noSwap/Tasks64. No services changed.

Ledger: inherited 213 actual + 1 pre-Lean charge; 5 new actual attempts =
218 actual + 1 pre-Lean charge = 219 charged / 220. One conservative slot
remains, no allocation reclaimed. Kani remains 0/20.

Next concrete producer: source-backed occupied/sibling parent and leaf lowering
and adoption at these retained exact local contracts. Full source 1161 and
actual remainder <=115/control flow remain open. Port12's 477+563+6=1046 remains
only the owned projection. The exact bound remains
(Q+34)*B+kappa(Q+1161)+2^-126+2^-454. Both deployed targets not yet established.
No crates/programs/protocol/target/security contract changes; current default,
devnet and Pool ELF pins remain those supplied by the lead. No keys touched.
