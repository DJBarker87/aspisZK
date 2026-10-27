# pv-runjoin15 under D277

**Target not yet established. Stage 3 remains open.**
Branch `codex/pv-runjoin-20261026`, entry `52a3712f25`.
Final source repair `b10f59dc07f0257f1cf0aecbc29aa1581462bb43`;
ELF build cohort `16ff321691d1175826b6b046679ee49b4842c46f`.
No later shipped source change. Concrete extraction now reaches a confirmed
outside-records blocker; work stops under the user's boundary, not budget
exhaustion. See BLOCKER-D277.md.

## Repairs

Twelve additional source repair stages (REPAIRS.md entries 4–15) are recorded
verbatim with their equivalence arguments in
`evidence/pv-runjoin14-20261027/REPAIRS.md`. They include branch-local stores,
split and expanded loops, combined/moved recipient matches, immutable Copy
values, inline raw projections, and fixed-array patterns. Intermediate
candidates and failures are retained, not relabelled successful.

The final body copies the immutable input/change/snapshot, destructures the
fixed sibling/direction/frontier/root arrays, constructs the same bits and
word arrays directly, and finishes with the recipient return branch. It
uses no raw helper, loop, indexed array access, heap allocation or I/O.
Signatures/types/all other functions are unchanged. Copy locations are
field.rs:22, pair_trace.rs:71, pair_forest_trace.rs:53,
payment_relation.rs:88 and pair_tree_profile.rs:403.

`source-freeze-audit.json` checks the exact signature and all bytes outside
records, and the exhaustive crates/programs/lockfile diff contains only that
file. `host-source-agreement.json` confirms all 510 tracked inputs match the
private host workspace. No shared env-J source or object was written.

## Gate (a): passed

All three ELF pins MATCH after the last source change (`gate-a.json`):

| Target | Exit | Wall s | Peak RSS KiB | Swap | Bytes |
|---|---:|---:|---:|---:|---:|
| default | 0 | 41.96 | 684392 | 0 | 1563728 |
| devnet | 0 | 39.457 | 686096 | 0 | 1563728 |
| pool | 0 | 53.474 | 677328 | 0 | 605704 |

- default: `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`
- devnet: `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`
- pool: `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`

Pinned command/environment/cache reused; separate fresh output directories.
Three artifact keys remain on the host at mode 0600 (`key-retention.json`),
with no key contents, ELF, compiled object or large LLBC copied into commits.
Gates (b)/(c) remain lead-owned under runjoin13/GATE-PLAN.md and were not run.

## Extraction receipt and stop

Unchanged tool binaries: Charon `ab6b8dca8e15969fb7caea6a8f7122a722225b58a5317639308aed57b7e8f744`,
driver `fe1da95c91cdc62d3868c00b226fa883c388dc0d6e31c1ee12b8a62722786169`,
Aeneas `562e1f51ef9bea84f62793f21b4d6b48f9ae65c61ec72588170b2c3abdc37f19`.
Command configurations changed explicitly; pinned extractor binaries were not patched.
The orchestration preflight was strengthened to require the exact named records root and LLBC
hash; cached results are accepted only on identical SHA-256.

17 Charon and 17 Aeneas scopes ran. The isolated mapper produced no accepted
Lean definition: nine Aeneas errors, six 240-second timeouts, and two recorded
manual SIGTERM stops when their replacement was identified. No memory cap
was raised and no memory-killed job was rerun. Maximum extraction peak RSS
was 6,342,434,816 bytes, with zero swap throughout.

Built-MIR shape inspection found 828,400 StorageDead nodes. Pinned Charon's
final storage pass inserts missing markers at exits; omitting explicit drop
options and the Rust RemoveStorageMarkers pass did not clear the expansion.
This is diagnostic evidence, not an impossibility theorem. Large LLBCs are
retained by hash/size/private-host path in large-llbc-artifacts.json.

The final concrete-closure Charon scope exits 0 in 25.365070801984984 s,
peak RSS 1,344,913,408 bytes, swap 0, revision d398636813. Its LLBC has
`has_errors=true` with five opaque ConstEvalVal nodes in three outside
Poseidon helpers. The local fail-closed preflight exits 1; **no Aeneas scope
30 starts**. Exact source/constant spans and minimal unapplied repair
patterns are in BLOCKER-D277.md and unsupported-constants.json. This is the
explicit outside-records stop, not a checked ROW counterexample.

## Proof, P and trust status

Transfer identification: OPEN. Withdrawal identification: OPEN. General
identification: OPEN. No R_shipped constant is accepted. Compiler-return,
transition equality at actual selected i, deployed public binding, and
P ∧ T non-vacuity are OPEN. Existing reference equations and 21 root cells
are retained; they are not relabelled as shipped mapper facts.

Constructed P before/after: {source public binding, trace} → same.
Deployed P before/after: OPEN → OPEN. Record counts: 2/8/6 → 2/8/6.
Endpoint premises removed/added/weakened: 0/0/0. Quantifiers, carriers,
failure event, observer/simulator, and conclusion are unchanged. T remains
exactly entropy_law, entropy_kernel, observation and hypothetical. No native
proof obligation is moved into T. See P-before-after.json and the focused
static trust review in trust-audit-status.md.

No new Lean theorem or kernel axioms audit is claimed; #print axioms is N/A
for all 37 host scopes (34 extraction, three SBF), not a standard-axiom
proof. receipt-index.json links every exact target, exit, wall, RSS, swap,
source revision and axioms field to full commands/logs. Every scope had an
admitted reservation, 6G/8G/swap0/TasksMax64, one scope at a time. Twelve
reservation refusals are retained, along with one seven-second early retry
correction in reservation-timing-note.md; no refused scope launched.

Budget: Lean **0/100**, Kani **0/2**; IDs 50600–50899 remain unused,
including reserved audit IDs 50897–50899. Stop is required by the confirmed
outside-records blocker. No arithmetic Kani, unrelated runtime regression,
full Lean manifest replay, merge or push was performed.

Next deliverable: an authorized outside-helper repair or a specified pinned
helper-link/extraction route that avoids these constants, plus resolution of
the isolated mapper's marker expansion. Then accepted R_shipped, fixture and
general identification, compiler return, selected-i transition, deployed
public binding, non-vacuity with hypothetical T, and focused kernel audit.
`commits-since-entry.txt` records the completed stages through the ELF gate;
the final report/stop commit follows that listing.
