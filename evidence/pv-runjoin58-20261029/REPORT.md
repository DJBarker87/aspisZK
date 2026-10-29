# Runjoin58 — transfer-13 prerequisites and backend producer laws

**Target not yet established. The required actual-fixture simultaneous-link
witness was NOT proved. CommonSample and BackendInput remain open. Rows removed:
NONE. The provenance-corrected skeleton remains UNVERIFIED under ruling (v).**

Worktree `/Users/dominic/ZK/.worktrees/pv-runjoin`, branch
`codex/pv-runjoin-20261026`, entry
`c8fb38ee734a84e8cdb4a3f8b8de697fd66195e7`. No merge or push. The round exhausted
100 Lean attempts, IDs 68800–68899, including audit IDs 68897–68899; zero Kani.
Source-stage commit list through the collection revision in `boundaries.json`: `commits.txt`; final evidence-only commits follow it.

## Requested witness: not delivered

The candidate's `PV_2TNV_PublicEncoding` and `PV_2TNV_CanonicalWitness` were read
and byte-compared with this worktree, read-only, at candidate
`a8ecbe80fd8057a68519b93dae232cf950dc222a`; both match. See
`fixture-candidate-identity.json`.

Their required closure was compiled privately against the pinned runjoin cache:
the byte-derived transfer-13 public, strengthened canonical witness, append
certificates, native byte aliases, headline fibre, and account-data associations.
The public index is 13; the original index-zero transfer was not substituted.
The existing honest-family results were read and the transfer theorem audited.

**These facts do not construct an actual successful prover run.** In particular,
this round did not obtain the fixture's successful `build_with_material`,
`prepare_opening`, `finish_opening`, or publication Result; did not produce its
actual `Fields` and completed common-sample record; and did not prove the
conjunction `ContextLinks` on its singleton run. No declaration
`PV_RunJoin_SkeletonWitness.fixture` is claimed or supplied with hidden success
or link premises. There was no fresh native fixture execution or complete
fixture-model replay. Compiling literal proof bytes is not such a replay.

No link was tested false on an actual fixture run, and no new contradiction or
ruling-(v) correction is claimed. This round supplies producer prerequisites,
not the requested witness-first milestone or decomposition credit.

## Checked producer work

New modules are under `docs/research/v8-r0-zk-20261009/lean/R1Z/`.

`PV_RunJoin_BackendHInput58.complete` derives the exact **hinput equation** from
successful Results of the original C1 and C2 source-model producers. Its
preconditions are explicit:

- the initial backend has 29 message columns;
- each of the 26 C1 input vectors has length 1024;
- the H1 slice has length 1024;
- the actual C1 call returns `(Ok root1, first)`;
- the actual C2 call on `first` returns `(Ok root2, last)`.

Its conclusion constructs `c` from those actual input arrays/slice and proves
canonicality of every cell, then:

```lean
alloc.vec.Vec.deref last.messages =
  PV_RunJoin_CoefficientsWeight46.messages
    (fun l j => ProverRwDictionaryTower.fromW
      (ProverCommitNativeOps47.embedded (c l j)))
last.messages.length = 29
```

The desired hinput equation is **not a premise**. This uses exact cell stores,
borrow restorations, symbolic row and lane induction, and all commitment-return
branches. C1 writes lanes 0–25 and 28; C2 writes 26 and 27. Consequently the
final matrix does not rely on the initial cell contents. Constructors normalize
raw representatives; no input-canonicality premise was added.

**Retained caller gap:** the actual fixture's semantic build has not been
connected to those two successful source calls, their row-length preconditions,
and the skeleton's chosen `data.c`. Thus this producer theorem does not discharge
`PV_RunJoin_Link_BackendInput` for an actual run family.

`PV_RunJoin_BackendInitialLength58.complete` proves the returned length of the
actual `alloc.vec.from_elem` model without assuming clone identity or allocation
success. `BuildBackendLength58` and `BuildMaterialBackendLength58` carry the
29-column invariant through the actual semantic-builder control flow, splitting
at the two commitment returns instead of expanding the entire computation.

`PV_RunJoin_BuildMaterialStored58.complete` consumes one successful actual
`build_with_material` Result and proves, for that same returned record:
canonical alpha prefix of length 10, provenance of both returned circle calls,
and returned backend length 29. It supplies neither execution success nor the
association with the original completed oracle-table record. It therefore does
not discharge CommonSample. The coefficient-caller continuation is an explicitly
uncompiled draft in `uncompiled-drafts/`, not an accepted result.

`producer-source-inspection.json` records the four emitted row bodies and their
used restoration continuations. The new credit is **inside the pinned extraction
model**. No new native differential or source-to-machine fidelity credit is
claimed; V370 and D381/D386 remain. No crate, program, client, extraction or ELF
was changed or rebuilt.

## Links and endpoint accounting

| Obligation | Status |
| --- | --- |
| Actual transfer-13 conjunction witness | NOT established; skeleton unverified. |
| R24Sampler | Prior discharge reused; no new discharge. |
| CommonSample | Open; complete stored-record association missing. |
| BackendInput | Open; C1/C2-to-hinput producer checked, actual caller/Data association missing. |
| FinishContext, QueryRange, QueryAppend | Owned by pv-rjq; definitions untouched. |
| QueryContext | Unchanged; no new discharge claimed. |
| NodeAppend, PublishOrder | Unchanged and open. |

Before/after link statements are identical: `boundaries.json` records byte-equal
hashes for Skeleton54, Skeleton57 and PublishContext57. Fields was not changed.
No requirement was silently removed or added. Native55's historical conditional
consumers were not reinstalled or promoted. Step (4) was not started.

Rows removed: **none**, including V038, V045, V163, V165, V167, V244,
V258–V260 and V262. Endpoint P removed/added/weakened/changed: **0/0/0/0**.
The eight endpoint fields, exactly three TrustItems, simulator, observer,
common coupling, bad/query events, failure-independence and side-channel
obligations remain. Protected `PV_RJDec_`, `PV_OWN*`, `PV_RJQ_` sources and
soundness files were not edited.

## Validation, budget and resources

**100/100 Lean launches: 82 accepted, 18 rejected; 0 Kani; 0 compiles remain.**
All IDs are 68800–68899. Every launch records atomic admission exit 0 plus
`allowed:true`, same-shell admission/launch, source revision/SHA, complete direct
object fingerprints, exit, wall time, peak RSS, swap and original printed axioms.
No refusal, void launch, overlapping capped scope, memory kill, timeout or cap
increase occurred. No unchanged failed source was resubmitted. Failed sources
are hash-verified and retained by Git blob in `retained-failed-sources.json`.

The rejected sources were repaired by explicit constructor/carrier arguments,
borrow-pair elimination, fixed scalar-length rewrites, correct induction argument
order and continuation normalization. The matrix recursion failures were replaced
by named empty-prefix transport, avoiding reduction under the 29×1024 matrix.
The line-wide failed-SHA guard hash is
`327348928cf71f1eb53cca1e619969bfe12439a7ef164dd3e7b4256948a32084`.

Caps: MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, Lean -M7000.
Total capped host wall time: **564.22 s**; maximum RSS **5,273,149,440 bytes**;
swaps **0**. The 200 original per-module output/time logs were fetched and
hash-verified in `original-module-logs.json.xz` and its manifest.

Audit source revision: `25dd88c682fde657fba2de18b06439a769707e3d`.

| ID | R1Z target | Exit | Wall s | Peak RSS bytes | Swaps |
| --- | --- | --- | --- | --- | --- |
| 68897 | PV_RunJoin_FixtureAudit58 | 0 | 2.11 | 5101780992 | 0 |
| 68898 | PV_RunJoin_BackendAudit58 | 0 | 1.88 | 4460818432 | 0 |
| 68899 | PV_RunJoin_BoundaryAudit58 | 0 | 2.27 | 5273149440 | 0 |

Every accepted printed axiom set is a subset of propext, Classical.choice and
Quot.sound; `accepted-axioms.json`, `final-audits.json` and `audit-coverage.json`
retain the evidence. These audits do not establish missing hypotheses.

Initial read-only cache preflight: 3,595 project source/object pairs and 7,954
direct fingerprints matched. Final: **3,677** pairs and **8,139** fingerprints,
with all **5,673** external objects and **5,438** IR companions matching.
The pinned private workspace was reused; no shared/other-job object was written.
Ten historical uncompiled exclusions remain unchanged. No own scope remains.
Source/tools/report whitespace checks passed. The full diff reports only EOF
blank lines in the 18 original rejected-launch logs, retained byte-for-byte.
There was no package-wide/frozen-release replay, Rust/Kani/SBF build, native
fixture replay, installation, key operation or push.

## Stop and next concrete deliverable

Stop reason: **100-attempt budget exhausted**, not completion or a checked
actual-fixture counterexample. The requested first milestone remains first:
construct the transfer-13 Run from its actual canonical input, fixed hash/entropy
and installed callbacks; prove its successful semantic/prepare/finish/publication
Results and actual record association; then prove every ContextLinks member
simultaneously as `PV_RunJoin_SkeletonWitness.fixture` with no success/link
premises. Use the new hinput theorem only after extracting its C1/C2 calls and
length preconditions from that actual caller. Complete CommonSample and
BackendInput only after this gate. Consume pv-rjq's owned results read-only;
do not edit those three definitions.
