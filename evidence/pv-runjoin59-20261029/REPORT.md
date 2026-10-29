# Runjoin59 — symbolic families; witness still blocked at the current skeleton

**Target not yet established. `PV_RunJoin_SkeletonWitness.model` was NOT
proved. CommonSample and BackendInput are NOT discharged. Rows removed:
NONE. The skeleton remains UNVERIFIED under ruling (v).**

Exact worktree `/Users/dominic/ZK/.worktrees/pv-runjoin`, branch
`codex/pv-runjoin-20261026`, entry
`87d831d8cf898ed771d6838922277437e017a6ae`. No merge or push.
`commits.txt` records source-stage commits; evidence-only commits follow it.

## First milestone and the owned NodeAppend obstruction

The lead's correction was followed: no concrete prover/fixture run was
kernel-evaluated. A model witness is permitted; no claim is made that a
literal deployed run must be evaluated to obtain one.

The exact current conjunction is still
`PV_RunJoin_SkeletonWitnessGate57.ContextLinks`. It includes the historical
Fields-only `PublishSkeleton54.PV_RunJoin_Link_NodeAppend`. Its quantifier
covers publications with substituted queries and commitments unrelated to
the successful source sequence. The query correction in Context57 does not
restrict this separate node link.

Read-only inspection of the node owner's branch found an existing CHECKED
obstruction and an explicit correction candidate:

- `PV_RJN_NodeObstruction.no_successful_witness`, accepted at owner attempt
  **69521**, rules out the unchanged NodeAppend for a successful,
  front-associated publication with the actual source layout and installed
  node primitives. The all-262144 query substitution preserves Fields but
  rejects before a tree walk, while the original successful append returns
  bytes. Both are forced equal to the same fixed model slots.
- `PV_RJN_NodeContext.PV_RJN_Link_NodeAppend` adds both `QueryRange` and
  `QueryContext` before the unchanged original conjunction. It reuses the
  separate named range/provenance obligations. This is a private owner
  candidate, not installed into this worktree's ContextLinks.

`owner-readonly-obstruction.json` retains the exact owner revision, source,
accepted receipt, original axioms and hashes; the accepted source hash was
checked against the current owner source. This reuses existing owner evidence;
no new node proof or discharge credit is claimed. The owner theorem's scope
is precise: successful front-associated source publications. It does not
prove that every possible failure-only abstract family is inconsistent, and
is not a privacy counterexample.

A duplicate empty-tree draft was withdrawn BEFORE compilation when the owner
result was discovered. Its drafts remain in `uncompiled-drafts/`, explicitly
unverified and excluded from the source tree/cache plan. One draft also
incorrectly treated a generic option conversion as native; this is recorded
in `duplicate-draft-withdrawal.json`. It is not evidence. No owned source or
link definition was edited, copied into this source tree, merged or rebuilt.

**Stop reason:** the existing checked node-link obstruction blocks the
intended non-degenerate successful-run witness for the unchanged local
skeleton, and the user explicitly reserves its correction to pv-rjn. This
is not budget exhaustion or a claim that the corrected owner candidate has
been refuted. A clarification about targeting that separate candidate was
left pending while independent symbolic-family preparation continued.

## Independently prepared symbolic families

The following compiled declarations now fix NativeCallback55.runOf's two
previously free parameters, without evaluating any source run:

- `PV_RunJoin_ActualRun.data`: coefficients from the stored semantic columns
  through the same raw/normalizing embedding; alpha and circle coordinates
  from stored semantics; gamma/kappa/alpha0 from the actual symbolic prepare
  call; alpha1 from the exact tag-30 scalar constructor, returned root and
  round bytes, original transcript and hash.
- `PV_RunJoin_ActualRun.plans`: the literal source header and offsets;
  compact semantic/claim constructors; inactive/root encoders; 22 symbolic
  per-query body projections partitioned at the actual 480/128/32/32/128/32
  boundaries; six source publication-index/multiproof constructions and
  native option conversion, with the six literal padding capacities.
- `PV_RunJoin_ActualRun.runs` is exactly
  `NativeCallback55.runOf data plans`.

The declarations retain source failures/divergence in the symbolic call
helpers. Total projection defaults are explicit on unsuccessful or malformed
Phase inputs; they do not assert those inputs are produced by the caller.
`ActualData59.point` uses a separately checked generic unit-circle fallback,
avoiding expensive elaboration of a concrete field proof.

The source-slice publication returns proof bytes only. The Plan's afterstate,
proofPath and statementPath are explicitly empty; statement bytes come from
`Public.public_bytes`. **These are proof-slice families, not a full native
account/observer association.** No claim is made that the empty auxiliary
fields identify actual account data. The actual caller reachability domain
and original completed common-sample/toRP record are not identified here.
The new challenge record is a projection of the stored/source-returned
values; equality with that original completed record remains required.

Checked local facts: canonicality of every normalized coefficient, exact
stored alpha/point projections, successful prepare/finish projection laws,
and the layout theorem: 22 query parts, six slots, opening offset 10055,
node offset 28359 and proof size 57607. The semantic matrix is still the
29-column/1024-row source object and the opening domain is 262144. These
facts do NOT prove a non-degenerate simultaneous-link witness, well-formed
commitment existence, query/slot success, or any complete link.

The prior `BackendHInput58.complete` C1/C2-to-hinput laws were reused read-only
and audited, not replaced with an hinput premise. Their caller extraction,
length obligations and identification with the selected `data.c` remain
open; this round did not consume them into a full BackendInput discharge.

## Links and endpoint accounting

| Obligation | Status |
| --- | --- |
| Explicit model witness for all corrected links | NOT established. |
| R24Sampler | Prior discharge retained. |
| CommonSample | Open: complete original stored-record association missing. |
| BackendInput | Open: full actual caller/C1/C2/data association missing. |
| QueryRange | Owner's result read-only; no new discharge here. |
| QueryAppend and FinishContext | Owned by pv-rjq; untouched. |
| NodeAppend | Historical link incompatible with successful associated runs; owner's correction separate and uninstalled. |
| PublishOrder | Owned by pv-rjn; untouched. |

All local link statements and Fields are byte-identical before/after;
`boundaries.json` records their hashes. Endpoint P removed/added/weakened/
changed: **0/0/0/0**. Whole rows removed: **none**, including V038, V045,
V163, V165, V167, V244, V258–V260 and V262. The eight endpoint fields,
exactly three TrustItems, simulator, observer, coupling, bad/query events,
failure independence and side-channel obligations remain. V370/D381/D386
and the extraction/native fidelity boundaries remain. Step (4) was not
started. No deployed-code, native-run or source-to-machine credit is claimed.

## Validation and resources

**12 Lean launches: 8 accepted, 4 rejected; 0 Kani. 88 attempts of budget
remain; available unallocated IDs are 69710–69796 (87 IDs).**
Used compiler IDs: 69701–69709 and audit IDs 69797–69799 only. ID 69700 was
refused by the shared quiet window before compilation and will not be reused.
The inherited local wrapper was interrupted during cooldown and changed to
return refusal to its caller; the next unused ID was launched after both
the quiet window and the 180-second cooldown. No void launch occurred.

Every launched attempt had admission exit 0 and allowed:true checked in the
launch shell. One scope at a time, MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64, Lean -M7000. No memory/time kill or cap/limit
increase occurred. Total capped host wall time **36.90 s**; peak RSS
**4,512,440,320 bytes**; swaps **0**. No own scope remains.

The four source failures were repaired with changed source: the semantic
point Fin index and a generic circle-point lemma; a checked platform-size
bound for scalar indices; and explicit monadic slice bindings/layout proof.
No failed source hash was resubmitted. Git blobs and hashes are retained in
`retained-failed-sources.json`. Failed diagnostic output containing sorryAx
is retained only as rejected evidence; every accepted printed axiom set is
a subset of propext, Classical.choice and Quot.sound.

| ID | R1Z audit target | Exit | Wall s | Peak RSS bytes | Swaps |
| --- | --- | --- | --- | --- | --- |
| 69797 | PV_RunJoin_SourceAudit59 | 0 | 1.81 | 4472991744 | 0 |
| 69798 | PV_RunJoin_FamiliesAudit59 | 0 | 1.66 | 4483846144 | 0 |
| 69799 | PV_RunJoin_BoundaryAudit59 | 0 | 2.97 | 4483006464 | 0 |

Every receipt records exact target, source revision/hash, direct import
fingerprints, exit, wall, RSS, swaps and original printed axioms. All 24
original module output/time logs were fetched and hash-verified in
`original-module-logs.json.xz`. Guard hash:
`0d17e2a5fddd81c025840be4c14ed410b81ba913f206ac4c152c8ee5f000808a`.

Initial read-only preflight verified 3,677 project pairs, 8,139 direct
fingerprints, 5,673 external objects and 5,438 IR companions. The pinned
private cache was reused; no unchanged dependency or shared/other-job object
was written. Final preflight verified **3,685** project pairs and **8,153** direct
fingerprints with every external object and IR companion matching; it is
retained in `fresh-preflight.json`.
No full frozen replay, extraction, Rust/SBF/Kani build, installation, key
operation or push occurred.

## Next concrete deliverable

Integrate/identify the node owner's corrected candidate in the exact
simultaneous-link target, retaining its separate range/provenance obligations.
Then prove `PV_RunJoin_SkeletonWitness.model` for a concrete non-degenerate
model with all layout dimensions and a well-formed commitment, using named
symbolic lemmas. Do not evaluate a complete prover fixture. Only after that
witness gate, establish the complete original common-record association and
extract the actual C1/C2 calls to consume BackendHInput58 for the full
BackendInput link. The symbolic families alone supply none of these proofs.
