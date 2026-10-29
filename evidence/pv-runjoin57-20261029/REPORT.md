# Runjoin57 — range repair and a second checked non-vacuity obstruction

**Target not yet established. No simultaneous-link witness was proved. No
link was discharged this round; rows removed: none. Both new conditional
skeletons remain UNVERIFIED as decompositions under ruling (v).**

Worktree `/Users/dominic/ZK/.worktrees/pv-runjoin`, branch
`codex/pv-runjoin-20261026`, entry
`9a2672562d21267aede920173d5849ba4ad2ed78`. No push. Historical skeleton54,
Fields, protected `PV_RJDec_`/`PV_OWN*`, frozen Rust/client, endpoint statements
and all three TrustItems are unchanged. Corrections are explicit versioned
successors, not silent changes to previously checked statements. Native55's
historical conditional consumers have not been reinstalled or promoted.
Step (4) has not started.

## Authorized first correction

The strict opening-domain bound is **262144**, from
`crates/aspis-core/src/r0/mod.rs`: `FIBRE_COUNT = 1 << 18`; the FibreIndex
macro accepts only `index < FIBRE_COUNT`.

`PV_RunJoin_PublishSkeleton57.QueryRange queries` states exactly:

```lean
∀ q ∈ queries.val, q.val < 262144
```

Before, skeleton54's QueryAppend began:

```lean
∀ i (p : prover.Publication), Fields (runs i) p →
  (runs i).plan.queries.length=22 ∧ ∀ out cc1 cc2,
    p.backend.c1=some cc1 → p.backend.c2=some cc2 →
    out.length=(runs i).plan.offOpenings →
    ∃ next, prover.append_query_openings out cc1 cc2 p.queries
      (alloc.vec.Vec.deref p.folded_word) p.folded_salts=ok next ∧
      bytes next.val=ProverCommitPublish43.queries (runs i).plan.queries (bytes out.val)
```

The range-only successor inserts `QueryRange p.queries →` immediately after
Fields, preserving every remaining quantifier and conjunct.
`PV_RunJoin_Link_QueryRange` separately requires that the publication
returned by the actual prepare/private-salt/finish chain has this range.
It refers to the actual returned query array, not the plan's model queries.
Its actual transcript-derivation proof remains **open**.

PublishOrder now takes that range explicitly, and
`PV_RunJoin_PublishSkeleton57.complete` (68500) again has EXACTLY the typed
`PV_RJ4IDB.OpenInputs.RUNJOIN_PUBLISH_COMPACT actual published` conclusion.
The proof obtains the actual publication using PublishReach54, obtains the
range from its separate named link, and passes it through ordering.
This conditional implication earns **no decomposition credit** without a
simultaneous-link witness. Exact complete before/after link definitions are
retained in `link-statements-before-after.json` and the versioned Lean sources.

## FIRST: simultaneous-link witness check

Before any discharge, the witness check found a second defect in QueryAppend.
`Fields` does not associate the publication's commitments with the actual
backend. Even with all **22 query indices equal to zero**, it admits a
commitment with `time=C1`, `lanes=[0]`, `words=[]`, arbitrary tree and no salts.
The source accepts FibreIndex(0), reads lane[0], then indexes words[0]. That
read fails before opening-lane values or any mutable-borrow update is reached.

Checked proofs:

- `PV_RunJoin_QueryEmptyWords57.fill` (68502): the first fill returns
  `Result.fail Error.arrayOutOfBounds`, for arbitrary opening matrix and index.
- `PV_RunJoin_QueryInRangeFailure57.range` and `.source` (68504): the concrete
  all-zero array satisfies QueryRange, yet the actual append emission fails
  on its first iteration with that commitment.
- `PV_RunJoin_QueryRangeObstruction57.complete` (68507): under the actual
  selected dictionary, **any** Fields instance and representable opening
  offset refute the range-only QueryAppend link. The theorem constructs the
  commitments and output buffer itself; no rejection or fill-failure premise
  is assumed.
- `PV_RunJoin_QuerySuccessfulObstruction57.complete` (68508): CommonSample,
  BackendInput, FinishContext, range-only QueryAppend, a successful actual
  source Result and representable opening offset imply **False**.
- `PV_RunJoin_SkeletonWitnessGate57.range_no_successful_witness` (68510): the
  conjunction of **all eight range-only links**, explicitly named RangeLinks,
  cannot hold for such a successful run. QueryRange, NodeAppend and PublishOrder
  are included in the conjunction, although the contradictory subset already
  suffices.

This is a source-model counterexample plus mechanically checked, read-only
Rust failure-prefix inspection (`source-finding.json`). It is not a native
fixture replay, a complete new Rust refinement, or a privacy counterexample.
The malformed commitment is admitted by the link, not asserted produced by
an honest backend. No discarded mutable restoration is crossed by this
failure prefix. No deployed-code/ledger credit is claimed.

## Explicit second correction candidate

`PV_RunJoin_PublishContext57.QueryContext r p` is the missing publication
provenance precondition:

```lean
∃ prepared salts,
  prover.prepare_opening .S2 r.hash r.backend r.sem=ok (.Ok prepared) ∧
  prover.derive_private_salts r.salts.1 r.salts.2 r.hash 114#u8=ok (.Ok salts) ∧
  prover.finish_opening .S2 r.hash prepared salts=ok (.Ok p)
```

The second QueryAppend successor begins
`Fields r p → QueryRange p.queries → QueryContext r p → ...`, with the append
success and byte-equality requirements retained exactly. The separate named
`PV_RunJoin_Link_QueryContext` carries the obligation that the actual returned
publication satisfies this provenance condition. No append, serializer,
assembly or desired publication equation occurs inside QueryContext.
PublishOrder takes the same explicit context. This avoids asserting the
serializer law for unrelated commitments substituted into a front-fields
record; it does not prove the serializer law.

`PV_RunJoin_PublishContext57.complete` (68509) compiles with the exact original
RUNJOIN_PUBLISH_COMPACT conclusion, now from nine explicit links.
`ContextLinks` in SkeletonWitnessGate57 names their complete conjunction.
**No concrete ContextLinks witness has been constructed.** The second
candidate is UNVERIFIED, and no sufficiency, satisfiability or link-discharge
claim is made for it. No other individual link was proved contradictory in
this round. The remaining NodeAppend universal publication quantifier still
needs scrutiny during the next witness attempt.

## Status and endpoint accounting

| Link | Status |
| --- | --- |
| R24Sampler | Previously discharged by runjoin54; reused, no new discharge. |
| CommonSample | Open; previous circle-record partial results retained. |
| BackendInput | Open; full hinput producer and message association remain. |
| FinishContext | Open; full actual field association remains. |
| QueryRange | Added explicitly; actual transcript-derived proof open. The all-zero counterexample array alone is checked in range. |
| QueryContext | Added explicitly in the second candidate; no discharge credit claimed. |
| QueryAppend | Range-only version refuted; provenance successor is an unverified candidate. |
| NodeAppend | Open and unchanged. |
| PublishOrder | Versioned to consume range/context explicitly; open. |

No link-discharge stage followed the failed witness gate. Rows removed: **none**,
including V038, V045, V163, V165, V167, V244, V258–V260 and V262.
Endpoint P removed/added/weakened/changed: **0/0/0/0**. The eight endpoint
fields, three TrustItems, V370/D381/D386 boundary, observer/simulator/coupling,
bad/query events, failure-independence and side-channel obligations remain.
The new skeleton preconditions are separately visible proof obligations,
not new trust items or endpoint discharges.

This round stops on the checked in-range missing-word source/link
counterexample, with budget unspent, rather than claiming the required
witness exists. This does **not** prove that ContextLinks is contradictory or
that its witness cannot be constructed. The next deliverable remains a
successful concrete fixture/model instance satisfying every ContextLinks
member simultaneously, correcting any further contradictory link with an
explicit actual-run obligation. Only then resume cheapest-first substantive
link discharge, including transcript-derived QueryRange.

## Validation and resources

**14 Lean compiler launches**, 68500–68510 and audit IDs 68597–68599:
**10 accepted, 4 rejected; 0 Kani**. IDs **68511–68596** remain unused (86).
The four rejected sources are retained and hash-verified by Git blob in
`retained-failed-sources.json`. Their replacements fixed the exact error
constructor/scalar length, scalar cast, record/dictionary elaboration and
record-projection rewrite. No unchanged failed source was resubmitted.
No memory/time kill or cap increase occurred.

Every launch used atomic successful admission plus allowed:true checking in
the launch shell. No admission refusal, void launch or scope overlap occurred.
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, Lean -M7000;
maximum RSS **4,504,358,912 bytes**, swaps **0**. See per-attempt receipt JSONs
for target, exit, wall time, RSS, swap, exact source revision/hash, import-object
fingerprints and original axiom output. All 28 original per-module output/time
logs were hash-verified and retained in `original-module-logs.json.xz`.

An inherited wrapper's prelaunch scope-inventory pattern matched another
job's scope at 68510. It was corrected to this round's own `pv57-lean-*`
pattern before admission; no compiler had started and that ID was not consumed.
The other job was untouched (`own-input-prelaunch-fix.json`). The current
line-wide failed-SHA guard hash is recorded in `boundaries.json` and SUMMARY.

Audit source revision: `989f5634cc3c65f796ed2eb7da4434bb57871d75`.

| ID | Exact audit target (R1Z namespace) | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | --- | --- | --- | --- | --- |
| 68597 | PV_RunJoin_RepairAudit57 | 0 | 1.87 | 4469723136 | 0 |
| 68598 | PV_RunJoin_FailureAudit57 | 0 | 1.73 | 4470484992 | 0 |
| 68599 | PV_RunJoin_WitnessAudit57 | 0 | 1.66 | 4477927424 | 0 |

All accepted printed axioms are subsets of propext, Classical.choice and
Quot.sound. Every new theorem is covered by the three audits. Accepted
compilation counts certify the stated conditional implications and
obstructions; they do not confer decomposition or release credit.

Initial read-only reuse preflight: 3,585 project source/object pairs and 7,935
direct fingerprints matched. Final: **3,595** pairs and **7,954** fingerprints,
with all 5,673 external objects and 5,438 IR companions matched. The pinned
private host workspace/cache was reused; no shared or other-job object was
written. Ten historical uncompiled staged modules remain the same exclusions
as runjoin56; none is a new credited dependency. No own scope remains running.

No complete frozen release replay, Rust build, ELF operation, extraction,
native fixture replay, installation or key operation ran. Branch changes
since entry are listed in `commits.txt`.
