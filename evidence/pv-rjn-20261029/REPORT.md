# RJN — publication ordering and NodeAppend quantifier audit

Target not yet established. No complete ledger row or endpoint premise is removed. No
simultaneous-link satisfiability witness or decomposition credit is claimed.

## Boundary

Worktree `/Users/dominic/ZK/.worktrees/pv-rjn`, branch
`codex/pv-rjn-20261029`, base
`c8fb38ee734a84e8cdb4a3f8b8de697fd66195e7`.
Only new `PV_RJN_` Lean modules, own tools and own evidence are written.
`PV_RunJoin_` sources, all historical Link definitions, the live runjoin
branch/worktree, frozen Rust/client and the held RJQ branch/worktree are
unchanged. Other-branch reads use `git show`. No push or key operation.

## PublishOrder

`R1Z.PV_RJN_PublishOrder.actual` is checked with the **exact** unchanged
`PublishContext57.PV_RunJoin_Link_PublishOrder runs` conclusion.
`PV_RJN_NativePublishOrder.actual` specializes it directly to
`NativeCallback55.runOf data plans`, quantified over the still-independent
Data and Plan families. No particular actual-run family is invented.

`PV_RJN_InstalledPublishOrder.actual` is checked against the selected
native dictionary. Its two remaining standalone Props are pure Plan facts:

- `PV_RJN_Producer_PlanLayout`: `proofBytes=57607`, `offOpenings=10055`,
  `offNodes=28359`, and the literal 16-byte MAGIC/S2 header.
- `PV_RJN_Producer_FrontLengths`: header, compact semantics and compact
  claim lengths are respectively 16, 7015 and 464.

`PV_RJN_LayoutInstalled.actual` and `.front_room` prove that these suffice
for the source layout and encoder-room facts below. No dictionary constant
law is left to the actual-family producer. The matching `.contextual`
ordering theorem is checked for the private corrected node contract too.

The lower-level standalone producer Props state:

- `PV_RJN_Producer_Layout`: the Plan header is the actual MAGIC plus the S2
  tag and seven zeros, and its opening offset, node offset and total proof
  size equal the constants read by the source serializer.
- `PV_RJN_Producer_FrontRoom`: header length plus compact semantic length
  plus compact claim length fits `Usize.max`.

Neither producer contains an append law, model assembly, complete proof-byte
equality or the target link. They are source input/layout facts. They remain
obligations of the actual-family producer.

The proof obtains the source's successful codec calls, all ordered front
appends, the two commitment extractions, query append, node append and all
three length guards through `PV_RJN_PublishTrace.source`. It does not assume
an external `map_err` implementation: raw codec Results are retained in the
trace and their success comes from Fields under the producer size bounds.
`PV_RJN_Bytes.append_success` identifies each successful native byte append.
The existing query/node links then supply their local model transport, and
the proof establishes both model assembly guards and all final bytes.

`PV_RJN_ContextPublishOrder.actual` and `.native` are also checked for the
private corrected node contract. They establish the same ordered-byte law
without using the refuted unqualified NodeAppend premise. The corrected node
link itself is still open. `PV_RJN_NodeRangeWitness.excluded` checks that the
new range precondition excludes the concrete substituted array.

The exact original PublishOrder link itself takes QueryAppend and the
**unchanged** NodeAppend as premises. It is a checked local conditional
serializer theorem, not a successful-run decomposition or endpoint discharge.

## NodeAppend obstruction and explicit correction

The checked rejection cells are `PV_RJN_NodeReject.body`, `.check`, `.count`,
`.tree`, `.first_slot` and `.source`. The sorted/deduplicated first batch of
an all-262144 array is the singleton `[262144]`. The proof uses a named
sorted-replicate lemma, a tiny ten-element dedup cell and isolated failure
cells; it never reduces the full multiproof or a concrete tree.

The conjunction under audit is problematic because `Fields r p` constrains
only the front fields. Substituting the 22 queries preserves Fields and all
commitments/tree. The actual tree check rejects 262144 because the strict
bound is 262144. Rejection occurs before the index-copy or tree-walk mutation
cone. `source-finding.json` records the frozen Rust hashes and the matching
failure-prefix inspection; this is not a new native association proof.

The selected-dictionary helper laws and `PV_RJN_NodeObstruction.no_successful_witness`
are checked. The native-family corollary `PV_RJN_NativeNodeObstruction.actual` is also checked.
Their precise claim is that a successful,
front-associated publication plus the actual node offset is incompatible
with the **unchanged** NodeAppend link: that link equates both the successful
node result and the substituted rejection with the SAME model slot list.
The contradiction uses the link's own publication_indices law; it assumes
neither the substituted source rejection nor a desired serializer equality.

The explicit private correction candidate is `PV_RJN_NodeContext`:

Before:

```lean
∀ i p, Fields (runs i) p →
  slots.length=6 ∧ publication_indices_law ∧ node_append_law
```

After:

```lean
∀ i p, Fields (runs i) p → QueryRange p.queries → QueryContext (runs i) p →
  slots.length=6 ∧ publication_indices_law ∧ node_append_law
```

Every original conjunct and byte/error requirement is retained verbatim.
`PublishSkeleton57.PV_RunJoin_Link_QueryRange` and
`PublishContext57.PV_RunJoin_Link_QueryContext` already carry the separate
actual-run obligations. Range excludes this counterexample. Provenance
restricts the unrelated-publication quantifier just as for QueryAppend.
No sufficiency or satisfiability claim is made for this candidate. Existing
`PV_RunJoin_` definitions are read-only; the correction is not installed into
the live skeleton. This is a malformed-publication link counterexample, not a privacy
counterexample or a failure attributed to an honest native producer.
The six actual multiproofs and generic publication-index
source proof remain work for the corrected link, rather than a hidden new
producer hypothesis.

## Endpoint accounting

Whole rows removed: none. Endpoint P removed/added/weakened/changed:
**0/0/0/0**. No TrustItems field is added. The eight endpoint fields,
V370/D381/D386 compiler boundary, observer/simulator, coupling, failure
independence and side-channel obligations remain. QueryRange remains available from
the held RJQ result; no new QueryRange discharge is claimed. The actual-family and
simultaneous-link fixture witness remain runjoin58's work.

## Final status and next deliverable

| Assigned link | Status |
| --- | --- |
| PublishOrder | Proved parametrically for `runOf data plans`, with explicit literal Plan-layout and front-length producer Props. Exact original conclusion; a checked contextual successor uses the corrected node contract. |
| NodeAppend | Original link refuted under a successful, front-associated producer and actual layout, for arbitrary well-formed families. The malformed substitution is internal to its universal publication quantifier. Private range/provenance correction is explicit; its six multiproofs and publication-index source law remain open. |

No concrete successful fixture is claimed by this work. The obstruction is
universally quantified over every successful associated instance, not a
claim that the all-links conjunction has a concrete witness. The corrected
whole skeleton remains UNVERIFIED under (v). Stop reason: the original
NodeAppend link has a checked source-model counterexample; its proof cannot
be completed unchanged. The independent ordering work is complete within
the assigned parametric scope. The unused Lean budget is not a resource stop.

Next: the owner can adopt the private NodeAppend precondition correction,
then prove its actual six multiproof/slot associations and generic insertion
index law, and combine those with runjoin58's actual-family and joint-link
fixture witness. No existing link was edited or silently weakened here.

## Validation and resources

**32 Lean launches: 17 accepted, 15 rejected; 0 Kani.**
IDs 69500–69528 and 69597–69599 were used; 69529–69596 remain unused (68).
All 38 new theorems are covered by the three reserved final audits
(`axioms-coverage.json`); their printed axioms are subsets of propext,
Classical.choice and Quot.sound. No sorry, axiom, admit, native_decide or
raised heartbeat/recursion limit was added.

The audit source revision is `5da99d27955728649cfcc169e946048cd179ed59`.

| ID | Exact audit target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | --- | --- | --- | --- | --- |
| 69597 | R1Z.PV_RJN_OrderAudit | 0 | 1.68 | 4476334080 | 0 |
| 69598 | R1Z.PV_RJN_NodeAudit | 0 | 1.87 | 4469252096 | 0 |
| 69599 | R1Z.PV_RJN_NativeAudit | 0 | 1.96 | 4473270272 | 0 |

Every attempt's source revision/hash, full import fingerprint, target, exit,
wall time, peak RSS, swap and original axiom output is retained in the
module/receipt JSONs. All 64 original output/time logs were hash-verified in
`original-module-logs.json`. All 15 rejected sources are retained by
hash-verified Git blob (`retained-failed-sources.json`). Failures were proof,
elaboration or syntax failures. One default-heartbeat failure was replaced
by a named dictionary projection. No memory or wall-time kill occurred.
Every resubmitted failed module had changed proof source; (u') was not needed.

Five quiet-window refusals occurred before attempt 69519. They launched no
compiler and consumed no ID. Each retry used the same ID after a full
180-second cooldown, as (m') and (t) require. Every actual launch had both
allowed:true and admission exit 0 in the same shell as the scope launch.
No void launch, cap increase or overlapping capped scope occurred. A second
local admission waiter was cancelled before any launch; 69520 was later used
normally for the node obstruction. The initial staging-prefix and verified
prerequisite-receipt guard corrections were also prelaunch own-input fixes;
see `own-input-prelaunch.json` and `cancelled-waiter-69520.json`.

Every scope used MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64 and Lean -M7000. Maximum RSS was **4513783808 bytes**,
with **0 swaps**. The failed-source guard `tools/pv-rjn-20261029/compile.py`
has SHA-256 `4c56bdf63d73b66298ba6970c17f7933ca647ce6acfeb3fe6ad22ca676cbbf3e`; it checks the 517 distinct
historical rejected hashes resolved through git, plus all own failures.
No submitted source matches a previously rejected hash.

Reuse under (h6) was read-only from the verified runjoin and held RJQ
cohorts, including object companions; no imported source/object was rebuilt
or written. Initial preflight: 3,605 project source/object pairs and 7,970
direct fingerprints matched. Final preflight: **3,622** pairs and **8,015**
fingerprints matched, with all **5,673** external objects and **5,438** IR
companions. Source authorities, selected variants, toolchain and ordered
project-before-external lookup were retained. RJQ source verification used
its recorded branch through git, without creating a non-RJN module locally.
The ten historical uncompiled exclusions are unchanged and uncredited;
every new RJN module is compiled. No own scope remains running.

No full frozen release replay ran: the original node contract is refuted
and no complete corrected skeleton witness or release result exists to
replay. No Rust build, ELF operation, extraction, installation, native fixture
replay or key operation ran. `commits.txt` lists the branch changes through
the audited code revision; the final evidence-only commit follows it.
