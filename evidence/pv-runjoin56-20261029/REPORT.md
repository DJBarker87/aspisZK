# Runjoin56 — checked obstruction in the fixed QueryAppend link

**Target not yet established. None of the six links was discharged. Rows removed: none.**

Exact worktree `/Users/dominic/ZK/.worktrees/pv-runjoin`, branch
`codex/pv-runjoin-20261026`, entry `6ecb132a54b86fa951e25aa93c23a4769ca7286c`.
The fixed Link definitions and `Fields` are byte-identical to entry. Protected
`PV_RJDec_` and `PV_OWN*` prefixes and frozen Rust/client sources are unchanged.
Step (4) has not started. No installation, endpoint premise or TrustItem changed.

## Checked finding

`PV_RunJoin_QueryNativeObstruction56.complete` (68214) proves, under the actual
selected dictionary, for every run family, index and publication:

```
Fields (runs i) p → plan.offOpenings ≤ Usize.max →
  ¬ PV_RunJoin_Link_QueryAppend runs
```

The theorem has no index-rejection hypothesis and no external commitment
inhabitation hypothesis. It constructs its own unused commitment values and
an output buffer of exactly the required length, symbolically.

The fixed `Fields` predicate constrains front fields only. Its truth is
unchanged when the publication's backend commitments and query array are
replaced. `QueryLinkObstruction56.poison` sets both commitments to `some` and
sets all 22 queries to **262144**. The first query is already invalid:
`FIBRE_COUNT = 1 << 18`, and `FibreIndex::new` uses a strict upper bound.
The source calls `.unwrap()` before reading opening data. The checked
emission returns `Result.fail Error.panic`, whereas the fixed QueryAppend
link demands an `ok next` for the same publication and buffer.

`QueryInvalidIndex56.source` (68206) checks exactly that first failure, without
unrolling the remaining queries. `QueryIndexInstalled56.rejected` (68208)
identifies op75 with the actual installed index guard, using a named field
projection and the retained dictionary preservation law. `source-rejection-finding.json`
records hashes and a script-checked comparison of the Rust rejection prefix,
constant, macro guard, cast and unwrap with the emission. This is source
inspection plus a Lean source-model result; no native differential or new
complete Rust refinement is claimed.

`PV_RunJoin_QuerySuccessfulObstruction56.complete` (68215) composes this with
the unchanged successful-run reach theorem, R24 theorem, coefficient caller
and opening images. Its hypotheses are the fixed CommonSample, BackendInput,
FinishContext and QueryAppend links, a successful actual `source (runs i)`
Result and a representable opening offset; its conclusion is **False**.
Thus these four links cannot jointly serve their intended successful-run use.
NodeAppend and PublishOrder are not needed for the contradiction.

The representable-offset/nonempty-Fields conditions are explicit. Empty run
families, families without Fields instances and impossible output offsets
are not unconditionally refuted. This is **not** a counterexample to privacy,
a ledger row, or the correctness of query indices actually produced by an
honest run. The malformed publication is admitted by the fixed link's own
universal quantifier, not asserted reachable from `finish_opening`.

The requested all-six discharge cannot be completed while preserving this
statement. Work stops on this checked source/link obstruction, with budget
unspent; no definition was weakened or silently restricted. A lead decision
on the incompatible interface is the next concrete deliverable.

## Link status

| Link | Status |
| --- | --- |
| CommonSample | **Open.** Both returned circle-point/transcript records are now associated with the common tape by `CommonCircleSuccessFirst56.complete` (68202) and `CommonCircleSuccessSecond56.complete` (68203), retaining the original address, causality, collision/public-address and framed-record hypotheses. This is not the complete stored-record association: semantic/opening challenge threading, all Data fields and coefficient-trace composition remain. |
| BackendInput | **Open.** No new producer discharge. The complete hinput producer, pointwise message association and canonical coefficient derivation remain. Prior length results are reused only as their stated partial results. |
| FinishContext | **Open.** No new discharge; actual folded leaves/tree/root, tags 30–32, final fold, public checks and front-field association remain. |
| QueryAppend | **Incompatible as specified with nonempty Fields and representable opening offsets**, by 68214/68215. Never weakened. |
| NodeAppend | **Open.** Six multiproofs, indices, deduplication, padding and complete Result/byte association remain. Not discharged. |
| PublishOrder | **Open.** Concrete serializer ordering/guards and all source appends remain. The previous conditional theorem remains conditional. |

R24Sampler remains discharged by runjoin54. No whole ledger row was removed;
in particular V038, V045, V163, V165, V167, V244, V258–V260 and V262 receive
no new whole-row credit. Endpoint P removed/added/weakened/changed:
**0/0/0/0**. The eight endpoint fields and three TrustItems, V370 and the
D381/D386 boundary, deployed disclosed/observerOracle and op79/op254
identifications, observer/simulator/coupling/bad/query events, failure
independence and side-channel obligations remain unchanged.

## Verification and resources

**19 Lean compiler launches:** 68200–68215 and audit IDs 68297–68299.
**10 accepted, 9 rejected, 0 Kani.** IDs 68216–68296 remain unused (81 attempts).
Every rejected source is retained by its verified Git blob in
`retained-failed-sources.json`; none was resubmitted unchanged. The final
source of every added proof module has an accepted compile and audit.

The first two circle-success failures were replaced with direct elimination
of the concrete parser Result. Other rejections concern scalar size bounds,
record layout, explicit carrier arguments and redundant closed-goal tactics;
no cap, heartbeat or recursion limit was raised. Failed/sorryAx outputs earn
no credit. No memory kill occurred.

All 19 launches used atomic successful admission and allowed:true checks in
the same shell as the scope launch, with no refusal or scope overlap. Each
scope used MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64 and Lean
-M7000. Maximum RSS: **4,500,496,384 bytes**; swaps: **0**. The wrapper's
line-wide failed-source SHA guard hash is
`656e40a99395f4527591b70a8f02911cc09f224f5cf92824ede04f9230939f6e`.
It is also recorded in `boundaries.json` and SUMMARY.

Audit source revision: `b08d16e5bcf18b9832e736682f33046c294886f5`.

| ID | Exact target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | --- | --- | --- | --- | --- |
| 68297 | R1Z.PV_RunJoin_CircleAudit56 | 0 | 2.07 | 4463136768 | 0 |
| 68298 | R1Z.PV_RunJoin_QuerySourceAudit56 | 0 | 1.91 | 4468727808 | 0 |
| 68299 | R1Z.PV_RunJoin_LinkObstructionAudit56 | 0 | 1.80 | 4476538880 | 0 |

All printed accepted axioms are subsets of propext, Classical.choice and
Quot.sound. Every added theorem is covered by `audit-design.json` and
`audit-coverage.json`. Receipts record exact target, exit, wall, RSS, swap,
source revision/hash, dependency fingerprints and original axiom lines.
All 38 original per-module output/time logs were hash-verified and retained
in `original-module-logs.json.xz`.

The initial read-only cache preflight matched 3,575 project source/object
pairs, 7,903 direct fingerprints, 5,673 external objects and 5,438 IR companions.
The final preflight matched **3,585** project source/object pairs and **7,935**
direct fingerprints, with the same external/IR objects; all matched.
The same pinned private host workspace was reused; no shared or other-job
object was written. The historical uncredited 67723 object remains provenance
only and is not a new credited root.

No full frozen release replay, Kani, Rust build, ELF operation, native fixture
replay, extraction or step-(4) installation ran. No key was accessed or
cleaned up. See `commits.txt` for the branch changes since entry.
