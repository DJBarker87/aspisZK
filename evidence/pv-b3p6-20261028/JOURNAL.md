# P6 continuation of batch 3

Exact worktree: `/Users/dominic/ZK/.worktrees/pv-b3p6`.
Branch: `codex/pv-b3p6-20261028`; candidate: `5fa2cc6781`.
Host: `/home/dombarker/project-offloads/codex-pv-b3p6-20261028/`.
Lean IDs 42500–42599 only; 42597–42599 reserved for final audits.
Budget: 100 charged Lean attempts, 12 Kani runs. One capped scope at a time.
No change under crates/ or programs/. No shared source/object writes.

Read pv-common.txt and restored flag, including all rulings through (p').
External h4 preflight verified all 5673 objects, zero mismatches, before any
compile. Source authority for project closure is EJR/freeze then own tracked
HEAD, with h5' precedence; resolved six-module op133 closure has no missing
module. Recount6 target files are absent from candidate; six exact rows and
ROWS6 lines were read with git show from committed research. authority.json
records that revision. No changes to ledger, trust items, simulator or observer.

## V229 / op133

The shipped original in aspis-statement has no arguments: it builds the
schedule, collects producer/consumer endpoints, sorts and deduplicates. The
owned reference is a literal 214-element array, outside shipped crates. Its
inventory derives from the frozen host copy's 136 MASK_LINKS; that derivation
is only preflight, not the native association. The no-stub Kani harness calls
the original aspis-statement function, checks success, exact length and every
row against this reference, with unwind1026 and unwinding assertions.

charon133-01 failed before extraction because the source snapshot omitted the
three pinned writer crates. charon133-02 then exposed a missing included
pinned glue_gen.rs. Both failures are retained; dependencies were added before
retrying. charon133-03 accepts the actual root (12.072s, 543968KiB, swap0).
aeneas133-01 accepts under unchanged pinned extractor/strict joins
(0.227s, 55264KiB, swap0). The B1 port changes only imports. There are no
mutable-borrow writes or backward continuations in the literal reference.

kani133-01 fails compilation on omitted proof-only tree.rs in the snapshot.
After uploading its pinned tool sources, kani133-02 exposes 21 pre-existing
proof-only records caller arity errors. The proof-only compatibility wrapper
in tools/r1-builder-reference/records.rs calls the unchanged seven-argument
shipped records with pair_empty_roots(), preserving the old helper convention.
It neither stubs nor changes the op133 closure. kani133-03 runs with this
source repair; timeout900s, taskset0–3, MemoryHigh6G/MemoryMax8G/swap0/Tasks64.
The 900-second gate is the first solver run, not a retry after a180s timeout.

Lean law and original-carrier installation are drafts until compiled.
Native differential is queued and will be labelled finite validation.
No row closure or endpoint premise removal is claimed at this stage.

## Other target rows

V228/op132, V241/op224, V243/op226, V244/op227 and V245/op228 remain OPEN.
The inherited batch3 extraction refusals/failures are not counterexamples.
Field arithmetic in op224/op227 requires structural or Lean correspondence,
never chained-field Kani. Finish op133 before starting partial work on them.

T remains exactly entropy_law, entropy_kernel, observation.
Target not yet established.

Ten-minute gate review: no new proof target has completed during kani133-03.
The obligation is a singleton-input control-flow/indexing/sort calculation,
not chained field arithmetic. Memory caps are unchanged and will not be
raised. Retain the current 900s timeout; on timeout inspect the exact phase
and shrink/split the bounded harness before another run. The frozen original
collects at most272 endpoints; a273 unwind split can test whether the1026
bound created pathological symbolic sort expansion, with unwinding assertions
still enabled. A failed candidate is retained and is not a row counterexample.
