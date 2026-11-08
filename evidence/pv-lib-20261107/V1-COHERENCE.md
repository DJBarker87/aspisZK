# Privacy library v1 coherence replay

Status: in progress; coherence is not established.

Source revision: `9a38706526c45bc0fac071869458400a07aaaba7` on
`codex/pv-lib-v1-20261108`. Manifest inputs are lane B `43fa17cd4a5`
(including lane A `fbc60bd811d`) and lane C `87e34a2b2af`.

`v1-coherence/INVENTORY.json` enumerates all 834 branch PV_LIB modules,
4,299 distinct roots and their manifest/audit-list provenance, and the
919-module repository-local import closure. The retained historical audit
lists are included, not merely the last session of each lane. The exact v1
JSON read from research is retained as `v1-coherence/V1_MANIFEST.json`.

Replay uses a new isolated subdirectory of the retained lane B host workspace;
accepted caches remain read-only. Source hashes, object hashes and cache
authorities must be retained before reuse. No cold package build is allowed.
Lean attempts use 56500–56589; the sole final strict union audit uses
56590–56599. Every scope is serial, MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64, Lean -M7000, with a separate SSH turn and
reservation admission. The final audit must return zero to pass.

No OwnInit witness, row proof, ledger, lane A/C branch, or proved statement
is changed. Premises removed/added: zero. Privacy target not yet established.

## Findings

STAGING-1 (attempt 56500, not a model/theorem finding): the first
`PV_LIB_Graph` invocation exited 1 in 0:00.10, peak RSS 175892 KiB,
swaps 0, before elaboration, with the exact diagnostic:

```
.../v1-coherence/sources/PV_LIB_Graph.lean:1:0: error: missing IR data file for module Init.Prelude
```

The isolated cache staging omitted the `.ir` companion files. The replacement
staging includes them and corrects the selected source/object pairing for
repository-local providers before any proof is credited. No source theorem,
statement, host infrastructure or cap changed. Attempt 56501 passed the same
first module under that changed environment. All failed records are retained.

Merged source files match all 1,567 supplying A/B/C input-file comparisons
(`v1-coherence/SOURCE_COHORTS.json`); no source-file difference was found.
Kernel root-type comparisons and the sole strict union audit remain pending.


### COH-1: incomplete dependency ordering exposed by an opaque cached provider

Attempt 56516 failed on `PV_W5_F32Specification`, a retained lane B slice
provider (`bd6ac9790a689392cf5f356da55f26319256df24b7c67eb09a27fdb95c34d19f`).
Exit 1, wall 0:00.58, peak RSS 1393176 KiB, swaps 0, source revision
`9a38706526c45bc0fac071869458400a07aaaba7`. Exact diagnostic:

```
.../v1-coherence/sources/PV_W5_F32Specification.lean:1:0: error: unknown module prefix 'PV_W5_MallocOwned'

No directory 'PV_W5_MallocOwned' or file 'PV_W5_MallocOwned.olean' in the search path entries:
.../v1-coherence/objects-resolved
.../v1-coherence/objects-resolved
/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean
```

`PV_W5_MallocOwned` was already in the replay plan, but after its consumer:
the pinned STX `PV_W5_F59Frame` cache object has no retained source at the
survey's inferred source path, so source-import traversal missed its dependency
edge. Its object hash is
`474bb1c9d6242e0173a9718975ecc6ed5fa944c435fa34af008c0da84459e488`.
The repair is dependency/import ordering, using the actual cached module headers
for all 23 such provider objects. No proved statement is edited. The failing
attempt is not a pass; replacement compilation remains pending.
