# Privacy library v1 coherence replay

Status: in progress; coherence is not established.

Source revision: `9a38706526c45bc0fac071869458400a07aaaba7` on
`codex/pv-lib-v1-20261108`. Manifest inputs are lane B `43fa17cd4a5`
(including lane A `fbc60bd811d`) and lane C `87e34a2b2af`.

`v1-coherence/INVENTORY.json` enumerates all 834 branch PV_LIB modules,
4,307 distinct roots and their manifest/audit-list provenance, and the
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

The first header repair missed cache-only intermediate modules. A shell
orchestration error continued after its failed ordering assertion and repeated
the same missing-module error in 56520 (exit 1, wall 0:01.15, peak RSS
1390600 KiB, swaps 0). This was an unchanged failure, not a pass. It is retained
as an automation error. A permanent precompile guard now refuses a repeat while
the named missing object is absent.

56518 spent its ID after a 361.41-second host turn but stopped at a task-local
staging assertion before admission or a compiler scope: a not-yet-run comparison
script had changed during the wait. Its exact traceback is retained in
`transport-56518.json`; no compilation is credited. The staging guard now keeps
Lean source immutability while permitting revisions to unexecuted task scripts.

The full actual cache-header scan 56521 passed (exit 0, wall 0:01.12, peak RSS
1977184 KiB, swaps 0, standard axioms on the helper). The verified ordering
places MallocOwned at 888 and F32Specification at 975 in the complete replay
order. `ORDER_REPAIR.json` retains before/after arrays and actual header edges.
No source theorem or statement changed.


COH-1 replacement passed in 56523: `PV_W5_F32Specification`, exit 0,
wall 0:02.30, peak RSS 4625128 KiB, swaps 0, the same v1 source revision and
unchanged source hash. MallocOwned passed first in 56522. The full predecessor
chain was built/reused in corrected dependency order; no proved statement or
proof body was edited. This resolves the missing-module compilation finding.


The final inventory also includes eight roots retained in historical Lean
strict-audit arrays whose JSON list had been replaced. The full union is
4,307 roots (the initial JSON-only enumeration had 4,299).

### COH-2: generated audit-array shape

The first new union-driver compile 56535 failed before any raw audit:

```
.../PV_LIB_V1_RawAudit.lean:5:11: error: maximum recursion depth reached in the code generator
function inline stack:
List.headD
inferInstance
...
```

Exit 1, wall 0:01.60, peak RSS 1618104 KiB, swaps 0, v1 source revision
`9a38706526c45bc0fac071869458400a07aaaba7`. This is the generated 4,307-name
array's code-generator shape, not a library statement failure. The failed
input is archived as `failed-driver-56535.lean.xz`. Its successor is the new
`PV_LIB_V1_RawAudit2` module, with named noinline array chunks of at most 128
names. Collector/walker code remains byte-identical after removing the array
definitions and array expression. No recursion-depth setting or cap was raised.
Replacement compilation is pending. The sole strict raw audit has not run.


COH-2 replacement passed 56536: `PV_LIB_V1_RawAudit2`, exit 0,
wall 0:02.44, peak RSS 1757304 KiB, swaps 0, standard axioms only.
The unchanged-body comparison passed. No strict raw audit has run yet.

The dependency replay completed: all 834 v1 PV_LIB modules are compiled or
matched to accepted cached source/object/dependency hashes in one LEAN_PATH.
The 56534 launcher exit 3 is its explicit empty-queue completion marker;
no compiler or scope ran for that ID. It is not a Lean failure or a raw pass.
The frozen workspace records 35,569 object/companion file hashes and 1,785
retained staged source hashes (including inactive preflight sources, which
are not credited as active proof modules). Toolchain Git hash and Lean binary
SHA-256 are retained in COHORT_FREEZE. The library source pin remains 9a38706526c.


### COH-3: duplicate namespace declarations across lane mirror modules

The first combined environment failed in 56537, before any strict raw audit:

```
uncaught exception: import PV_LIB_SPEC_LaneA_Graph failed, environment already contains 'PV_LIB.Observation.abort.elim' from PV_LIB_Graph
```

Exit 1, wall 0:18.65, peak RSS 6317488 KiB, swaps 0; source revision
`9a38706526c45bc0fac071869458400a07aaaba7`. The import-only lane-C `LaneA`
and lane-A `C18` source mirrors redeclare the same public namespace under
different module identities. Individually compiling them did not expose this.

`IMPORT_CANONICALIZATION.json` identifies 53 mirrors whose complete declaration
bodies are byte-identical to their canonical source after removing imports.
The import repair redirects 59 consumer files to canonical modules. No theorem
statement, definition body, or proof body changes. Mirror files remain retained
and independently compiled compatibility inputs; the combined root environment
selects one canonical provider per duplicated namespace. It still audits every
root in the 4,307-name union, and source-cohort type comparisons must pass.
This is a changed import graph and will be replayed before any coherence claim.
