# Privacy library v1 coherence replay

Status: **PASS for the repaired v1 cohort**, proof source
`27993341c495ea9107b742c011745b6ed725bebb`. The original merge required the
COH-3 import repair; it is not credited as an unchanged passing tree.

All **834 original PV_LIB modules** are accounted for in one pinned workspace:
384 freshly compiled artifacts and 450 verified cache reuses, with all 788
recorded reuse dependency hashes matching the final freeze. The final inventory
contains 877 PV_LIB modules including 43 compiled replay/audit helpers.

The union contains **4,307 roots** from the v1 JSON and every retained A/B/C
strict-audit list. All passed in **one capped aggregate scope**, using 182
disjoint array selections, one immutable ModuleName→object mapping and the
unchanged private importAll walker/collector. Namespace compatibility passed
1,477 comparisons of repeated kernel declarations. All 47 source-type groups agree with their
source cohorts: zero logical statement changes, including 55 direct Lean Expr
equalities for serialized hygiene-label differences. No proved statement or
proof body was changed; the repair canonicalizes imports in 59 files for 53
identical mirrors.

| Formal release field | Result |
| --- | --- |
| Target | Strict union audit 56595, all 4,307 roots |
| Exit | 0 |
| Wall | 1:00:20 |
| Peak RSS | 7,133,420 KiB |
| Swap | 0 |
| Proof source | `27993341c495ea9107b742c011745b6ed725bebb` |
| Executed driver/config revision | `9d02f25aa027963f6191437a9037cf7bb1ca2e6f` |
| Limits | MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, Lean -M7000 |
| `#print axioms` | Standard axioms only: `propext`, `Classical.choice`, `Quot.sound`; every raw/augmented summary agrees |

The final freeze recheck passed for all 35,570 frozen object/companion files,
1,786 staged sources, the environment and the exact Lean binary. Offline
validation passed: full coverage, cache/source provenance, helper receipts,
array-only collector changes, import-only repairs and both archive hashes.
Failures 56590, 56592 and 56594 remain retained as non-passes.

[FORMAL_RELEASE.json](v1-coherence/FORMAL_RELEASE.json) records exact toolchain,
binary, environment and freeze hashes as well as the required release fields.
[VALIDATION.json](v1-coherence/VALIDATION.json) records the final checks.
[FINAL_MODULE_INVENTORY.json](v1-coherence/FINAL_MODULE_INVENTORY.json) enumerates
every current module; the original inventory retains every root's provenance.
[COLLECTED_MANIFEST.json](v1-coherence/COLLECTED_MANIFEST.json) and
[RAW_GRAPH_MANIFEST.json](v1-coherence/RAW_GRAPH_MANIFEST.json) identify the
ordered archive parts and hashes. All 4,307 actual raw walk files are retained.
The archives use parts of at most 10 MiB; `validate.py` checks them offline.

The remaining sections retain the input provenance and chronological findings.

Original merge revision: `9a38706526c45bc0fac071869458400a07aaaba7` on
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
Kernel root-type comparisons and the strict union outcome are completed above.


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
attempt is not a pass; the replacement result is recorded below.

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
The successor compilation result is recorded below; this failed compile is not a strict audit.


COH-2 replacement passed 56536: `PV_LIB_V1_RawAudit2`, exit 0,
wall 0:02.44, peak RSS 1757304 KiB, swaps 0, standard axioms only.
The unchanged-body comparison passed. This was a compile preflight.

The dependency replay completed: all 834 v1 PV_LIB modules are compiled or
matched to accepted cached source/object/dependency hashes in one LEAN_PATH.
The 56534 launcher exit 3 is its explicit empty-queue completion marker;
no compiler or scope ran for that ID. It is not a Lean failure or a raw pass.
The frozen workspace records 35,569 object/companion file hashes and 1,785
retained staged source hashes (including inactive preflight sources, which
are not credited as active proof modules). Toolchain Git hash and Lean binary
SHA-256 are retained in COHORT_FREEZE. This initial replay stage used source pin 9a38706526c.


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


The canonical import repair is pinned to `27993341c495ea9107b742c011745b6ed725bebb`.
`ACTIVE_INVENTORY.json` carries its file hashes; the original `INVENTORY.json`
remains the 9a38706526c input inventory. The repair affects 353 module artifacts;
only those descendants are replayed. Unchanged artifacts are reused read-only
in `objects-canonical` within the same host workspace. The old failed cohort,
its sources, objects and freeze are retained. The final combined environment
selects 734 canonical modules while preserving all 4,307 root names.

A staging-only compile 56539 stopped before elaboration because Lean resolves
source symlinks outside its `-R` root:

```
input file '.../sources/PV_LIB_SPEC_SiteHistory.lean' must be contained in root directory (.../sources-canonical/)
```

Exit 1, wall 0:00.06, peak RSS 83948 KiB, swaps 0. The source symlinks were
retained under `symlink-staging` and replaced with immutable hardlinks to this
job's own source files. No host file was deleted and no source byte changed.
The replacement `PV_LIB_SPEC_SiteHistory` passed 56540 (exit 0, wall 0:02.23,
peak RSS 4841048 KiB, swaps 0). Tool staging skips writes of unchanged sources.


The affected replay completed: 189 focused module recompiles passed and 164
artifacts matched verified hashes after their rebuilt dependencies stabilized.
All 834 v1 modules are again present under the single canonical LEAN_PATH.
The 56549 exit 3 is a no-scope empty-queue completion marker.
`PV_LIB_V1_RawAudit3` compiled 56550 (exit 0, wall 0:02.36, peak RSS
1755192 KiB, swaps 0, standard axioms only); its module array chooses canonical
providers and its root array retains all 4,307 roots. The collector/walker body
comparison passed unchanged. Canonical object, companion and source hashes are
frozen separately as `COHORT_CANONICAL_FREEZE`; the failed merge freeze remains
retained. Root-type comparison and final strict audit results are recorded above.


### COH-4: full-root import exceeds the fixed Lean memory threshold

56551 (734 module heads) and 56556 (708 exact root-owner heads; 684 library
modules in their closure) both stopped during import, before printing a root
type, with:

```
excessive memory consumption detected at 'interpreter' (potential solution: increase memory consumption threshold)
```

56551: exit 1, wall 0:19.48, peak RSS 7174820 KiB, swaps 0.
56556: exit 1, wall 0:19.09, peak RSS 7201248 KiB, swaps 0.
Both use source revision 27993341c49. The second input removed 50 uncited
library modules from the imported closure; no failed shape was retried with a
higher cap. The full-import approach was then stopped. These full-import attempts are not strict union passes.

The replacement uses one frozen ModuleName→object mapping and one canonical
source revision, with disjoint root batches (35 batches, at most 125 roots).
This is batching a single cohort, not combining input-cohort audit results.
The graph-wide metadata gate 56558 performed 1,477 comparisons of repeated kernel
declarations. Every type and definition body matched exactly; theorem proof bodies
are compared by their unchanged type under proof irrelevance. All comparisons
passed (exit 0, wall 0:00.98, peak RSS 2213636 KiB, swaps 0). The repeated names
are generated equation/auxiliary declarations; the conflicting nominal lane
mirrors were already canonicalized. ROOT_IMPORT_PREFLIGHT records the complete
root→owner mapping and 3,795-module dependency closure.

The new array-only batch drivers all compiled in 56559 (35 passes; aggregate
exit 0, wall 0:30.70, peak RSS 1593364 KiB, swaps 0, standard axioms). Collector
and walker bodies are unchanged. The initial aggregate56590 used these batches serially under ONE admitted
capped scope. The controller returns nonzero
if any process, root, summary comparison or axiom check fails. It uses the
same canonical objects for every batch and checks exact root-union coverage.

A new metadata helper candidate 56552 failed on an unavailable Inhabited
instance for ModuleData×CompactedRegion (exit 1, wall 0:00.64, peak RSS
1560392 KiB, swaps 0). Its diagnostic-generated sorryAx is not a pass or an
active placeholder. The failed input is archived. Its successor
PV_LIB_V1_ModuleDeclarations2 uses an explicit optional lookup and passed56553
(exit 0, wall0:00.73, peak1570380 KiB, swaps0, standard axioms). Header scan56554
also passed (exit0, wall0:01.14, peak2165220 KiB, swaps0). No library statement
or resource cap changed during this isolation.


### COH-5: serialized hygiene labels, checked against actual kernel expressions

The complete 35-batch merged type scan passed in56560. The original-cohort
comparison resumed from retained hashes rather than re-running it. Older source
resolutions lacked common framework/transitive entries:56560 stopped at missing
Init.Prelude,56561/56562 at missingPV_STX2_LiveNumbering. Exact diagnostics and
resource fields are retained. Missing framework entries were supplied from the
pinned shared toolchain cache; missing PV entries were supplied only from the
specific historical cohort authority or where ALL retained verified authorities
agree on one historical object hash. Existing cohort entries always win. No
current repaired PV proof is used to invent an old reference type.

56563 completed all47 source groups but returned1 because raw `reprStr` differed
for34 A/session16 and21 SPEC/session9 roots. TYPE_SERIALIZATION_DIFFERENCES
retains exact pairs. Inspection showed module names embedded in synthetic
lambda/let binder labels (for example abort_state_free's source binder label
contains SPEC_LaneA_Graph and the canonical label contains Graph). Bound-variable
indices, constants, quantifier kinds and universes were unchanged.

The new StatementAlpha verifier loads the exact type expressions directly from
both pinned module files, first checks each against its captured representation,
then compares Lean Expr values and universe parameters.56565 passed ALL55 pairs:
55/55 raw Expr equalities TRUE,55/55 same universe parameters,55/55 annotation-only
checks TRUE. The custom annotation erasure was redundant: the original Lean
expressions already compare equal. No theorem statement was edited, weakened,
unfolded or repaired on this account. STATEMENT_COHERENCE records4307 merged roots,
47 source groups and ZERO logical statement differences.

56563: exit1,wall6:29.22,peak6847956KiB,swaps0 (representation differences, not a pass).
56564 helper compile: exit0,wall0:00.78,peak1575424KiB,swaps0,standard axioms.
56565 exact type check: exit0,wall0:00.82,peak1599012KiB,swaps0,standard axioms.
The failed/cohort-specific checkpoints remain retained and are not promoted to
successful aggregate audit evidence. The canonical object/source freeze check
passed unchanged after these comparisons.


### COH-6: buffered strict-audit memory, changed root-array shape

The first aggregate strict union attempt 56590 FAILED in its first 125-root
batch with `excessive memory consumption detected at 'interpreter' (potential solution: increase memory consumption threshold)` under Lean -M7000. Aggregate
exit1, wall0:37.97, peak7168780KiB, swaps0, source27993341c495ea9107b742c011745b6ed725bebb.
It emitted no buffered result records; 99 partial raw graph files were retained
in failed-56590-graphs.json.xz before their filenames were reused. This is not
a pass and does not establish any union coverage.

The replacement changes only the module/root array acquisition to immutable
JSON selections of at most25 roots. The collector and private importAll walker
are byte-identical to Session19 outside array selection. One driver object is
used for every selection; per-selection hashes and the driver object hash are
recorded. No source proof or cap changed. Compile56566 passed: exit0,
wall0:00.96, peak1586816KiB, swaps0, standard axioms. Focused diagnostic56591
passed75 roots across three selections including the earlier failing region:
exit0, wall0:42.34, peak7064200KiB, swaps0. This diagnostic is not counted as a
union audit. The replacement aggregate56592 covered173
disjoint selections in ONE capped scope using the same frozen canonical cohort.


The changed25-root aggregate56592 also FAILED; it is not a union pass.
It completed1,600 roots before narrow064 failed with the same exact interpreter
memory diagnostic quoted above. Aggregate exit1, wall18:49.44,
peak7169596KiB, swaps0, source27993341c495ea9107b742c011745b6ed725bebb.
The failed batch combined lane-B slice statement/typedDrop providers with
lane-C ActiveAdoption19/ActiveBoundary19 providers. Its module/root arrays are
retained in NARROW_ROOT_BATCHES, and every completed result remains retained
without being credited as successful union evidence. Failed raw graph files
are preserved separately before reuse.

The next input shape splits every mixed source-family batch at its family
transitions, yielding182 disjoint selections, still at most25 roots each.
The failing25-root batch becomes13 slice roots and12 specification roots.
FAMILY_ROOT_BATCHES records the exact refinement and parent batch names.
The driver, collector, walker, source revision and resource caps are unchanged.
Diagnostic56593 tests the two affected imports before any replacement union
attempt. No failed memory shape is rerun unchanged or given a larger cap.

Diagnostic56593 passed both refined inputs:13 slice roots and12 specification
roots. Aggregate exit0, wall0:57.29, peak6955692KiB, swaps0, standard axioms,
source27993341c495ea9107b742c011745b6ed725bebb. This isolates the memory
problem to the mixed import/collection shape, without a model or theorem change.
The replacement182-selection aggregate56594 started again from the first root; no
partial56592 result will be credited to its strict union result.


Historical replacement aggregate:56594, driver/config revision5c9b6b294da,
proof source27993341c495ea9107b742c011745b6ed725bebb. It executes all182
FAMILY_ROOT_BATCHES selections in one capped scope, starting from the first
root. It later terminated120 after the SSH transport loss described in COH-7.


### COH-7: SSH-dependent controller output, not a proof failure

56594 terminated with NONZERO120 after2,950 retained root results; it is NOT a pass.
Finalized GNU time records wall43:36.73, peak7040000KiB, swaps0,
source27993341c495ea9107b742c011745b6ed725bebb. Client transport exited255:
`Read from remote host 100.108.41.90: Operation timed out` followed by
`client_loop: send disconnect: Broken pipe`. The capped scope briefly continued
but the Python controller ended120 following the output-pipe loss; its final stderr was lost with that pipe.
No Lean batch failed. The partial union remains strict_pass=false. The original
controller died before writing its receipt; recover-transport.py explicitly
marks a FAILED reconstructed receipt based on the finalized time file and
partial union report, and does not claim to recover a successful result.

The replacement launcher persists its exact controller and payload and starts
them in a new host session with stdin/stdout/stderr bound to host files. It
asserts that stdout is a regular file before admission and launches the same
capped scope. SSH only returns the background PID/ack; the job's actual
receipt remains authoritative. This changes the failed transport environment,
not the walker, collector, proof source or caps. FINAL_ROOT_BATCHES orders the
remaining untested arrays first and then replays every earlier root. No partial
result is reused as strict union coverage. The full retry is required because
the interrupted aggregate did not pass; it is not an unchanged regression.

The finalized partial2950-root report includes narrow117p0, which was written
before its streamed progress line was lost. Thus the final ordering begins
with that one already-completed batch followed by previously untested batches;
it still reruns every root. The detached56595 launch ack records the PID,
controller/payload hashes and host stdout path. Live unit properties confirm
MemoryHigh6442450944, MemoryMax8589934592, MemorySwapMax0, TasksMax64.


## Final disposition

56595 completed all182 selections and4307 roots with exit0. Its detached
controller/payload are retained by hash and content. The final freeze and
offline validation both passed; no additional Lean run followed the successful
aggregate. All formal attempts retain their original target/exit/resource/source
and axiom records in the metadata archive. The reconstructed56594 receipt is
explicitly marked failed and recovered, using finalized GNU time and the partial
2950-root report; it is never counted as a pass.

One offline validator schema error (`KeyError: target`) was corrected to accept
both per-target and batch `targets` receipt shapes. Cap, compilation, coverage,
source/body, type, axiom and archive checks remain mandatory. The corrected
validator passed; the formal audit was not repeated for this metadata fix.

Premises removed/added:0/0. No OwnInit joint witness or ledger row closure is
claimed. The final result establishes the repaired library's coherent replay.
