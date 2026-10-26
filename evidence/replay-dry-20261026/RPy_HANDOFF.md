# L187 fresh replay handoff

**STOPPED AT REQUIRED ADMISSION BARRIER. L187 open; target not yet established.**

Branch: `codex/cx-replay-dry-20261026`. Research input revision:
`7d1ea416bd4c185e63c278623727adc4f3c9c483`.
Fresh host workspace:
`/home/dombarker/project-offloads/codex-cx-replay-dry-20261026`.
Do not substitute `/home/dombarker/project-offloads/codex-cx-sound-int2-20261025`.

## Claim and limits

This job replays a dependency-order prefix from source. It does not repair
proofs or certify the headlines. The historical planning graph has 10,389
modules; its first 400 are Init modules. The budget is 400 one-module Lean
attempts and zero Kani runs, INCLUDING foundational dependencies. Exempting
Init or silently reusing its cached objects would change the requested scope.
The bootstrap Lean executable is pinned in `RPy_toolchain-launcher-pins.txt`.

Committed research sources were streamed from the pinned revision into the
fresh workspace's `research/` directory. The attempted Init sources are copied
from the pinned Lean toolchain's source distribution; their exact hashes and
actual source imports are in `RPy_source-manifest.json`. A source-import
preflight checks that every direct predecessor occurs earlier in the prefix.
Every launch requires those predecessor objects to exist in the fresh workspace
and pins their hashes. No cached research object is copied into this workspace.

`RPy_graph.json` is the historical audit graph, retained as a planning input,
not relabelled a freshly validated whole-closure graph. It inherits four
unknown circle-module import headers. `RPy_source-availability.json` records
committed-source availability against that historical selection: canonical
sources, exact historical hash matches, or unresolved selection. A canonical
path is availability evidence, not proof that its imports equal cached imports.

## Validation and receipts

`RPy_summary.json` indexes exact targets, exits, wall times, peak RSS, swap,
research revision, source SHA256, dependency fingerprint, and audit status.
Each `RPy_NNN/receipt.json` retains the exact command and verified cgroup
limits: MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. Lean uses
`-j1 -M7000 -DElab.async=false`. `stdout.log` and GNU time output are retained.
Only unchanged existing S2W_run_host.py and S2H_reservation.py execute/admit
work; their hashes are recorded. Job-specific scripts only prepare inputs,
serialize calls, collect receipts and summarize them.

An initial receipt-collection destination typo placed RPy_001 logs one directory
above their intended location. They were moved into RPy_001 without any compiler
rerun. The existing host launchers were not changed. The original traceback is
retained in `RPy_progress.log`. Vanished-cgroup admission scans are retried only
as permitted by local-lean rules 6–7, with host-side redirected logs retained.

A compile receipt's empty `print_axioms` list means **audit not run**, not
standard-only. No new theorem is introduced by this job. No independent
axiom query has yet been issued against the fresh objects.

## Requested definitive axiom findings

(a) Whole-closure list of modules containing nonstandard axiom dependencies:
**not established by this partial replay**. The historical 67-name list is not
promoted to a fresh result.

(b) Reachability from `AspisR1.FGl_Headline.deployed` and
`AspisR1.Rc6_Top.deployed` proof terms: **not freshly established**. Neither
headline has been reached in this replay. Historical standard-only printed
summaries are not reused as a coherent-replay result.

(c) Reached Aeneas FunsExternal_Template axioms and Rust externals:
**not established**. No Aeneas module has yet been reached. This is unknown,
not an empty definitive list.

## Before/after, ledger and non-vacuity

Before and after theorem statements are byte-identical: the sources of
`FGl_Headline.deployed`, `Rc6_Top.deployed` and `FGl_Nonvacuity.composed` are
unchanged. No quantifier, carrier, failure event, conclusion, trust item or
implementation premise is altered. Premises discharged/added/changed: 0/0/0.
The ledger method therefore yields delta **T 0 / P 0 / C 0**; no absolute
recount is claimed for a theorem that was not changed.

Historical non-vacuity is not reclassified: `FGl_Nonvacuity.composed` still
exists in the pinned source, but this run has not freshly certified its
closure or joint inhabitation of all security premises. The dry run does not
change the satisfiability of any premise or construct a new witness.

No session A worktree or candidate is edited. No shipped file, harness, Rust,
Kani, SBF, key or ELF changes; no ELF rebuild trigger. The three inherited ELF
pins remain historical, not newly reproduced. No push.

## Continuation

Completed **361/400 Lean attempts**, all exit 0; **0/0 Kani**. No compiler
failure, timeout, memory kill, cap increase or unchanged rerun. Sum of compiler
wall times: 502.9997756333323 s; maximum peak RSS: 635,768 KiB; total swaps: 0.
All 361 receipts are indexed by `RPy_summary.json`. Object and sidecar SHA256
and sizes are in `RPy_fresh-object-manifest.json`; no objects are committed.
The workspace and its newly compiled objects are retained for resumption.

Last completed: **RPy_361**, `Init.Data.String.Lemmas.Pattern.TakeDrop`.
Next target: **RPy_362**, `Init.Data.String.Lemmas.Pattern`, source SHA256
`7d1547e43f92773fddcf3e5168f19c16af2d9a6ea41ca5b3f640c88d156cd639`.
Attempt 362 was NOT launched; 39 compiler attempts remain unused. The historical
graph has 10,028 listed modules beyond the compiled prefix, with unknown circle
headers potentially adding more.

**Required infrastructure stop:** before RPy_362, the existing admission script
`/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py`
raised FileNotFoundError reading cgroup.procs for vanished scope
`run-r62bbd78f7c344bab889c1391bdfdac41.scope`. After the permitted 30-second wait,
the retry raised the same error for another vanished scope,
`run-r9cc0973c69294b63a61c253402ede16d.scope`. Both full tracebacks are in
`RPy_362-barrier-0.log` and `RPy_362-barrier-1.log`, redirected on the host
before collection. Neither scan produced a reservation JSON. Local-lean rules
5–7 require stopping after the permitted transient retry fails; the whole-budget
instruction does not authorize bypassing or repairing the reservation barrier.
No admission or launcher code is modified. The lead must resolve that issue.
A final read-only process check found no live RPy compiler/runner.

Once the lead resolves admission, resume this SAME fresh workspace at RPy_362
with fresh admission and the existing source/object pins; do not rerun RPy_001
through RPy_361. The existing source plan extends through RPy_400. Further
budget and source selection work are required beyond that prefix. Resolve
missing source/import-header provenance, finish the complete closure, then
perform fresh exhaustive declaration axiom queries (including both headlines)
and the Aeneas-template-to-Rust-external mapping. L187 and the definitive L188
axiom/provenance result remain open.
