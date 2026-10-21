# S10 pass 2

Frozen inputs and first-pass evidence remain read-only under
`../s10-inventory-20261021/`. New scripts are in
`tools/s10-inventory2-20261021/`. No shipped source changes are planned.

The rustc probe visits one selected Pool module per invocation, after type
analysis, and records optimized MIR calls with source spans, generic arguments,
indirect calls and drop types. The verifier may use a whole-crate probe.
This uses the pinned Charon nightly (1.98.0-nightly, 14210df0e), independently
of Charon lowering. It is diagnostic native/forced-cfg evidence, not SBF
source equivalence. Only corroborated edges or ELF-confirmed edges qualify.

Each host probe must use MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64, a reservation preflight, and a timed receipt. Derived JSON over
5 MB is represented by SHA-256, size and generator, never committed.

The completeness gate must retain unresolved semantic frontiers. Ownership
assignment and source completeness are separate checks; neither discharges
AcceptedRunJoin or the security target.

Final packet: `reconciliation.json` is the overlay on the immutable first-pass
inventory. All 234 residual records have one proposed owner, and all 10,520
new generic source candidates have one proposed owner/boundary. Fifty-seven
anonymous-name corrections are explicit. `owner-acceptance.json` supplies
S1–S6/S9 review rows; other owners use the overlay and `mir-owners.json`.

`frontier-dispositions.json` explains all 243 original entries. Boundary
accounting, a located source body and a located constant are distinct from
proved source-instance correspondence. `unresolved-sites.json` names all
1,602 retained LLBC trait/indirect calls and 152 ELF callx sites. Full source
completeness remains open; the release gate must exit 2.

The 54,375,173-byte `mir-census.json` is retained only at
`/home/dombarker/project-offloads/codex-cx-s10-inventory2-20261021/mir-census.json`,
SHA-256 `95df1cbb86f6924fba1c3feca6e7f5aca112f2a8c52302f8097da9085c7001c9`.
Generator: `tools/s10-inventory2-20261021/summarize-host.py`. Download it to
`/tmp/cx-s10-inventory2-analysis/mir-census.json` (or supply `--census PATH`),
then run:

```sh
python3 -B tools/s10-inventory2-20261021/reconcile.py --check --require-complete
python3 -B tools/s10-inventory2-20261021/audit.py
```

The first command deliberately fails closed with exit 2; the second validates
the receipt/input pins, exact assignment partition, corroborated edge IDs,
frontier retention, host caps, ELF checks, reused model axioms and mutation
rejection. No Lean compiler, SBF rebuild or runtime suite is rerun.

Raw host compiler receipts identify a wrapper checkout revision separately
from the independently rehashed frozen input revision. The command JSON pins
each actual driver source SHA. Failed driver probes are retained: local-path
qualification, const/function query separation, a stolen elaborated closure
body and an unavailable elaborated constructor query were corrected without
raising memory caps. A later trait-inspection diagnostic found no function
`kind` metadata in the retained monomorphized schema; that failed diagnostic
is also retained rather than advertised as an edge-resolution result.
