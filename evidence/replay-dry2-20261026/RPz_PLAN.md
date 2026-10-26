# Corrected L187 replay

Input revision bb0b0f5b12b28ddbe761267973ae8db1a9a89edb; target
AspisR1.Rc7_Top.deployed. Budget 600 Lean compilations, zero Kani.
The owner exempts pinned Lean v4.32.0 and pinned library objects from source
replay. Repository modules are compiled from committed source in actual source
import order. Historical closure manifests select source provenance where no
canonical source exists; they do not replace a fresh source import traversal.

Fresh workspace: /home/dombarker/project-offloads/codex-cx-replay-dry-20261026.
Use only RPz_ metadata/evidence plus newly built repository objects; preserve
RPy's Init outputs but prefer sysroot Init objects. No historical repository
objects enter LEAN_PATH. Existing S2W runner/admission scripts remain unchanged.
Each attempt uses one 6G/8G/swap0/tasks64 scope and -j1 -M7000. Admission
contention retries follow local-lean 6–7. Failed modules are never retried
unchanged; dependent modules are blocked while independent modules continue.

Stage 1: committed source selection/import graph and trusted-base hashes.
Stage 2: up to 600 dependency-order module compilations, exact receipts.
Stage 3: fresh-object axiom audit if reachable; otherwise explicit partial
findings, frontier and handoff. Commit each stage, never push.

No theorem statement changes: before/after Rc7_Top.deployed identical.
Premises removed/added/changed 0/0/0; ledger delta T0/P0/G0/C0.
Historical Rc7 conditional non-vacuity is retained, not a fresh joint fixture.
No shipped-file changes; no ELF rebuild trigger. L187 remains open until the
complete repository closure is replayed; the release target is not established.
