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

Pending source/cache and compilation checks.
