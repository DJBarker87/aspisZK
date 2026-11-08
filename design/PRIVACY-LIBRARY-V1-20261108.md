# Privacy library, version 1 (2026-11-08)

Branch `codex/pv-lib-v1-20261108`, commit 9a38706526c. It merges library lane B at 43fa17cd4a5, which already contains lane A at fbc60bd811d, with specification lane C at 87e34a2b2af. The merge has no conflicts. The branch is local and has not been pushed or merged to research or main. Per-slot data is in PRIVACY-LIBRARY-V1-20261108.json.

## Contents

The library contains the 29 per-function privacy specifications of the B-y ledger (11 slice, 18 thread). Each has a compiled whole-contract statement: Pre, Post, MachineSpec and Contract over named definitions. Corrected successor statements live in new modules, and the originals are retained for the recorded model corrections (SPEC-C2 to SPEC-C18, A-S16-1/2, and the five session-5 corrections).

The library map pairs every caller with the contract it consumes at each call site, across 170 slots:

| Status | Slots | Meaning |
| --- | --- | --- |
| INSTANTIATED | 126 | A compiled adapter of a CLOSED provider: deterministic model graph, caller-domain lemma and local machine adapter. |
| CORRECTED-STATEMENT | 5 | The old statement was wrong. A corrected statement is compiled in a new module, with before and after recorded. |
| WAITING-ON-ROW | 39 | The callee or facet has no CLOSED provider. Each slot names the open ledger row it waits for. |

No slot is simply missing. The 39 waiting slots point at exactly the 29 ledger rows that are still open (125 rows, 96 CLOSED). They fill as those rows close, and those rows are paused under D969. One waiting slot, slice:f7 typedDrop178, already has a compiled and audited runtime adapter (PV_LIB_SLICE_RuntimeDrop.certified). Only its caller-context discharge waits on slice:f7.

Also included: the store-action table PV_LIB_StoreActionTable.v2, the native, TLS, allocation and Vec instance modules, and the parametric physical entry world EntryWorld18 with its concrete inhabitant.

## What version 1 does not establish

- **Joint premise satisfiability (the OwnInit joint witness) is not proved.** The library's statements have not yet been shown to be jointly satisfiable on one real execution. Lanes A and C continue this at lower priority. The original history is proved to step 141 on the repaired v2 machine, and four join targets (LaneAJoins19) remain open.
- **No combined coherent replay of the v1 tree has run.** Each input cohort passed its own strict audit with standard axioms only: lane B 56490 (141 roots), lane A 55692 (239), and lane C's audits through session 19. Separate compile passes do not establish coherence of the merge; a replay of the merged tree is the next gate.
- **Library results are not row closures.** INSTANTIATED means the callee contract is usable at that slot. Actual caller invariants and the native, source and binary adequacy remain obligations of the consuming row. No ledger row, endpoint premise or T field changed. The privacy headline is unchanged.

## Model corrections for the owner

These model corrections were found while building the library. Each is checked in Lean and repaired in new modules:

- **SPEC-C13.** The Entry14 fixture cannot exist physically: its run pointer contradicts the binary's stack layout.
- **SPEC-C14.** The fixed runtime of the eighteen frozen contracts replies Ok(null) where the real TLS gives Ok(false).
- **A-S16-2 / SPEC-C18.** The context-bound environment stalled forever at the f5 Active::enter callback.
