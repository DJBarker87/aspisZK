# Coherent repository replay findings

L187 remains open; target not yet established. This file is completed from
receipts at the end of the run. The process reuses only the explicitly trusted
Lean/library caches, never historical repository objects in place of a failed
or unresolved source module. No existing proof or shipped source is modified.

## Retained failures

- `RPz_001`, `ImportUnionNamedDiscriminant`: missing `AeneasMeta` trusted
  library prefix during the initial library-cache preflight. The library
  selection was subsequently amended and pinned; this module was not rerun.
  Its dependent repository modules remain blocked in this replay.
- `RPz_247`, `R1NaturalProjection`: source elaboration fails at lines 28 and
  58 with unsolved goals. The `sorryAx` printed after these errors is Lean's
  failed-elaboration diagnostic, not an accepted declaration or a release
  result. The module is not retried or repaired; its dependents are blocked.

No theorem repair, new security premise, source adoption, or metric change is
made to hide these failures. All attempts and their diagnostics are retained.

## Source provenance and unchanged statements

The actual committed-source import traversal selects 4,141 repository modules
and records 108 unresolved source selections. That is a partial source graph,
not a claim that no missing source has additional imports. Exact source choices,
imports, hashes, unresolved names and candidate paths are in
`RPz_source-plan.json`. Nine unresolved candidate files were found read-only at
the retained immutable candidate revision, matching their historical source
pins (`RPz_source-recovery.json`); they are not silently substituted into this
in-flight replay.

`RPz_before-after.md` contains the identical before/after top statement.
`RPz_statement-pins.json` gives its source hash. Ledger-method delta is
T 0 / P 0 / G 0 / C 0; premises removed/added/changed 0/0/0. Historical
conditional non-vacuity is retained unchanged, not freshly promoted to a joint
witness for all top premises.

## Trusted base

`RPz_trusted-base.json` pins Lean 4.32.0 (commit
8c9756b28d64dab099da31a4c09229a9e6a2ef35), Mathlib
81a5d257c8e410db227a6665ed08f64fea08e997 and the library cache hashes.
`RPz_library-provenance.json` distinguishes 234 exact matches to the historical
Aeneas port receipts from the selected Fmt repair and the differing ArraySlice
object. The exact cache artifact pins are authoritative for this run; a source
version is attributed only where the retained object hashes match.

No Rust/Kani/SBF/ELF or key changes; no ELF rebuild trigger. Inherited ELF pins
are historical, not newly reproduced: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4,
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299,
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

## Audit interpretation

The explicit audit enumerates imported repository declarations by their owning
module and issues both Lean's `collectAxioms` API and `#print axioms`. On pinned
Lean 4.32 this uses axiom dependencies computed when each fresh object was
exported; collection includes constants in a declaration's type and body.
This is declaration dependency evidence, not a source-text grep. Separately,
actual imported module headers and axiom declarations identify nonstandard
axioms merely present in each audited module's import closure. Importing Lean
for the audit itself does not add Lean to the recorded source module's direct
imports. These two lists must not be conflated.

Because Rc7_Top is blocked before compilation, this audit cannot establish
which nonstandard axioms are reachable from its proof term. It likewise cannot
establish a definitive set of FunsExternal axioms reached by that top or map a
purported empty set to Rust externals. Those two requested results remain
unknown, not verified empty. Historical cached headline audits do not fill the
fresh-object gap.

## Audit preflight correction and artifact stability

RPz_530 (RPz_Audit001) failed before any query: the unannotated mutable
counter was inferred as MessageData. Its source and diagnostics are retained.
The corrected template gives the counter explicit type Nat. New, uniquely
named audit modules RPz_Audit531 onward repartition all 527 successful replay
modules across the remaining 70 attempts. RPz_530 is not rerun or counted as
an audit. This is an audit-source type correction, not a proof change.

The read-only post-source-replay inventory checked 22,637 pinned trusted-base
artifacts with zero changed or missing artifacts. `RPz_final-object-inventory.json`
records their manifest hash and all 542 fresh repository object/sidecar file
hashes and sizes. The workspace has no default `.lake/build/lib/lean` directory;
only the explicit RPz object and trusted-library paths are selected. This is
artifact identity/stability evidence, not independent source reproduction of
the owner-approved trusted base.
