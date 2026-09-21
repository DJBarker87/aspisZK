# Focused actual-source mask extraction

This dependency-free crate wires unchanged `field.rs` and
`r17_structured_g.rs` files into an extraction-only library. It does not alter
production code or replace loops with a synthetic trace. `corelib` is only a
module alias needed by the research source. Source pins are enforced by run.sh.
Extraction excludes `cfg(test)` bodies; no runtime arithmetic test is claimed.

Run run.sh with a directory containing the two pinned files and a fresh output
directory, inside a Linux scope with MemoryHigh=4G, MemoryMax=6G,
MemorySwapMax=0, TasksMax=128. The script uses the cached pinned Charon tool,
Rust nightly-2026-06-01, one job, offline/locked release compilation.
Record the LLBC hash, then pass it to translate.sh with a fresh output path in
an equivalently bounded scope. Neither script overwrites existing outputs.

The first actual-source translation succeeded but is NOT a compiled theorem.
It emitted external placeholders for Iterator.map.default and Map.next, and
warnings concerning map/zip/collect/rev runtime trait information. Do not copy
FunsExternal_Template.lean into FunsExternal.lean or accept its axioms. Supply
justified runtime models first, then compile the smallest dependency and caller.
The translated field types are in a fresh namespace; their relation to the
previous arithmetic projection must be checked, not inferred from names.

Pinned evidence, command results and the remaining obligations are recorded in
../../R16_SOUNDNESS_OBLIGATIONS.md. Raw extraction artifacts remain in the
task-owned Linux workspace identified there, outside accepted Lean targets.
