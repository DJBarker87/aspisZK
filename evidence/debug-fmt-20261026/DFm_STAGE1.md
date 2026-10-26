# Debug formatter removal candidate — stage 1

Evidence-only preparation for L188. Research, generated source owners, shipped
Rust and session A files remain untouched. No release or premise removal claimed.

Selected inputs are the exact two source variants from RPz2_source-plan.json.
DFm_inventory.json pins both original and filtered copies, the two explicit
source declarations per module and the retained 37 nonstandard axiom names.
DFm_remove-debug.patch deletes only their adjacent generated declaration blocks.
DFm_regenerated contains filtered copies, not a fresh Aeneas extraction.
Everything outside those blocks is byte-for-byte unchanged.

Source provenance: both retained extraction crates' source/lib.rs line 131 has
`#[derive(Clone, Copy, Debug, PartialEq, Eq)]` on r1_wire::Error. Generated
comments identify that derive's core::fmt::Debug::fmt and trait implementation.
No FunsExternal file is imported by either Funs file: the Formatter placeholder
is supplied by imported Aeneas. Native-decide axioms are auxiliary constants
created when elaborating formatting string literals; they are not explicit
`axiom` lines in these generated sources. Removing the formatter consumer does
not remove Formatter from the trusted library environment.

Planned validation: isolated DFm_ overlay in the coherent SInt2 host workspace,
unchanged launcher, one admitted capped scope at a time, -j1 -M7000. Compile the
two filtered modules first, then audit original/filtered declaration expressions,
compile all six direct importers and selected transitive importers. Use at most
40 Lean attempts and no Kani. Full 1,487-transitive-importer replay cannot fit
this budget; no claim of that replay will be made. RPz3 owns top reachability.

Extraction proposal: exclude the derived Debug impl at the extraction boundary,
while retaining Error's enum, Clone/Copy/PartialEq/Eq and all parser bodies.
Prefer an extractor reachability root set limited to parser entry points and
required types, with a negative Debug-impl selection rule. Do not make Debug
opaque (that preserves another external). Exact supported exclusion syntax and
an end-to-end re-extraction remain to be checked against the pinned Charon.
Add a generator check rejecting CoreFmtDebug and formatter-specific helper
constants in these two outputs; compare all remaining elaborated declarations.
No production derive or extraction configuration is edited by this proposal.

Latest committed top on this branch is Rc8_Top.deployed. Before and after are
identical (zero source edits): premises removed/added/changed 0/0/0; ledger
T83/P18/G13/C0 unchanged; deployment-inclusive T89/P22/G13/C0 unchanged.
No quantifier, carrier, event, conclusion, assumption, trust item or metric changes.
No joint premise inhabitant is constructed by deleting unused declarations;
existing conditional non-vacuity remains conditional. Target not yet established.
