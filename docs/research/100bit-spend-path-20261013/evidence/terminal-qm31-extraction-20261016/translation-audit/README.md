# Terminal QM31 translation audit (16 Oct 2026)

This package audits the successful name-adapted Aeneas translation in `../attempt-g-name-adapt/`. It records translation structure and candidate declaration reuse only. It contains no Lean compilation, source proof, production-source equivalence, or semantic claim about opaque external functions.

The input is the original F LLBC plus a checked metadata-only alpha-renaming of function declaration ID 236. `verify_adapter.py` proves the JSON changes at exactly `translated.fun_decls[236].item_meta.attr_info.rename`; IDs, references, signatures, bodies, source spans, item names, and ordered declarations remain as in F. Generated output hashes are in `audit.json` and the parent attempt checksums.

The generated translation contains 221 function records (201 local, 20 opaque external) and 59 type records. An earlier 151-record/14-opaque count came from a direct generated-body identifier-reference scan rooted at `Public.terminal_qm31`. It is retained only as a provisional scan result in `reachable-callgraph.json`. That scan does not establish the complete closure through all trait dictionaries, callback instances, or opaque callee implementations. Therefore none of the 20 opaque declarations is classified as unreachable; all 221 function records and all 59 type records remain in the conservative translation inventory.

All 20 external declarations are emitted as axioms in `FunsExternal_Template.lean`; the single external type (`core.array.iter.IntoIter`) is an axiom in `TypesExternal_Template.lean`. These are placeholders, not specifications. Before any theorem relies on behavior, the relevant external operation must have a checked compatible model or a separate verified bridge. Related Std iterator models do not discharge that obligation by name similarity.

## Reuse and smallest focused targets

The generated terminal translation uses namespace `AspisR1SelectedMaskProbe`, matching the selected-mask extraction. A normalized full-declaration comparison found 23 overlapping function declarations with identical generated bodies, including M31/CM31/QM31 operations and `PreparedQm31Multiplier.new/mul`; six generated types also match structurally. The raw files and exact lists are retained in `shared-mask-declarations.json` and `shared-mask-types.json`. This supports declaration-level reuse after the identity manifest is checked. It does not by itself validate any imported external behavior.

The first narrowly useful target is the generated `external_linear_lazy_row` closure slice: its body calls concrete Aeneas array indexing, U32-to-U64 widening, and checked U64 add/multiply operations, and returns the closure state. The generated closure instance and all referenced types must be included. This target does not depend on the opaque `array::from_fn` or `[T; N]::map` declarations. A subsequent `external_linear_lazy` target has broader callback/range structure and needs its complete generated declaration-reference closure plus checked models for operations it actually uses. Do not infer that closure from the old direct-body count.

For a larger terminal compile, use a dependency-ordered split: (1) canonical shared selected-mask Types/Funs, after checking the overlap manifests; (2) terminal-only Types and callback/trait declarations, retaining every required constructor and external type; (3) checked Std/model adapters for each external declaration used by the selected focused target; then (4) terminal-only Funs. The complete raw `Types.lean`, `Funs.lean`, and external templates remain preserved. No declaration should be removed based on the provisional 151/14 scan.

## Existing compatible model evidence

Two useful retained models were found:

- `AspisV8R19.TraversalRuntime` defines an `Array.map` model, with `TraversalLaws.array_four` and `array_empty` giving concrete finite-array laws. This is a separate retained model; check its exact types and namespace adaptation before reuse. Its header limits the claim: specialized iterator/fold behavior still needs a call-site proof.
- `AspisR72Sampler.Funs` contains a concrete `Result.map_err` model with ordinary result matching and closure invocation. This is a retained generated model, not proof that every `Result.map_err` usage in this translation is already connected.

The searched Std sources contain related iterator and scalar definitions, but this audit did not find exact executable models for the generated `from_fn`, owned-array IntoIter operations, integer bit intrinsics, Range clone, `Option.is_some_and`, `Result.map`, or the relevant iterator-fold declarations. This is a bounded source search, not proof that no model exists elsewhere.

## Attempt and resource records

The audit index retains attempts A–F and successful Aeneas-only G. Their inputs, logs, receipts, and source snapshots remain in sibling `attempt-*` directories. G's LLBC alpha-renaming adapter, command, and tool pins are recorded in its `input` and `receipts` directories.

G completed in 8.78 seconds with 317,524 KiB peak process RSS and zero swap in a 4 GiB `MemoryHigh`, 6 GiB `MemoryMax`, zero-swap, 128-task scope. The transient cgroup `memory.peak` file was unavailable after cleanup, so the record reports measured process RSS only.

## Publication review notes

The tar archive is immutable. Its archived README contains a direction typo: the row callback widens U32 inputs to U64, as corrected in this outer README. The archive includes all sibling attempt paths needed to inspect or extract the retained inputs; those paths need not be separately checked out.

A later static inventory identified three additional matching declarations beyond the archived 23-item list: `field.P` and the two PreparedQm31Multiplier closure-call definitions. This makes 26 candidate function overlaps. The deterministic split and its raw-to-active-source comparison remain under review; the archived inventory is retained as a subset, not treated as a complete compiled reuse result.
