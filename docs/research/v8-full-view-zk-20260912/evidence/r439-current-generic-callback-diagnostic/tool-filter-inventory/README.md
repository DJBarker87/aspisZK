# Aeneas per-function filtering preflight (R439)

This is a read-only source inspection of the pinned Aeneas candidate used for the R438 LLBC. It answers whether the normal frontend offers a supported way to translate only the selected FnMut closure (R438 Fun284) and its dependencies while retaining the generated borrowed-return shape.

## Result

The inspected CLI has no per-function/declaration include or exclude option. It reads one LLBC file, runs the normal prepasses, and translates the declaration closure encoded in that LLBC. `-print-unknown-externals` and `-mark-ids` are diagnostics/debugging options, not extraction filters. The `gen_config` booleans select output categories (types/functions/traits/globals and opaque/transparent functions); they do not select an individual declaration ID.

The frontend computes its translation contexts from `crate.declarations`. It gathers IDs in the declaration groups, filters declaration maps to those IDs, then analyzes type declarations and function information. `translate_crate_to_pure` translates all selected type declarations before globals, signatures, and function bodies. Consequently, an unrelated problematic type that remains in the R438 declaration groups may still be processed before the selected function body. This inspection does not identify a particular R438 type as the cause of a raw-pointer or Pattern error; it establishes the phase ordering and the absence of a supported per-function CLI selector.

No AST pruning, translation, compilation, or semantic/proof conclusion was performed. Filtering declaration rows by hand would change the input and is outside this inventory.

## Source pins and relevant locations

All source files below were copied from `/home/dombarker/project-offloads/aspis-r425-unit-constant-candidate-20261002-a/src`, the R425 candidate source tree recorded in the R437 pointer API inventory. That inventory records campaign source revision `ee7ba72da456d5f353bca9f6739b23750a5dfffa` and Aeneas executable SHA256 `eadb205fc1e00cf7e32197dd7cbbbd82aa42b59442d8f186cfdca7c8fdca9b01`. The source tree itself is not a Git checkout, so the revision is cited as the existing campaign provenance, not independently read from that tree.

- `Main.ml`: CLI option table at lines 76–260; input argument parsing at 263–266; ordinary prepasses and translation call at 733–744.
- `interp/Interp.ml`: `compute_contexts` at 52–245. Declaration-group ID collection and selection are at 108–177; type analysis is called at 149; trait-method closure is collected at 179–235.
- `Translate.ml`: context construction and eager selected-type translation at 317–331; selected globals at 334–369; all selected function signatures at 371–431; all selected function bodies at 444–452; category/output flags at 623–650.
- `symbolic/SymbolicToPure.ml`: selected type-declaration translation at 132–151.
- `llbc/Contexts.ml`: supporting LLBC context structures and declaration-group splitting definitions; see saved full file.

The source-level type/global ordering described above is not a claim about Rust execution or whether the R438 closure can be proved independently. The captured R438 input remains at `.r21-scratch/r438-fnmut-source-selection/root-launch-a/saved-output/R438GenericClosureDispatch.llbc` (SHA256 `76eefed780e23eb3243413b913e935dc7a9b661bceeb0fc0346668621ab07fb6`).
