# R418 binder substitution API inventory

Read-only source and LLBC inventory for the proposed constrained `B → Try::Output` substitution. This bundle does not edit LLBC, run Charon/Aeneas/Lean, implement a transform, or decide whether the transformation is semantically acceptable.

The decisive API facts are recorded in `inventory.json` and `source-excerpts.txt`. Charon supplies capture-avoiding substitution through `TyVisitable`/`SubstVisitor` and whole-function `FunDecl::substitute_params`, but the inspected source has no general operation that removes/reindexes an arbitrary function type parameter and rewrites every declaration/reference. Its allocator-removal visitor is narrow to known ADT references and substitutes an error type. The associated-type expander resolves known projection replacements and walks `FunDeclRef`, normal function pointers and trait function pointers, but its generic-reference update path appends missing type arguments; it is not a general binder-slot-removal pass.

The decoded R396 census preserves all three function binders with the `Try::Output = free type variable` constraint: Fun58 `Iterator::try_fold`, Fun120 `Chain::try_fold`, and Fun169 `Rev::try_fold`. It records five `FunDeclRef` nodes across these functions: the Iterator default and two implementation refs to Fun58 (five type arguments each), one Chain implementation ref to Fun120 (six), and one Rev implementation ref to Fun169 (five).

The Iterator trait method36 binder itself has `B`, `F`, and `R` and the same `Try::Output = B` constraint. All four Iterator trait-impl method36 binders likewise have three type parameters and one constraint; exact rows and their referenced function IDs are retained in the JSON. Four call sites dispatch through the trait method id and carry three method type args, separately from the trait refs. Thus the reference forms and their arities differ; the saved census does not conflate them.

Aeneas translates generic trait-type constraints to `predicates`, but the pinned function-signature translator asserts the signature's trait-type-constraint list is empty and then initializes instantiated-signature constraints to `[]`. Trait method translation first routes through this function-signature path. Therefore the inspected Aeneas layer does not demonstrate first-class preservation of this equality as an assumption in translated function bodies/signatures.

`build_r418_inventory.py` regenerates the decoded reference census from the immutable saved R396 LLBC. `write_excerpts.py` regenerates line-numbered source excerpts from the copied, hash-pinned source files. `source-manifest.json` records upstream source identities and the R396 input hash.

The pinned Charon host inspection is in `remote-workspace/report.json`, with exact copied source hashes in `remote-workspace/pinned-charon-source/file-manifest.json` and relevant numbered source in `remote-workspace/workspace-source-excerpts.txt`. It confirms the existing release workspace/cache location and shows a public serialized-AST load/save API (`CrateData`) separate from compiler-time `--start-from`. The regular Charon transform pass runner is called after rustc translation and before serialization; the `ui-test` command is an input Rust fixture harness, not a saved-LLBC transform test command. This was read-only inventory: no cache build or new binary was attempted.

## Boundaries

- No source or premise change is authorized by this inventory.
- No claim is made that the proposed reverse substitution is implemented correctly or should be used.
- The four trait dispatch call sites use method id 36 with three method type args; the function-reference entries carry their own varying type-argument arities (five, six, five for the constrained functions' implementations, plus the default/impl refs to Fun58).
- The census is qualified to the decoded R396 structure and must be independently inspected before any transformation.
