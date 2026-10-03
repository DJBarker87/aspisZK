# R433 actual slice iterator constructor fragment

This scratch bundle contains a strict command table for the complete R431 `core::slice::iter::Iter::new` body (`fun_decls[86]`) and a structural comparison of the selected R429/R431 sized-type-property constant graph. It is an AST inventory only: it performs no operation lowering, readonly evaluation, Lean proof, or Rust/source correspondence claim.

The source LLBC input is `.r21-scratch/r431-actual-slice-construction/root-launch-a/saved-output/R431ActualSliceConstruction.llbc`, SHA-256 `df9180ee7c9959a7840d6edac0b756f007ef33ed0bd88bb36faf57a3e18f2358`. The constructor table preserves all 28 original top-level statements and both arms of its `IS_ZST` switch (8 branch statements, 36 statement nodes counting those arms). The entire raw function row and original top-level statement array are preserved beside the descriptor table. Generation fails closed for any unrecognized top-level statement, assignment rvalue opcode, or If-switch shape.

Each descriptor keeps the native statement ID and span, statement opcode, local storage index/type, assignment destination and root-local alias, exact rvalue node/opcode, local/global operand references, and resolved type graph. Charon `HashConsedValue` definitions are collected from this capture and every referenced `Deduplicated` type is recursively expanded; the raw type nodes and wrappers remain recorded too. Cast/transmute/pointer metadata, raw-pointer operations, aggregates, the global `IS_ZST` condition and all storage statements remain in the original AST and the command table. The table does not reduce the branch or rewrite an opcode.

The graph comparator checks exactly these rows:

- R429 functions 142, 145, 153 mapped to R431 functions 143, 146, 154 (`IS_ZST`, `SIZE`, `size_of` respectively).
- R429/R431 global rows 31 and 32 (`IS_ZST` and `SIZE`).

The comparator resolves each capture's hash-cons wrappers using that capture's own unique definitions, maps only the explicitly listed function-row IDs and `Fun.Regular` references, and then compares the resulting rows structurally. It ignores only `span`, `generated_from_span`, and statement-node `id` metadata. Other identifiers and all content compare exactly. Result: the normalized selected rows are equal; zero structural differences remain after those explicit operations. This is a finite row comparison, not a theorem about constants or source behavior.

Run both scripts from the worktree root. `build_constructor_table.py` regenerates the row/table files; `compare_constant_graphs.py` regenerates the graph comparison. Input paths and SHA-256 values are embedded in the outputs. `SHA256SUMS` covers all files in this bundle except itself.

The current lead-owned `R433ConstructorFragment.UNVERIFIED.lean` draft was read without modification. `model-command-binding.json` records its SHA-256 and provides a row-by-row structural alignment for all 28 native top-level statement positions and all 8 statements nested under the two preserved switch arms. The mapping treats the input argument local as the initial state and retains its explicit final `StorageDead(1)` statement. This alignment is syntax/shape bookkeeping only; it does not validate the draft's operation meanings or prove execution correspondence.

During preparation, a checksum glob was run before I discovered that lead-owned compile artifacts had appeared concurrently at this directory's root. That command rewrote the root-level `SHA256SUMS` using a mixed file set. Per lead direction, treat that root-level index as superseded/untrusted; it must not be used for publication. My complete inventory is isolated in this `inventory/` subdirectory and has its own physical `FILES.json` and `SHA256SUMS`. The lead-owned Lean draft, attempt logs, and receipts were not modified.

Run the three scripts from the worktree root: `.r21-scratch/r433-actual-constructor-fragment/inventory/build_constructor_table.py`, `compare_constant_graphs.py`, and `build_model_binding.py`. They write only to this `inventory/` directory.

## Strict model-binding verification

`model-command-binding.json` is retained as the original bounded row index. `verify_model_binding.py` adds the requested fail-closed checks without editing or compiling the Lean draft. It gates the draft SHA-256 to `816ea0b20355bcd23d06b0831841db279a08caa78cc59819abfebbb1fc04e2ef`, parses the `constructor86` source block into exactly four command lists (18-command prefix, one then command, seven else commands, nine-command tail), and checks each native statement's opcode/storage local and the source-model sequence.

It separately verifies the native metadata read, shared raw slice-pointer construction, all seven cast assignments with explicit source/destination locals, cast opcode and resolved type endpoints, the `Global31` branch, offset operands/types, zero-operand marker ADT 59, and iterator ADT 42 aggregate operands/types. These checks compare AST structure with the existing draft's constructor names and data flow only. `model-binding-verification.json` records the exact source/table hashes and checks performed. It does not validate primitive ABI or pointer/lifetime/heap semantics, and no Lean compiler was run by this worker.
