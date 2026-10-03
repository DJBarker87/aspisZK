# R485 selected shared-read syntax binding

R485 compiled successfully in the pinned Lean 4.32 cached workspace. Its promoted source is byte-for-byte identical to the successful run snapshot. Compilation source revision: `4b8b9f6aaff2418806c0053c5d84371b4ec01442` (`research/v8-r64-guarded-m31-20260929`). Target source SHA-256: `c2a28d4554b2da8e434405f5ada6b054e6e6e9ecb8ed1776023696a732a39df2`.

## Proved boundary

The typed syntax projection selects the pinned Fun70 statement 10438 assignment and Fun112 statement 11909 assignment: the shared reference from dereferenced local 21 assigned to local 20, and the copy from dereferenced local 4 assigned to local 9. In Lean, only assignments with the specified type identifiers, reference kind, unit metadata, dereference places, and copy flag decode to those commands. The selected commands execute in R483's proposed checked reference fragment. R485 proves that every decoded or unsupported execution preserves the fragment's heap, liveness, and readability fields. Under explicit heap lookup, alive/readable permission, in-bounds initialized-cell, and local-binding premises, it proves the selected acquire or copy result.

The external fail-closed checker `evidence/r485-selected-shared-read/extract.py` passed with exit 0. It checks the full nested assignment trees against exact function/statement IDs in the frozen R440 AST, and checks the Lean literals against those selected trees. The frozen input is `R440GammaExecutionSelection.llbc`, SHA-256 `96135e91c71f93dcd3aeec7b693eb737e7cf05027456ca973242cf2586088c48`. Its manifest retains the statement-node hashes and exact selected-node file hash. This is an external exact association, not a kernel-checked JSON theorem. R485 does not prove native Rust semantic adequacy, or derive the actual caller's heap image, permissions, lifetime, aliasing, local values, or call binding. This is a model-level syntax binding with a conditional initialized-cell result; it does not close native source memory behavior, privacy, or end-to-end security.

## Compilation record

Exact target: `AspisV8R19/R485SelectedSharedRead.lean`. The target compiled with `lake env lean -j1 -M4500` in the pinned cached workspace under `systemd-run --user --wait --collect --pipe`, with `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`. Successful run `1791039196798100000` exited 0 in 1.62 s, with GNU time Lean-child peak RSS 3,729,072 KiB and swap 0.

## Complete `#print axioms` output

```text
'AspisV8R19.R485SelectedSharedRead.decode' depends on axioms: [propext]
'AspisV8R19.R485SelectedSharedRead.execute' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R485SelectedSharedRead.decode_selectedAcquire' depends on axioms: [propext]
'AspisV8R19.R485SelectedSharedRead.decode_selectedCopy' depends on axioms: [propext]
'AspisV8R19.R485SelectedSharedRead.execute_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R485SelectedSharedRead.selectedAcquire_backed' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R485SelectedSharedRead.selectedCopy_backed' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The exact Lean source snapshot, receipt, complete log, checker, selected AST nodes, and checker manifest are preserved in `evidence/r485-selected-shared-read/`. The remaining native-source obligation is to establish semantic adequacy and derive the actual caller's memory image, read permissions, lifetime, and local/call bindings from source execution.
