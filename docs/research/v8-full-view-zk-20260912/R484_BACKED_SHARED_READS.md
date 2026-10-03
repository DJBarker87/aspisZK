# R484 backed shared-read proofs

R484 compiled successfully in the pinned Lean 4.32 cached workspace. The promoted source matches its successful run snapshot byte for byte. Compilation source revision: `95d940b0d08adaee737a2394d3d49a258f39e18a` (`research/v8-r64-guarded-m31-20260929`). Target source SHA-256: `7f7445661508ccb8f89cecd549728f8a03366db4327c66a4a77b1c48b2c32610`.

## Proved boundary

Under explicit premises that an allocation is present in the modeled heap, marked live and readable, the selected cell index is in bounds, and the relevant local contains the modeled pointer or reference, R484 proves acquisition of a shared reference and copying its initialized packed bitcell as the decoded QM31 value. It proves the corresponding reference and copy statements update their destination local as specified, and all other locals remain unchanged under `put`. It also proves that an acquired reference copies the same cell after the destination-local update without adding a second successful-read premise.

The heap lookup, liveness, read permission, bounds, and local-binding premises are not established from the actual Rust caller. R484 does not prove native source memory/reference semantics, lifetime or aliasing validity, the callback fold, privacy, or end-to-end security.

## Compilation record

Exact target: `AspisV8R19/R484BackedSharedReads.lean`. Command was `lake env lean -j1 -M4500` in the pinned cached workspace, under `systemd-run --user --wait --collect --pipe` with `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`. Peak RSS below is GNU time's Lean-child RSS in KiB.

- Successful run `1791038967477202000`: exit 0; wall 1.58 s; peak RSS 3,717,860 KiB; swap 0.
- Failed predecessor `1791038938516441000`: exit 1; wall 1.48 s; peak RSS 3,703,912 KiB; swap 0. The failure was an unsolved acquisition goal after rewriting the backed pointer; the axiom report contained `sorryAx`. The successful run's complete axiom output below contains no `sorryAx`.

## Complete `#print axioms` output

```text
'AspisV8R19.R484BackedSharedReads.cellPointer' depends on axioms: [propext]
'AspisV8R19.R484BackedSharedReads.cellReference' depends on axioms: [propext]
'AspisV8R19.R484BackedSharedReads.acquire_backed' depends on axioms: [propext, Quot.sound]
'AspisV8R19.R484BackedSharedReads.copy_backed' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R484BackedSharedReads.ref_statement_backed' depends on axioms: [propext, Quot.sound]
'AspisV8R19.R484BackedSharedReads.copy_statement_backed' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R484BackedSharedReads.put_other_local' depends on axioms: [propext]
'AspisV8R19.R484BackedSharedReads.acquired_copy_after_put' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Evidence files

`evidence/r484-backed-shared-reads/` preserves exact source snapshots, receipts, and complete logs for the successful run and failed predecessor. `SHA256SUMS.txt` covers those files, this report, and the promoted Lean target. The first remaining proposition is to derive the caller's heap image, initialization, liveness/read permissions, bounds, and local bindings from actual Rust/Aeneas source semantics.
