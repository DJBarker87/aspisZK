# Candidate 2: opt-in diagnostic profiling

The observer replacement is source-factorized equivalent under the existing
sufficient-reference-resource and SDK diagnostic-projection boundary. It covers
**10,992 stage-1 CU + 13,201 settlement CU = 24,193 CU** of retained measured
savings. Production Rust is unchanged; no new CU replay is attributed to this
formal-only change.

The comparison is candidate `190e1779c3b9530047e4d2dfcdf0022b200d6c35` against
its exact parent `0330ae7300b3df6602600a727dfd1b969bfbe19a`.
Selected production features are `pool-adapter,private-leaf-salts`; profiling,
detail phases and prover are disabled. The frozen production revision is
`39c2971dd16c95858a4cfd2c9ae35da052eacfa9`.

## Checked composition

- The unchanged original `Phase`, `Observer` dispatch and complete `mark` body
  are emitted by the existing arrow-capable Charon/Aeneas reference pipeline.
  Installed Lean Types/Funs are byte-identical to the raw emission.
- The exact dispatcher instantiated with the fixed projected program callback
  equals the literal-None dispatcher. Six smallest-target Lean checks passed,
  ending in `CuSavingsProfilingCandidate2.complete_source_context_eq` and
  `all_observations_eq`. No candidate-equivalence premise is supplied.
- The source audit enumerates all 12 observer-owning definitions, covers every
  `obs` variable occurrence, and verifies that it is used only for dispatch or
  internal forwarding. The semantic marker compiles to a no-op with these
  features. Eta-lifting `mark obs` factors this recursive closure over a single
  dispatcher; every other verifier/semantic function, loop, return, error and
  hash body remains byte-identical. The audit reverses the factoring exactly.
- The entire original candidate diff reverses byte-for-byte: the selector and
  feature declaration, three observer expressions, and the two exact adapter
  diagnostic blocks. Application events, error logs, validation, account-data
  copies, `set_return_data`, and `emit_result` are retained.
- The fixed program callback has all eleven phase arms matched byte-for-byte
  against parent, candidate and frozen production source. It emits its exact
  phase message and a CU report. Explicit diagnostic-event projection erases
  these effects and the two adapter diagnostics while preserving arbitrary
  surrounding application events. Common contexts may fail or diverge; they
  need not succeed.

This is **source factoring plus universal checked source-context substitution**,
not direct whole-Solana-program Aeneas emission and not a second Rust
interpreter. Source-layout/factoring and the standard SDK runtime contract are
explicit admission boundaries. The result is stronger than a generic observer
lemma alone: its fixed callback, full transitive source use closure, complete
candidate delta and adapter effects are bound by the inverse source audit.

## Runtime and resource boundary

Equality applies with sufficient **reference** compute, stack and heap, and
returning standard SDK diagnostic syscalls. It does not turn reference heap
exhaustion, panic, a failed syscall or out-of-compute execution into success.

The pinned SDK `msg!` macro formats four phase arms using `format!`, so
formatting allocates. The pinned Solana bump allocator does not free those
buffers. The callback receives only a phase value; formatter buffers do not
escape the diagnostic borrow into the syscall or the callback's Unit return.
Under the standard runtime contract these private allocations/logs do not
modify application state. Heap addresses/cursor are not protocol observations.

`private_allocations_admitted` proves that the **actual allocation request
trace**, including growth allocations, succeeds when
`sum(request sizes) + future reference budget ≤ free heap`, and leaves that
future budget intact. Erasing those private requests leaves at least as much
free heap. Byte-buffer alignment is one, matching the pinned bump subtraction;
we do not substitute message lengths for allocator capacities. On the 64-bit
ABI the largest callback payload is 38 bytes (the detail-only query-part arm);
this is a payload bound, not an allocation-capacity proof.

The standard SDK formatting, allocation and logging contract remains trusted
runtime behavior; the new Lean theorems do not claim a kernel proof of the
complete SDK or compiled program. The existing reference resource admission
must satisfy the actual formatting-request budget. No whole combined
soundness/privacy transfer is asserted here.

## Evidence

`PROFILING-CANDIDATE2-FINAL.json` selects six successful Lean receipts with
exact commands, source revision/hash, features, exits, wall times, RSS, swap,
axiom output, direct import hashes and cache provenance. Each selected target
used about 2.46 GiB RSS, 1.60–1.80 seconds and zero process swaps. Some focused
targets overlapped other small Lean jobs under the user's parallel-work
instruction; their foreign process IDs are retained and no exclusive-host
measurement is claimed. Axioms are only `propext` and `Quot.sound` where used;
the original dispatcher and local substitution lemmas are axiom-free.

`PROFILING-CANDIDATE2-DECLARATION-REPIN.json` inventories all six changed/new
program owners and distinguishes contextual source bindings from directly
emitted declarations. No nonexistent whole-program extraction is listed.

Run:

```sh
python3 docs/research/100bit-spend-path-20261013/tools/cu-equivalence-20261019/check-profiling-candidate2.py
```

The failed no-branch-join arrow emission and first local nil-case proof are
retained as excluded diagnostics. The existing pinned arrow-capable producer
succeeded without compiler changes. No unchanged SBF/codec/injection/CU suite
was repeated, and no ELF, shared object or compiled Lean object is committed.

Unified-import normalization: the generated Phase discriminant instance now has a qualified registration name with identical constructors and ordinals. emit-profiling-source.py inversely audits that mechanical change; raw Funs is unchanged. The six affected targets were refreshed as profiling-{types,funs,marker,projection,resources,candidate2}-qualified-a. All exit0, about1.604seconds each, zero process/cgroup swap, only previously reported standard axioms. The final JSON selects these coherent receipts. No proof statement or Rust body changed.
