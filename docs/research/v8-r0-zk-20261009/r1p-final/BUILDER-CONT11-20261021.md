# Builder continuation 11

Branch `codex/cx-builder-ref11-20261021`, base `4715dbaf3`.

## Scope

Repair the forest callback state ABI, then attempt semantic admission and the
destructor pointer/iterator correspondence. RuntimeJoin and checker/retry
coupling remain named execution joins. No concurrent-worker file is edited.

Only J9396–J9399 remain unused in the assigned attempt range. Earlier attempts
9200–9395 have host receipts and will not be reused.

## Stage 1: callback adapter

`BuilderForestCallbackAdapter` proves state/pair round trips, successful
borrow-back application, captured-index restoration and tuple-call adaptation.
The returned callback is `back next`, never the original environment. This
supplies a generic checked adapter; it does not yet certify the aggregate
forest or its source identification. J9396: exit 0, wall 1.17 s, peak RSS
2,532,764 KiB, swap 0. Five axiom audits: three use only `propext`, two none.
Exact source revision/hash, dependency fingerprint and logs are retained in
`builder-cont11-attempts.jsonl`.

## Stage 2: aggregate forest ABI port

`BuilderForestAdmissionPort` compiles the complete 6,000-line dependency cone
through `compile_forest_from_copies`, with all 24 std declarations supplied by
CONT10's models. Generated borrow-back callback functions are retained under
`_borrow` names, and their ABI wrappers use the proved `borrowToPair` adapter.
Unit-valued owned callback wrappers use `stateToPair`. The nullifier callback
is uncurried without selecting an output. A threaded permutation variant
returns its final callback environment through the final round loop; the owned
API discards that environment only after the rounds. This is a repaired
reference model, not a new shipped=reference solver certificate.

Three excluded source declarations (`external_linear_lazy`, `records`, Drop)
are represented by explicit typeclass instance parameters. They are neither
axioms nor chosen implementations. Their successful source/refinement handoff
is still required. The raw generated borrow functions are kept for audit;
the generator's deterministic `--check` pins the entire transformation.

J9397 failed on four remaining shift-count ABI sites. The corrected source
J9398 passes: exit 0, wall 8.77 s, peak RSS 2,873,736 KiB, swap 0. Six complete
axiom audits cover the threaded permutation, sponge, nullifier, tree validator,
Parts and full helper; all use only propext, Classical.choice and Quot.sound.
No pre-existing shared source/object is replaced: all module names are new.

### Admission boundary identified by inspection

The raw extraction ends at the internal `compile_forest_from_copies` helper.
It does **not** include the two public compiler entry points. The shipped
entry points in `pair_forest_trace.rs` additionally check public validity,
`validate_common`, snapshot pool/domain binding, positive bounded output
values and checked conservation before calling the helper. CONT10's validator
checks frontier/root consistency, not those entry-point conditions. Parts
content does not imply these checks either. Therefore successful helper
execution is not yet a complete semantic admission certificate. No
`RspendPlus` conclusion or source-instance inhabitant is inferred from the
mere compilation of this port.

## Stage 3: successful helper and destructor cursors

`BuilderForestAdmissionProgress.compile_selected` uses successful execution
of the compiled aggregate helper to obtain its actual successful record
constructor, selected commitment, input leaf and false mismatch comparison.
The record function and external linear layer remain explicit source-function
parameters. This is a checked consequence of the actual helper control flow,
not the full RspendPlus admission statement.

`runPointer` models one column's four-byte cursor advance. `pointer_frame`
proves its byte frame at arbitrary length by induction, using only the
existing one-word store contract. `pointer_fields_frame` and
`pointer_fields_observation` compose arbitrary column lists and preserve all
retained output outside their buffers. No list of concrete recurrence cells
or large numeral is reduced. J9399 passes: exit 0, wall 1.86 s, peak RSS
4,026,244 KiB, zero swaps; all four audits use only allowed standard axioms.

Two new reference-only Kani harnesses check actual std cursor behavior:

- `trace_drop_iterator_step`: every suffix of a 1024-word M31 column. Actual
  `IterMut::next` returns the exact first pointer, advances by one M31 and
  decrements remaining length; the identical volatile write expression sets
  that word to zero. 144 checks, three unreachable; exit 0, wall 11.253 s,
  peak RSS 529,080 KiB, swap 0.
- `trace_drop_outer_iterator_step`: actual `IntoIterator` for
  `&mut [Vec<M31>;16]`, followed by `nth(skip)` at every skip 0..=16. It checks
  the exact column pointer and residual iterator pointer/length. 267 checks,
  four unreachable; exit 0,
  wall 2.190 s, peak RSS 197,284 KiB, swap 0. The checked Vec values are empty;
  this is cursor/layout evidence, not a dynamic allocation/deallocation frame.

The first harness uses initialized zero words: its purpose is cursor shape,
not arbitrary-value noninterference (the inherited projected volatile-store
certificate supplies that separate contract). Neither harness calls the
whole shipped destructor. They do not universally certify allocator effects,
Vec ownership/disjointness, the complete Drop caller or a compiler-fence
semantics. The Lean induction composes a cursor model; linking its memory
model to the Rust source execution remains explicit. Universal shipped Drop
correspondence is therefore **not claimed closed**.

## Stage 4: endpoint and stop condition

The assigned range 9200–9399 is exhausted: this continuation used its four
remaining unused numbers, 9396–9399. No number is reused, no unchanged proof
rerun occurs, and no out-of-range compilation is launched. A request for a
further assigned range was left with the lead while independent cursor gates
and receipt audits continued.

Full forest semantic admission remains open. Next proof work is the explicit
handoff from the three opaque source declarations to the existing owned
records/linear/drop specifications, the public entry-point admission checks,
and their composition with the tree validator, append/public/empty-root
semantics, transfer sentinel and Parts content. The ABI port makes that work
possible; typechecking it is not that proof. No source-matching P6 certificate
for the changed threaded aggregate is asserted.

Consequently the condition for a new endpoint with builder-premise deletions
was not met. `PrivacyR1HeadlineAcct`, `PrivacyR1FinalReleaseSource5`, the release
privacy roots, `RustRuntimeJoin`, checker/retry coupling and all concurrent
worker files are unchanged. No new endpoint or before/after deletion claim is
manufactured. The runtime and checker/retry joins remain named premises.

## Final evidence and resource record

`builder-cont11-attempts.jsonl` retains all four attempt receipts, including
J9397's failure. Every accepted source hash and current direct-import object
fingerprint is checked by `builder-cont11-audit.py`; the committed JSON stores
resolved dependency/tool pins, complete Kani stdout/stderr/time receipts,
per-run Rust source manifests, reservations and effective cgroup limits.
There are three passing modules and fifteen complete allowed-axiom audits.
All passing Lean and Kani runs have zero swaps.

Lean runs use env J and the inherited run-joint launcher, MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0, TasksMax=64, Lean -M7000. Rust/Kani runs use the
same caps, four cargo jobs and `RUSTFLAGS='-C link-arg=-Wl,--threads=4'`.
No arithmetic release gate, full frozen manifest replay or shipped-source
privacy release result is claimed. The generator `--check` and read-only
receipt audit pass. No existing module source/object is overwritten.

No shipped crate/program source changed against base 4715dbaf3, so the ELF
rule is not triggered. Rust changes are in the separate test/extraction-only
reference crate and cfg(kani) modules. No binary, object, LLBC, archive or key
is committed. No task-owned host job remains running; no wallet operation,
key cleanup, push or merge is performed.
