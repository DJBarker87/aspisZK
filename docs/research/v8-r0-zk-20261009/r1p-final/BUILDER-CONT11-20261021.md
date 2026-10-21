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
