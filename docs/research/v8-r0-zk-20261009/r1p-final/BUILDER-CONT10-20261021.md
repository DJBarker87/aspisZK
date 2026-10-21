# Builder continuation 10

Branch `codex/cx-builder-ref10-20261021`, base `e5d6d81a5`.

## Stage 1: destructor field composition

`BuilderDropFields` composes the existing projected volatile-word contract
at byte granularity. `word_bytes` and `column_bytes` identify exact half-open
byte intervals; `word_frame`, `column_frame`, `frame_compose`, `fields_frame`
and `fields_observation` cover arbitrary word counts, initial bytes and lists
of fields (in particular the sixteen Vec columns). No disjointness between
columns is needed for the frame result; retained output must be disjoint from
the union of buffers. J9378: exit 0, 1.39 s, peak 2,537,168 KiB, zero swaps;
nine allowed-axiom audits. J9377 was an elaboration failure corrected by
closing a definitional equality; no resource failure or cap increase.

No whole-frame Kani check or unchanged store check was rerun. The existing
57-check projected store certificate is inherited. The new theorem composes
its write-set shape for arbitrary lengths. Actual pointer-to-byte enumeration,
iterator traversal and allocation/deallocation semantics remain source
correspondence obligations; the model theorem alone is not that certificate.

`BuilderDropStoreComposition` strengthens stage 1: its input is an arbitrary
store satisfying the projected word write-set contract. A word-list induction
then a field-list induction derive the complete destructor frame and retained
output rule, without equating that store to the concrete `wipe`. J9390: exit 0,
1.25 s, 2,532,776 KiB, zero swaps; four allowed-axiom audits. Rust pointer and
iterator correspondence remains the source boundary described above.

## Stage 2: forest standard library and validator

All 24 std externals have explicit adapters in `BuilderForestStdPort`.
`BuilderForestStd` adds 27 checked specifications covering array iteration,
mutable array mapping, lazy flattening (including empty inner iterators),
short-circuit iterator any, sequential checked u64 accumulation, Option/Result
branching/mapping, and positive-size slice chunking with exact head/tail
contents. Existing proved adapters supply from_fn, map-next, ranges and slice
any. No std external is an axiom. J9380/J9382: 1.66/1.24 s,
2,549,788/2,542,296 KiB, zero swaps. The port inventory distinguishes these
24 declarations from three opaque Aspis functions: external_linear_lazy,
records and Drop. No opaque source declaration is silently supplied by a std
model.

Three projected Kani harnesses replace the timed-out whole-tree comparison:
frontier transition 307 checks (three unreachable), index guard 74 checks,
and root branch 329 checks (three unreachable). All pass; 5.824/4.407/6.482 s,
620,716/604,440/623,180 KiB, zero swaps. These are projected expressions,
not calls to the whole shipped validator. The frontier arrays are projected
to one arbitrary node/empty pair; the root helper to one arbitrary common
pure result. Full bytewise/source pins, commands, limits and logs are in
`builder-cont10-host-evidence.json`.

`BuilderForestValidatorExtracted` dependency-slices the actual generated
validator. The unchanged root reconstruction call becomes an explicit pure
function parameter. There are no opaque declarations in this slice. J9387:
exit 0, 1.31 s, 2,544,424 KiB, zero swaps, two allowed-axiom audits.
`BuilderForestValidatorSteps.complete_frontier` proves its entire carried
loop equals the early-return scan by induction on symbolic remaining length.
It preserves errors, stops at the first bad step and does not enumerate twenty
concrete cells. J9391: exit 0, 1.97 s, 4,011,288 KiB, zero swaps, five
allowed-axiom audits. No whole-frame or timed-out whole-validator job reruns.

The aggregate port J9383 exposed a distinct backend-interface obstruction:
raw Aeneas emits mutable callback borrow-back closures, whereas env J expects
(output,state) pairs. Errors include hash_fields_with_trace, permute callbacks
and the curried nullifier callback. It is rejected, not an admission certificate.
Dependency slicing removes unrelated callbacks for the focused validator;
it does not repair the full forest caller. Earlier failed edits and missing
object J9386 remain in the attempt receipts. Only successful matching hashes
and dependency fingerprints count as proofs. `BuilderForestValidatorAcceptance.validator_success` derives successful
execution of all twenty actual projected checks from successful whole-wrapper
execution, for every supplied pure root function. J9394: exit 0, 1.87 s,
4,010,620 KiB, zero swaps, four allowed-axiom audits.

The strengthened root harness also covers all thirteen tree-error variants:
331 checks (three unreachable), 3.703 s, 523,324 KiB, zero swaps. Its earlier
329-check result remains supplemental; the changed harness was checked once.

Complete semantic admission
(RspendPlus, append/public/empty-root correspondence and sentinel) is still
not established by these validator control-flow facts.

## Stage 3: shipped runtime inhabitant

Pending.

## Stage 4: checker/retry coupling and Source5

Pending.
