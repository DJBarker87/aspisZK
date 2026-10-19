# Complete array emission and checked loop bridge

This checkpoint is proof/tooling work only. Production Rust remains frozen at
39c2971dd16c95858a4cfd2c9ae35da052eacfa9. It does not establish the final
optimized-verifier soundness/privacy transfer.

## Why this work occurred

The earlier fixed-prefix comparison uses a concrete ordered callback builder
for Rust `array::from_fn`. Proving that library interpretation against emitted
source encountered mutable-copy normalization, associated-type matching,
parent equalities, then cyclic Try/Residual dictionary emission. Pursuing
those frontend boundaries expanded the work beyond the optimization proofs.
The component count was not a measure of completed security-transfer scope.
No further general frontend expansion is planned in this checkpoint.

## Exact emission

The opt-in AENEAS_R1_TRY_GRAPH metadata maps the retained three Try associated
types and both parents to CuSavingsTryGraphRuntime. Residual retains its
already-lifted third parameter. Self and Residual::TryType are distinct in the
generic model: no false reverse associated-type equality is introduced. The
empty residual and two concrete cyclic infallible instances consume the
previously checked extracted methods. Interpreter/type/borrow checks remain
unchanged by this metadata extension.

The outer build/emission plan retains legacy inherited no-join frontend fields.
Those fields are not a claim about the new binary: the inner build receipt,
actual emission command and paired case receipts identify the metadata binary
and patch used. The checker uses those authoritative pins. Frozen receipts
are retained without retroactive editing.

The isolated binary c0d5cbc1676c3ab85ffc0b00e6ee440dd6dca3e02573a181ca9766d65ee01d6b
successfully emits the complete normalized library with strict checks. The
selected Types/Funs are exact declaration prefixes, not edited proof bodies.
Generated external axiom templates are captured for diagnostics and are never
imported. emit-array-graph.py --check checks the exact source cuts.

The 66 paired frontend controls pass, including the earlier diagnostics with
the flag off/on, incorrect/missing associated-output negatives, mutable-copy
rejection, and full emission off/on. Receipts, errors, generated hashes and
commands are retained. Duplicate large synthetic LLBC files are omitted from
this checkpoint; inputs are pinned by their per-case hashes and are generated
by the retained harness from the already pinned input. This is regression
evidence, not proof of a compiler transformation.

## Checked execution

CuSavingsArrayGraphStep proves the emitted body writes and increments correctly
under its local slice bound, including the backward handback. Callback errors
and divergence are preserved. CuSavingsArrayGraphLoop proves the complete
emitted loop equals finite fill whenever index + remaining = buffer length.
CuSavingsArrayFillCells equates that fill with the existing ordered callback
cells, including failures/divergence and checked-add failure. CuSavingsArrayStorage
proves symbolic suffix overwrite and initialized-array conversion.
CuSavingsArraySourceBuilder.try_eq_build and CuSavingsArrayFromFn.source_eq_build
consume the full emitted wrappers and equate from_fn with the callback builder
for arbitrary callbacks, without a success premise. The exact finite-loop
bridge is now complete under the explicit primitive/library interpretation.
No concrete
large recurrence is normalized. Successful focused receipts print only
propext, Classical.choice and Quot.sound; failures remain archived separately.

## Explicit boundaries

The LLBC deref-temporary rewrite remains experimental and its semantic
admission is open. Unsafe uninitialized/write/add primitives and the selected
borrow-aware forget handback have explicit models; compilation of these
models does not itself prove their source admission. Generic graph metadata
also remains within the explicit frontend/model boundary. The earlier opaque
Formatter TYPE in the dot/prefix closure remains separately allowlisted;
it is not present in these new loop proofs.

Build receipts record the outer 768MiB/1GiB/no-swap controller and inner
6GiB/8GiB/no-swap compiler, with reservations checked before create, at the
gate and continuously. Aggregate reservations stayed within 50GiB. Focused
Lean jobs were serialized on an idle Lean host with 6GiB/8GiB/no-swap caps.
The artifact checker checks commands, pins, success, reservations and swap;
it is not a final proof replay.

## Remaining deliverables

Full candidate-to-caller equivalence, remaining source/field/decoder bindings,
checkpoint/adapter composition, and the final soundness/privacy transfers are
still required. The authoritative per-candidate gaps are in OBLIGATIONS.md.
No security theorem is closed by counting these modules.
