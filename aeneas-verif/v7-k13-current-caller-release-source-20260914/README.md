# V7 current release-profile caller and snapshot source bundle

This bundle fixes the execution-profile gap in the earlier `V7CallerCurrentR18`
receipt.  That extraction used Cargo's development profile.  The current bundle
uses `--release`, matching the selected optimized runtime, and roots both the
complete observer-capable Tag-73 caller and the literal
`snapshot_query_batch_prechallenge` helper in one Charon/Aeneas graph.

## Source and generated graph

- Source revision: `e508c2b632ee02282404cd04c4c420df85455128`
- Charon: `0.1.223`
- Aeneas: pinned `d860` Linux backend
- Lean: `4.32.0`
- Cargo profile: `--release --locked --package aspis-core --lib`
- Feature: `aeneas-observer`
- Roots:
  - `aspis_core::v6_transcript::verify_v7_compact_transcript_and_relation_prepared_with_hiding_context_observe`
  - `aspis_core::v6_transcript::snapshot_query_batch_prechallenge`

Source hashes:

```text
field.rs          50f66ca87b924efe7c52a7ae274b805876d0550e16473d746d4f312e320255c3
sumcheck.rs       3f390d96a668206b9d49691cd337f58153ba70d688329697dcb73c2891dfe2dd
v6_transcript.rs  03c561a5048efc308ba4f479ebe19597a4a36dfa9b035571185372754b299fb5
LLBC              db337ead22903b7d366e3bcd652bcdeb45b19d30bd1eea775aa2427b8e269ced
Funs.raw.lean     3947059448981329b5150acba412da4860be0b4b453b367419d239e81b8704bc
Types.raw.lean    3f03fd09a9b5b878496829c0e6389f514c7a4ba4b7e138b5e315546d82f1fc52
```

Charon exited zero in 13.51 seconds at 654,996 KiB peak RSS. Aeneas exited
zero in 227.18 seconds at 3,836,232 KiB peak RSS. Both ran through Tailscale
inside a 6 GiB hard cgroup with swap disabled.

## Generated integration repairs

`Funs.raw.lean` and `Types.raw.lean` are the untouched backend outputs. The
checked generated files make source-neutral compatibility repairs for the
pinned Lean/Aeneas library: narrow umbrella imports, the already audited
mutable-iterator write-back adapter, transcript namespace qualification,
executable Boolean equality, one curried fold, the no-op diagnostic callback's
literal result shape, and explicit/correctly typed wrapping-shift operands.
No Aspis function body is replaced by a model or external axiom.

The complete generated graph kernel-imported successfully. Peak RSS for its
largest target (`Funs`) was 3,199,024 KiB with zero swap.

## Proved scope

The files in `proof-r20/` prove the actual generated release-profile field,
half, multilinear, tensor, deferred grouped-binary, component, accumulator,
256-term dot, and snapshot functions. The strongest current results are:

- `generated_live_six_component_accumulator_corresponds`
- `generated_prequery_dot_256_corresponds`
- `generated_snapshot_prechallenge_corresponds`

Every printed axiom set is contained in
`[propext, Classical.choice, Quot.sound]`; there is no `sorryAx` or
project-specific axiom.

This closes the release-profile generated computation layer, not all of G1/G2.
The remaining immediate source obligation is to derive the literal six-component
accumulator and its canonical/length premises from the translated successful
`finish_onefold_relation` path, then identify the snapshot fields with the
maintained restored K1.3 checkpoint.

## R21 caller-return experiment

A default-off Rust wrapper now retains the observer snapshot as an `Option` in
the successful caller's return value.  Its focused Rust test passed.  The new
release Charon root also exited zero in 13.68 seconds at 630,932 KiB RSS, and
Aeneas exited zero in 242.81 seconds at 3,952,440 KiB RSS; both used the same
6 GiB, zero-swap Tailscale NUC scope.  The new LLBC hash is
`a1acd1a671e1f872a14d9280437f345756474325bfec69a9bcbafe601a1d72fa`.

The generated R21 root is not yet a checked source theorem.  Its dependency
files compiled, but the generated `Funs.lean` exposed an Aeneas mutable-closure
write-back mismatch: the generated callback methods return closure state where
the generated `FnOnce`/`FnMut` instances require `Unit`, while the generated
observer wrapper drops that state before the outer wrapper destructures it.
The focused target failed at generated lines 23332, 23356 and 23384.  No opaque
callback or fabricated `Some` value was introduced to make this compile.  The
next source step is a source-level observer-return shape that the pinned backend
can translate faithfully, followed by the actual accepted-path `Some` theorem.

## R23 capture-branch extraction and bridge

R21's observer-return wrapper exposed a generated mutable-closure write-back
mismatch.  R23 avoids that backend shape without changing production
acceptance: the default-off observer feature now calls the named local helper
`capture_v6_query_batch_prechallenge`.  With capture enabled, the helper
returns `Some` of the same borrowed pre-query snapshot; with capture disabled,
it returns `None`.  The production feature builds the no-op helper, so the
selected verifier path is unchanged.

The extraction was rooted at the helper and its literal relation-tail call
graph at source revision `f18928e4`.  The generated LLBC is
`generated/V7SnapshotReturnR23/V7SnapshotReturnR23.llbc` with SHA-256
`5c1c49a61593a70849cf4dec6f5c5aa380ffa9bb3bebc1ffd922a0bd407c21b9`.
Aeneas completed in 219.31 seconds with 3,323,700 KiB peak RSS and zero swap
inside the build-host 6 GiB zero-swap scope.  The focused release observer test
and production-feature release check both passed.

The `proof-r23/` chain replays the field, weight, 256-entry dot, snapshot,
tail, and capture results against that generated graph.  In particular,
`generated_capture_true_snapshot_witness` proves that enabled capture returns
a concrete snapshot which copies the prechallenge fields and whose terminal
discrepancy is the exact full 256-term residual.  The full focused chain and
its axioms audits passed with only `propext`, `Classical.choice`, and
`Quot.sound`.

This is still not an end-to-end acceptance theorem.  The next source-to-model
step must connect a successful generated `finish_onefold_relation` execution
to the captured checkpoint and construct the concrete K1 source obligations;
the semantic-terminal, two-tree authentication, batched residual, relation,
and transaction-wrapper facts remain to be derived from source rather than
assumed.

## R24 full-wrapper kernel bridge

R24 re-extracted the complete observer snapshot-return wrapper against the
restored R23 source (current `v6_transcript.rs` SHA-256
`e0660c2c966356af105ca8181e26aa2f8a61651e3099c235ed0965ec7c0b2a5f`).
Charon completed in 4.52 seconds at 768,608 KiB with zero swap; LLBC SHA-256
was `44a0169370c52e30b366e01ff453a7ab59faaa532cc5bc9d42a594e2100ccf2f`.
Aeneas completed in 220.81 seconds at 3,290,404 KiB with zero swap.

`toolchain/normalize-r24-full-wrapper.py` freezes the raw-graph shape and
performs only checked Lean/Aeneas compatibility repairs: pinned imports,
method-path spelling against executable library models, mutable-iterator ABI,
Boolean equality, one tupled fold callback, erased shift widths, the two
no-op `FnMut` unit results, and diagnostic strings represented by a
kernel-constructed `Str`. The latter changes neither a verifier success value
nor a `V6TranscriptError` value. It has no `sorry`, `admit`, `native_decide`,
or axiom declaration. The raw and normalized function SHA-256 values are
`80d2129d19326a823c10c764aec8cd6e53d37f57394079b7db1f81ceef5a7c7c` and
`59270731c9feb884a5675d0e22f9fb2926573d7a41506853a30f3b7d460a8247`.

The complete normalized graph compiled in a fresh 6 GiB, zero-swap cgroup:
`TypesExternal` exited 0 in 1.47 seconds at 2,569,588 KiB; `Types` exited 0
in 2.15 seconds at 2,624,116 KiB; `FunsExternal` exited 0 in 1.85 seconds at
2,614,860 KiB; `MutableIteratorCompat` exited 0 in 1.33 seconds at 2,564,436
KiB; and complete `Funs` exited 0 in 14.61 seconds at 3,263,204 KiB. The
focused theorem `proof-r24/V7CallerCurrentReleaseR24FullWrapper.lean` then
exited 0 in 1.44 seconds at 2,556,952 KiB. Its
`#print axioms snapshot_wrapper_calls_captured_inner` result is exactly
`[propext, Classical.choice, Quot.sound]`.

That theorem proves definitionally that the full observer snapshot wrapper is
the translated shared verifier inner path with its generated no-op
prechallenge closure and capture set to `true`. It does not assume acceptance,
construct a snapshot, or hide the parser, transcript, terminal, relation, or
query path. The companion focused theorem
`terminal_body_preserves_prechallenge_snapshot` replays the literal terminal
branch and proves that it returns the exact incoming prechallenge option; it
exited 0 in 1.98 seconds at 2,575,564 KiB with zero swap and the same clean
axiom set. The remaining end-to-end work is to invert a successful full
execution through that inner path, obtain the actual captured `Some` snapshot,
and derive the K1 source obligations from its source checks.

R25 tested replacing the no-op closures with named function items. It passed
the focused observer release test and production release check, but the pinned
Aeneas backend rejected the wrapper's function-item lifetime shape in
`RegionsHierarchy` before emitting Lean. The experiment was reverted; the
current source is byte-identical to the R23 capture-helper source. No generated
model, external axiom, or fabricated snapshot result was accepted as a
workaround.

## R26 accepted relation loop to K1

R26 closes the accepted post-prechallenge relation-loop source chain. The
capstone theorem
`V7CallerCurrentReleaseR26AcceptedTerminalEndToEnd.accepted_relation_loop_end_to_end`
starts from a successful call to the literal generated
`finish_onefold_relation_after_prechallenge_loop`. It extracts the three exact
accepted relation rounds and connects the source implementation's component
weights, 256-to-64-to-16-to-4 value folds, and production terminal dot to the
maintained K1 `candidateClaim` equality. Canonical field representations,
fixed component layout, and expected vector lengths are stated explicitly as
source-domain premises.

The final frozen replay at source revision
`34bb5ecdd9bf9b4f30f2daf769541dbca33edd2d` compiled five generated modules and
the complete 117-module proof closure. All 122 targets exited zero with zero
swap. The capstone used 7,252,340 KiB peak RSS in 4.46 seconds, while the
largest target used 7,268,020 KiB. Both capstone axiom audits reported exactly
`[propext, Classical.choice, Quot.sound]`.

The replay uses Aeneas revision
`b59d5188c082f704a418c7cb4e52ad69328002d1` with the checked
`AENEAS-FORMATTER-UNIT.patch`. That patch gives the backend's ignored formatter
state the concrete carrier `Unit`, matching the imported formatter operations
that return the state unchanged and removing the unrelated custom type axiom
from the capstone's dependency closure. The manifest pins the patch, all proof
and generated sources, and the replay script. Exact hashes and resource
measurements are recorded in
`evidence-r26/extraction-and-snapshot-kernel-check.txt`.

## R27 current production observer entry

R27 extracts the feature-gated monomorphic
`observe_v7_read_only_with_statement_digest` entry at source revision
`fd8ca3a715c234a46c2c436fa92eb05eb9ff0713`. This entry uses the current
production parser, hiding context, terminal predicate, authenticated query
fold, and shared verifier. Its only observational change is to retain the
pre-existing prechallenge callback value so the source proof can name the
accepted execution's exact K1 boundary.

The normalized generated graph compiles under Lean 4.32. The focused theorem
`productionObserver_acceptance_exposes_core` proves by control-flow inversion
that every accepted observer result exposes a successful exact parser result,
public-key conversion, hiding-context construction, frozen schedule reads, and
successful shared-core call carrying the returned prechallenge snapshot.
Companion theorems prove forward exact result flow and fail-closed parser
rejection. Exact definitions now discharge the public-key conversion, hiding
context construction, frozen schedule reads, generic array/Result helpers,
and field equality. Their axiom audits contain the remaining parser,
shared-core, onefold, snapshot, and terminal interfaces plus `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorryAx`.

This still is not an end-to-end acceptance theorem. The shared-core call and
production callback interfaces in the small outer graph remain explicit
external declarations. They must be linked to the R26 generated shared-core
proof and the existing parser, terminal, Merkle, and query-fold source proofs.
The transaction-wrapper premises and final maintained security/probability
conclusion also remain outside this bridge. Exact hashes, normalization, and
focused resource measurements are recorded in
`evidence-r27/production-observer-source-bridge.txt`.
