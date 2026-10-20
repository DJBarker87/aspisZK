# Candidate 5: original-source consumer equivalence complete

Candidate `e58b87665233febecc1b1a75c506eac1a8b72e00`, exact parent
`d11f9b2fcbddf68fd1ffec297f987de0aa95a6c0`. The complete candidate
`fast_pairing.rs` is byte-identical at the frozen production revision
`39c2971dd16c95858a4cfd2c9ae35da052eacfa9`.

The measured retained saving is 11,273–11,286 stage-1 CU and 11,617–11,630
settlement CU, a conservative combined range of 22,890–22,916. These are the
existing matched runtime measurements, not new measurements of Lean edits.
Production Rust, ELF, proof bytes and checkpoint format have not changed.

## Checked

`CuSavingsCanonicalCandidate5` proves the actual old/new EbyKDot constructors
correspond, complete finalization produces the same value for every raw sum
array, and complete push execution can be substituted under an arbitrary
unchanged computational context. Push preserves returned errors, unchanged
state on rejected input, source counter guard, failures and divergence.
Noncanonical scalar rejection is retained. The shared raw multiplication
helper is byte-identical and universally parameterized, not assumed correct
or equivalent through an axiom.

The removed operand checks are discharged by actual source-producer results:
whole transcript scalar, gamma/ordinary sampler, decode8 and Wide.new;
whole strict byte/digit parser and field read; whole powers builder; checkpoint
Reader.e; and the actual dot finalizer. Raw word canonicality is not supplied
as an assumption to these producer results. The powers result includes the
exact field-power value and retains the final multiplication. Source loop
execution and counter increments preserve the private/public count invariant,
starting from the actual constructor.

`SourceValue` and `SourceState` are inductive predicates over executions of
those extracted source functions. They do not implement another verifier or
replace source computation with a trusted interpreter. Their canonicality and
counter theorems are consumed by the exported push theorem.

Fifty-seven selected targets pass with standard Lean axioms, plus the inherited
`core.fmt.Formatter : Type` declaration used by source unwrap diagnostics. Peak RSS is
below 2.99 GiB and zero process/cgroup swap. Exact commands, revisions, features,
source hashes, object/import hashes, wall time, RSS, swap, and axiom output are
in `CANONICAL-CANDIDATE5-COMPONENTS.json` and its selected run receipts. The
checker rejects stale sources/import objects and any selected failed or
sorry/native-axiom-bearing result. The root-owned Reader proof is a pinned
direct dependency of the source-origin theorem.

## Source/runtime boundary and caller composition

The exact old/new Rust files and generated callback/loop bodies are retained.
Source promotion inserts the shared-instance binder. Powers additionally uses
the same checked mutable-closure signature transport as Libra: the emitted
call_once applies the emitted raw callback handback, the ordinary instance
projects its returned value, and the builder preserves updated capture state.
The handback equation is checked in the kernel. The previously checked
`CuSavingsArrayFromFn.source_eq_build` is reused. Array.map reuses the identical
already-admitted `AspisR1CuRho.core.array.Array.map` runtime, not a new map axiom.
Original Rust/Aeneas compiler, ownership and standard primitive assumptions
remain explicit.

The checker inventories all seven production push statements. The actual
prepared_claim 29-term dot and fast_dots head plus two-term tail have now been
extracted, source-factored and proved equivalent for all success/error/failure/
divergence outcomes. Their actual gamma-power input invariants are discharged
from source scalar/resume origins and the actual powers builder, rather than
supplied as canonicality premises. The checked
`CuSavingsCanonicalVectorContexts.six_point_claim_context` and
`four_slot_tail_context` substitute these complete source computations under
arbitrary unchanged six-point/four-slot continuations. The separate
`check-canonical-vector-context.py --check` checks inverse factoring of the
complete original prepared_claim/four_dots bodies and parent/candidate identity.

The plain pair stream, shared inner16/outer4/high4 computation and final-relation
enumerate stream are also complete original-source consuming theorems. Their
actual successful strict reads and previous dot finishes establish operand
canonicality. The arbitrary malformed-byte, decoder error, counter guard,
panic/failure and divergence branches remain in the source computations.
`CuSavingsCanonicalDotPartialsCanonical.caller_context` consumes the source
partials result and derives canonicality before substituting the high-four
loop into both functional slots.

`CuSavingsCanonicalCandidate5Consumers` imports all five consuming contexts in
one coherent closure. Its final receipt `canonical-candidate5-consumers-final-a`
is green: exit 0, wall 1.604 seconds, peak RSS 2,982,972 KiB, zero process/cgroup
swap. A final topological refresh after the shared Reader and std map_err
normalization made all 57 selected direct-import object hashes coherent.
The source/error enum normalization changed generated registration names only;
the shared map_err definition is the exact already-admitted std source body,
now imported once.

All seven production push statements are covered by source loop equivalence
and inverse-audited unchanged-context composition. The candidate report now
records `closed_whole_candidate=true`. This is equivalence of candidate 5
against its exact parent under the existing Rust→Charon→Aeneas compiler/runtime
boundary. It is not a new extraction/proof of the entire transaction or of the
compiler. The unchanged production transcript, challenge schedule, proof bytes,
checkpoint bytes and settlement continuation are outside the replaced kernels.

EbyEDot has no use in any other production cost-probe src Rust file; the checker scans the complete crate source closure. Its changed push
is extracted and listed for re-pinning, but the checked API theorem covers
EbyKDot. No standalone EbyEDot public-API equivalence is claimed.

The changed declaration inventory is recorded in JSON: Dot layout; Q.from_wide;
Dot.new; Dot.push and its body/loop; EbyKDot.push/finish; EbyEDot.push. Shared
reduce and helper arithmetic are also source-pinned. No binary artifact is
part of this result.

The first direct standard all emission failed because builtin Iter has an
opaque producer layout. Exact original all/ok_or method bodies were then
extracted through invertible receiver-only adapters, with no algorithm rewrite.
The failed attempt is retained and not admitted. A stale incompatible
RawReducerNat object was quarantined by the root; its unchanged actual source
was focused-compiled under the coherent toolchain before the reducer proof.
No failed run is selected as release evidence, and no unchanged full runtime
regression was repeated for these Lean-only changes.

The tail source loop initially hit a heartbeat limit while checking an unfolded
monadic source-factor equality. That proof was replaced by direct symbolic
comparison of the actual source binds and a generic execute-unroll lemma.
The accepted focused replacement ran in under two seconds at the same resource
settings; no larger cap or concrete finite evaluation was used.
