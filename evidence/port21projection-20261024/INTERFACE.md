# Exact projection sufficiency and source remainder

## Before / after (no installed production interface changed)

Before: `OraclePortRuntimeBindingC7.ExecutionJoin D rust` is
`forall i : Input, rust i = verifier D dV i`. StoredCarrierBinding additionally
requires every accepted runtime stored RunView to equal the annotated experiment
view. Equality of source/model programs preserves all terminal values and logs.
`OraclePortJoinSplitStd.Signature` asks for complete pre/post carrier state.

After, PROPOSED ROOT alternative, now kernel-checked in Port21PROJECTION_Experiment:
`native : Program Bytes State (Option RunView × Private)`;
`model : Program Bytes State (Option RunView)`;
`forall H, forall run, (eval H native).2.1 = some run -> run.2.2 = true ->
(eval H model).2 = some run`;
and SEPARATELY `forall H, (eval H native).1.length <= Q`.
Then `lazyMean native emptyTable nativeMass <= deployedFailure model`, and the
same all-outcome Q law remains. The accepted hypothesis is explicit, not hidden
in a NativeBinding/noHash record or asserted proved for Rust. The model, actual
stored/public/proof carrier, extractor, private RawCoins and memoized oracle law
are unchanged. Quantifiers range over every H and every native/model causal
program, hence arbitrary finite adaptive schedules and input selections encoded
by those programs. No Some->None retargeting or successful-allocation domain.
This is sufficient; no abstract lattice-minimality claim is made.

`nativeMass` is EXACTLY existing runtimeMass after forgetting terminal Private;
existing failureMass averages the event `accepted AND extract run coins = none`.
`accepted_mass_transport` uses finite-support memoized expectation monotonicity,
not an assumed probability inequality. Accepted equality of the FULL stored run
retains its ordered recorded log, proof and public bytes, so the existing extractor
sees the SAME input for every coin bank. Reject/absent mass is zero; model mass
is nonnegative. Rejected runtime logs need NOT match for this root probability
argument. They DO remain in the independent source accounting obligation.
The native root log is not silently equated with the stored RunView's log: its
runtime/recording association is still a source/runtime obligation.

This root interface is NOT an arbitrary adaptive subroutine replacement law.
Port21PROJECTION_Core.Sim is the stronger local construction rule: matching ask
addresses and ALL answer continuations, plus an explicit terminal relation.
Its bind_sim preserves adaptive contextual composition when related return
carriers feed related continuations. evaluated/charge retain the full ordered
log on every outcome. No private state equality is needed. To use the weaker
root interface, first compose the actual experiment (including adversary and
extractor interactions), or prove a corresponding reached continuation rule.
An accepted-output-only helper premise does neither.

Port21PROJECTION_Counterexamples proves total Bool output equality AND accepted
full-log equality while a rejected execution issues two queries versus one.
Thus accepted-run refinement alone cannot discharge the all-outcome query law.
These are interface counterexamples, not production allocator counterexamples.

Finite Program semantics cannot themselves model an infinite-query native
execution. Actual finite SBF execution/abort interpretation, emitted fail/div
classification, P2/P7/S10, source/runtime/artifact identity and original query
constants remain explicit. No rollback erases prior oracle observations.
Privacy cleanup remains required in its separate workstream; this result says
only that soundness's observation need not contain private allocator state.

## Concrete source progress / exact omission

Port20 LLBC had structured parent IDs2/3 but neither in ordered_decls. Charon
reorder_decls.rs:303ff rebuilds reachability using StartFrom.matches on LLBC
item_meta.name. Those parent names contain `Impl(Ty ... InherentImplBlock)`,
not the plain `Accumulator`/`BatchedWeights` identifier in the old CLI roots.
options.rs:593ff delegates to the name matcher. name_matcher/mod.rs:245ff
matches Ident only with Ident; its inherent `Impl(Ty)` pattern branch is itself
TODO/false. This is before Aeneas; not an Aeneas parent-body rejection.

Job-only public free-function roots directly CALL both unchanged bodies.
The new Charon ordered output contains both parents and Aeneas emits
Accumulator.new, BatchedWeights.new and its actual loop. Source audit verifies
whole pinned ROOT objects and exact included source spans, actual parent->filled
calls, reserve pair->map_err->branch->resize def-use, full QM31 Copy/Clone and
four-u64 operands. Row10 still takes arbitrary weights, not a fixture length.
No backend/source/emitted Lean rewrite. Templates are uncompiled .lean.txt.

## Smallest missing primitive / literal policy scope

Pinned host Vec::new constructs `{buf:RawVec::new(),len:0}`. Vec::try_reserve_exact
calls ONLY `self.buf.try_reserve_exact(self.len,additional)`. RawVec forwards
through unsafe inner reserve/grow_exact/finish_grow. Fresh cap0 selects
Global.allocate -> alloc_impl -> alloc -> __rust_alloc (plus allocator shim).
RawVec failure returns TryReserveError; helper maps its ACTUAL result to
Allocation, not an arbitrary Boolean. On normal return, deriving the len0
frame would imply empty initialized contents, independent of pointer/capacity.
Full QM31 clone is emitted `ok self`; constants retain all four u32 words.
Vec.resize -> extend_with reserves then clones/moves into the initialized
prefix. This is exact SOURCE evidence, not a native field/effect theorem.

runtime-source-graph.json pins the real cost-probe target_os=solana global
BumpAllocator and lock-matched solana-program-entrypoint2.3.0. The SDK crate
archive checksum and exact source member were checked against Cargo.lock.
Bump alloc uses private pointer read/write, saturating/alignment arithmetic,
null return; dealloc is empty. Default entrypoint allocator/panic expansion is
recorded separately. Host extraction uses native std's selected Global shim,
NOT this SBF global declaration: source inclusion is not a deployed identity.
All native pointer/intrinsic/alloc shim/abort primitive leaves need their exact
selected-runtime interpretations. Absence of Digest arguments proves nothing.

Current emitted reserve remains an opaque external returning arbitrary
`Result ((core.Result Unit TryReserveError) × Vec T)`. It has no law fixing
post-Vec len/content, no ordered effect relation, and no native private-frame
law. The approved filled_exact covers GIVEN Bool content only, and its header
excludes capacity/physical allocation/Drop. D157 explicitly excludes allocation
failure and unsafe. D189 and S2W design lines1210ff cover the SDK snapshot/account
projection under the runtime allocator premise, not arbitrary Vec helper or
allocator effects. S2H design lines163ff explicitly preserves abort query history
and warns opaque P2-P4 do not imply a typed runtime relation. These scopes have
not been extended. No TrustedStd field or primitive law was added.

Small reviewable missing proof obligation: for the PINNED selected allocator
shim/Bump arena, show private field/frame preservation and actual normal
Ok/Err/null/abort transitions with their ordered prefix effects, using the
runtime's existing arena admission; then derive Vec's len0 frame and resize
content by source control. No whole-helper equality is needed. If the intended
route is to TRUST that primitive law rather than prove it, that requires an
explicit policy decision outside this job; it is not installed here.

No native no-RO/content/count producer exists yet. The abstract external type's
spurious post-Vec/effect choices demonstrate missing specification, not a
production counterexample. No reached-S2 invariant or S2 Kani check was claimed;
no all-Variant timeout repeated. Parent/helper linkage is closed as extraction
and exact-source association, not as a source refinement theorem.
