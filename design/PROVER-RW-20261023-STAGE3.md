# Stage 3: selected sampler refinement, whole attempt still open

ADOPTION CANDIDATE; branch `codex/cx-prover-rw-20261023`. This continuation
starts at `54390a5a5c`. Production code remains the `9c131667ca` checkpoint.
No merge, push, protocol change, artifact replacement, or security claim.

## Established component

`R1Z.ProverRwSemanticSampler.sample_total_semChal` proves, for **every**
32-byte block, existence of the actual selected QM31 sampler result and
its decoded/embedded equality to `R0P.SemSource.semChal (decodeState block)`.
Success, canonicality and the desired sampler equation are conclusions,
not hypotheses. `ProverRwSamplerModel.sample_total` also identifies all four
canonical coordinates with the existing `SamplerNatModel.qm31Digits` of
`SourceSamplerByteRank.rank`. `sample_exact` transports the complete result
to the retained checked sampler, copying only nominal field coordinates.

The arithmetic transport proves that the newly extracted wrapping division,
byte-assembly and four-pass bodies equal the previously certified checked
bodies. Subtraction is guarded by positive `j`; byte offsets are bounded by
`i < 8`; the four-pass increment is guarded by `i < 4`. The division-loop
body equality includes out-of-range failure cases. Function equality then
transports the loops without unrolling eight/four iterations or reducing
concrete 256-bit divisions. The prior sampler correctness and the model's
`ProverCommitSemanticSampler22.model_qm31` are reused unchanged.

This closes the **sampler-lowering delta** identified in the previous handoff,
for the explicitly normalized extraction described below. It does not close
all of R-wire, install the sampler into the full caller's external dictionary,
or identify the actual block read by each semantic row.

## Extraction compatibility and trust boundary

The existing actual-source Charon/Aeneas sampler extraction is reused, not
rerun. Its input/source pins and emitted files remain under
`continuation/generated-sampler` and the prior extraction receipts.
Attempt 11200 accepts its unmodified Types. Attempt 11201 rejects its
unmodified Funs: the emitted `U64.wrapping_shl remainder 32#i32` supplies an
I32 where the pinned backend API requires U32. The failed log is retained;
its elaboration-error `sorryAx` is not accepted proof evidence.

`normalize-sampler.py` changes exactly that one literal to `32#u32`, checks
the occurrence count, and records before/after SHA-256. The normalized file
is committed separately in `lean/prover-rw-20261023/ProverRwSampler/Funs.lean`.
No native Rust source or shared backend changes. `shift_exact` proves the
normalized wrapping operation agrees with the existing checked signed-count
shift for every U64 input. This is a disclosed backend API adaptation, not
a claim that the original emitted Funs typechecks. All the other emitted
operations remain unchanged.

## Validation

Env J attempts 11200–11211: seven passes, five retained elaboration failures;
12/100 Lean compiles, no new Kani runs (42/60 total retained). Next ID 11212.
`stage3/summary.json` includes every command target, source SHA, source revision,
dependency fingerprint, exit, wall time, peak RSS, swap and full axiom lines.
The final focused audit is 11211: exit 0, 1.70 s, 4,062,488 KiB peak RSS,
zero swaps. All twenty theorem audits use only a subset of
`[propext, Classical.choice, Quot.sound]`. No additional axiom, sorry,
admit, native_decide, heartbeat or recursion limit is introduced in proofs.
Generated files retain their existing resource options.

The private launcher is the existing env-J launcher with only the assigned
11200–11399 range and TasksMax=64 adapted. Common-rule stricter Lean caps
remain -M7000, MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0; it records a
24 GiB populated reservation before each launch. Only new module names are
installed; no pre-existing shared module/object is replaced. Private failed
and successful revisions are retained under the branch's host stage3 directory.
No unchanged successful target was recompiled. The audit consumes the final
compiled sampler dependency chain; no full frozen release replay is claimed.

Absolute timing is skipped: the preflight records two populated peer scopes
(8 GiB each), including the retained Z3 scope, at load 1.37/1.20/1.18.
Neither job is touched. No timing sample or unchanged native regression is
run. The prior 1000-pair differential, interleaved relative timing and ELF
byte-identity receipts are reused; no new ELF or runtime coverage is claimed.

## Remaining per-attempt and conjunct-1 obligations

The full `ProverRwCaller` translation still cannot enter an axiom-free proof
build: `TypesExternal` and `FunsExternal` are unbound templates. The prior
caller audit enumerates 287 holes, including 104 opaque project functions
in the detailed obligation inventory. A proved focused sampler does not
subtract an installed hole from that full-caller dictionary. No full-caller
Funs compile is attempted with invented definitions or installed template axioms.

1. Bind each external type/function and its exact selected source body,
   representation and domain. Complete the remaining leaf-contract gate,
   including ordinary/gamma/circle samplers, geometry/weights, hashing,
   parallel evaluation and P_R1; local Kani results need compiled composition.
2. Prove the full per-attempt equation at `prove_masked_with_attempt`: mask
   material/application and private salts; semantic foundation and rows 0–24;
   point claims and rows 25 onward; encodings, salted commitments and trees;
   opening rounds/folds; ordered query scan; P_R1; compact publication. Include
   returned errors, proof/audit bytes, reservation state and ordered oracle
   effects on rejected and fatal paths. The sampler theorem supplies a callee,
   not the source caller's block provenance or this equation.
3. Rebind the rewritten retry owner and selected 64-byte caller. Discharge the
   concrete `RealR1_OuterOwner.PrefixContract` and `BodyContract` instances;
   reuse its theorem only after those actual instances are proved.
4. Instantiate the native real experiment, witness/compiler/public map and
   observer, then provide the first `RustProverRefinement` conjunct's RunJoin
   for every admitted adversary/witness with the unchanged realBad and
   realSeedQueries. Establish E1/E2 laws and the required L1/L2 joint coupling,
   full ordered ROM view/observer-decision transport, and compiler/runtime
   connection. Per-attempt fixed-tape equality alone does not supply these.
5. Complete the deferred quiet-host absolute gate and remaining Stage 2
   adoption gates, then replay the coherent final frozen dependency closure.

No top-level privacy premise has been discharged, changed, hidden, or added.
The whole per-attempt equality, conjunct 1 and the security target are not yet
established. The next concrete deliverable is an axiom-free, fully typed
external dictionary and selected semantic-row caller binding that consumes
`ProverRwSemanticSampler.sample_total_semChal`; it must identify the actual
read block and retained ordered effects rather than assume their equality.

## Continuation checkpoint (2026-10-24)

The full caller now has an axiom-audited **parameterized** dictionary and a
concrete selected sampler entry, plus direct rewritten retry-control refinement.
This supersedes the earlier statement that no full Funs proof build was attempted.
It does not supply the remaining native dictionary instances or conjunct 1.
See `design/PROVER-RW-20261024-STAGE3-CONTINUATION.md` for exact claims,
backend adaptations, rejected audits and the remaining obligations.

The continuation stops on a proved false unrestricted pure-dictionary E1
refinement: the actual emitted entropy iteration cannot retry then succeed
below the limit under any fixed pure dictionary, whereas a native zero block
followed by a nonzero block does so. See the continuation's second checkpoint
and `ProverRwEntropyIteration.no_retry_then_success`. This does not refute
privacy; the next required interface must carry effects or have a proved
observational transport. Final audit 11261 is standard-axiom-only. Next ID
11262; 60/100 Stage 3 Lean compiles and 42/60 Kani runs used.
