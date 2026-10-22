# Checkpoint bytes third packet

Branch `codex/cx-ckpt-bytes3-20261022`. Work in progress; no closure claimed.
Additive modules and task tools only. No shipped source, existing Lean,
session A candidate, shared object, wallet or key changed. No env J attempt
used; the concurrent privacy job is untouched. No ELF rebuild trigger.

## Stage 1

`CheckpointBytes3Namespaces` compiles: explicit maps preserve every
Prepared/Accumulator component, all array/weight positions, physical queries,
state/root bytes and next; K/E maps have checked two-way inverses. This is
type transport, not decoder or source-operation adoption. Attempt 1: exit 0,
wall 27.51934037497267 s, peak RSS 3581394944 bytes, swaps 0. All six
`#print axioms` results are standard subsets (see lean.log and manifest).

Kernel identification is closed at exact production widths:
`CheckpointBytes3KDecode.decode_k_identification` (16 bytes) and
`CheckpointBytes3EDecode.decode_e_identification` (32 bytes) identify the
complete Result with C5, mapped through explicit `rawK`/`rawE` transports.
`reject_k`/`reject_e` cover every canonicality rejection; `successful_k`/
`successful_e` characterize every output. No canonical-input premise, decoder
equality hypothesis or successful-fixture restriction is introduced.
The word proof is bounded and symbolic, on arbitrary byte values, with
explicit Usize range checking and both platform widths; `pack_append` and
`pack_value` use named bitvector/Nat lemmas. No numeral buffer is normalized.

Accepted final attempts: Word-6, WordMath-4, ScalarShape-2, KDecode-4,
EShape-1, EDecode-1. All exit 0 and swaps 0; peak RSS <=3655778304 bytes.
All added theorem axiom sets are subsets of the three standard axioms.
Exact source revisions, targets, wall/RSS and complete axiom lines are in
manifest.json and per-attempt receipts. WordMath-1 is explicitly rejected:
its exploratory bitvector tactic generated a nonstandard native verification
axiom. It is replaced by named lemmas; neither it nor compiler recovery
sorryAx reports count as accepted evidence.

Verbatim final stage-1 theorem statements (in their respective namespaces):
```lean
theorem decode_k_identification (b : Slice U8) (width : b.val.length = 16) :
    decode_k_spec b =
      ok ((ExactLeafFieldCodec.decodeQM31 (bytesOf b.val)).map rawK)

theorem decode_e_identification (b : Slice U8) (width : b.val.length = 32) :
    decode_e_spec b = ok ((FoldedLeafCodec.decodeWide (bytesOf b.val)).map rawE)
```

Local attempts use
private objects, shared mkdir lock, -j1 -M4400 -DElab.async=false; manifest.json
and individual receipts retain exact commands, revision, source/dependency
hashes, exit, wall seconds, peak RSS bytes, swaps, errors and axiom lines.
Failed attempts' compiler recovery axioms are not accepted proof evidence.

## Stage 2 and stage 3

Not yet established. The inherited ResumeOps callbacks are not a concrete
source instance. No Kani fact is installed as a Lean axiom or hypothesis.
The final theorem with only S2S10CallerBinding and S1S7S8StateProvenance has
not been constructed. No statement is quoted as proved before it compiles.

## Stage 2 — reader transport and independent operation gates

`CheckpointBytes3Reader.read_k_c5` / `read_e_c5` compose the actual extracted
bounded raw reader with the newly identified scalar reference decoders and
explicit source K/E namespace conversion. They return exact section bytes,
unchanged backing, cursor +16/+32, and the C5 output mapped to source
`core.result.Result`, including `.Err .Checkpoint`. The reference decoder
sequencing is now concrete; this is not a kernel claim identifying the Rust
from_le_bytes implementation (the independently pinned Kani gates supply
that separate implementation evidence).

Reader final attempt 3: exit 0, wall 9.108965374995023 s, peak RSS 3658285056
bytes, swaps 0; both axiom sets [propext, Classical.choice, Quot.sound].
Attempts 1–2 preserve let-pattern/instance-transparency rewrite failures.

The independent tools crate includes the production Reader and the semantic/
weight helpers verbatim. `source_check.py` checks byte identity. Each Kani
harness checks one operation; none calls resume/checkpoint/whole verifier.

| Accepted gate | Exact scope | Wall seconds | Peak RSS KiB |
|---|---|---:|---:|
| semantic-1 | 10 K fields, arbitrary 161-byte backing, offset 1; all outputs and noncanonical rejections | 16.52824234799482 | 533456 |
| weights-2 | actual helper on 64 entries, arbitrary 1025-byte backing, offset 1; all output limbs and rejections | 126.02069685608149 | 4676536 |
| filled-2 | actual heap::filled(64, arbitrary raw K), successful length/content | 5.216660239035264 | 309184 |
| resize-2 | actual empty Vec resize(64, arbitrary raw K), length/content | 3.02196759195067 | 203476 |
| box-2 | actual Box::new(Prepared), every field, all three variants, arbitrary canonical E fields and arbitrary other contents | 3.558823192026466 | 210076 |

All exit 0, zero swaps; #print axioms N/A (Kani). Exact commands, source
revision/pins, dependency fingerprints, GNU time and cgroup peaks, optimized
compiler environment and bounded host reservation preflights are in kani/.
Every job used MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64.
Expected work was compilation then the named symbolic operation gate, never
arithmetic elimination. No env J attempts were used.

Failures/replacements are retained: weights-1 exhausted CBMC's 2^10 addressed
object table (not a failed content assertion or memory-pressure kill).
weights-2 changes only that tool bound to 2^12, with the same memory cap.
box-1 failed the 66-step memcmp unwinding assertion on a long array; box-2
compares query/semantic elements individually. filled-1 and resize-1 used
symbolic n<=64, reached cgroup peaks 6652743680/6614794240 bytes, and were
explicitly stopped at 216.4/153.8 s (exit 143) after inspecting the path
explosion; neither was killed by memory pressure or retried unchanged.
They are replaced by the exact frozen S2 length 64, which checks in seconds.
The inherited K/E scalar gates are reused, not rerun, since their covered
source is unchanged. audit.py checks current shipped sources and each
accepted harness/helper body even when unrelated harnesses changed later.

`CheckpointBytes3Allocation.filled_exact` adapts the existing fallible
allocation content model to the exact source Vec/Error types. It preserves
both reservation outcomes. `filled_success_content` derives reservation
success and every returned value from successful execution; no allocation
availability premise is added. `filled_rejection` preserves Error::Allocation.
Final attempt 1: exit 0, wall 11.477649916429073 s, peak RSS 3662725120 bytes,
swaps 0; all four axiom sets standard. This is the explicit outcome/content
model, not a claim that the physical allocator always succeeds.

## Stage 3 — adoption boundary and unresolved final scope

**Not closed:** a complete source ResumeOps instance and its semantic/weight
kernel content join, its application to successful_fields, and source-stage
adoption through reached_stage/strictStage. The operation gates above are not
Lean hypotheses and are not promoted into a complete source instance.
Neither intended remaining premise has been defined as a wrapper for the
missing observation equality. No two-premise final source theorem is claimed.

There is a concrete all-outcome obstruction which must not be hidden in
caller binding: Rust resume returns Error::Allocation when heap::filled
fails on authentic bytes; strictStage's authentic saved-ten path returns a
resumed state and has no allocator failure branch. Kani's command line uses
`--no-malloc-may-fail`, so successful allocation-content gates cannot discharge
allocation availability or validate a failing physical allocation.
`no_unconditional_allocation_success` kernel-checks the false-reservation
counterexample for the typed outcome model. This does not obstruct a theorem
conditioned on an actual successful source resume; successful_fields and
filled_success_content then derive the reservation fact. The lead was asked
whether the final source theorem is success-conditioned or covers allocation
failure too. No answer was received while doing the independent work; no
release/security target was silently weakened to resolve that distinction.

The source inspection receipt also records that the imported logical std
has Iter/IterMut contents but no `core.slice.iter.IteratorIter.next` or
`alloc.boxed.Box.new` declaration under those names. No theorem is inferred
from those failed #print commands; the temporary diagnostic module is not a
release module. Box content is separately checked by the native operation
gate; physical allocation/Drop semantics remain outside logical Vec.

Exact next consumer: finish the concrete AspisR1Stage2.ResumeOps operation
instance and the kernel semantic/weight section content refinements, consume
it in OraclePortCkptAbiSourceFields.successful_fields with the explicit
Prepared/Accumulator transport, then construct the source-stage theorem at
OraclePortCkptAbi5Stage.reached_stage through strictStage. Its allowed
external premises are S2S10CallerBinding and S1S7S8StateProvenance, with the
caller/error scope resolved as above and neither containing observation
equality. Preserve the six ordered reads through
OraclePortCkptAbi5Decision.decision_observation and dV_frozen2. The final
source theorem does not yet exist, so there is no honest verbatim statement
to quote as proved. The stage-1 final statements are quoted verbatim above.

## Focused union and audit

CheckpointBytes3Freeze attempt 1: exit 0, wall 63.49288387503475 s, peak RSS
3408920576 bytes, swaps 0, revision ec6dbabe1. Its 35 axiom reports cover all
33 new theorems plus reached_stage and decision_observation; all standard.
The exact full revision, commands, source/import/object hashes and dependency
fingerprints are in manifest.json and the receipt. This is one focused union
against pinned cached objects, not a coherent frozen-release replay. No
unchanged full regression ran. audit-result.json explicitly records that
source_stage_join_closed and concrete_resume_ops_source_instance_closed are
false. `python3 -B tools/ckpt-bytes3-20261022/audit.py` is the read-only audit.

No shipped source or existing Lean was edited. No frozen ELF rebuild trigger,
SBF build, runtime/adversarial suite, generated certificate aggregation or
wallet cleanup occurred. No local target, binary, .olean or JSON >5 MB is
included. All commits remain local; no push or merge.
