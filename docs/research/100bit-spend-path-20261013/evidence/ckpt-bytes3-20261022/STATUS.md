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
