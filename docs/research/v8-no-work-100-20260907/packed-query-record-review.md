# Packed query bytes to observed query arithmetic

Research base: `edb199c12fcc41f00330298b95b4736f60ac6f3a`, branch
`research/v8-no-work-100-20260907`. The worktree was clean at inspection.
This continuation owns only new Lean, runner, log and evidence files.

## Actual record and source boundary

Each of 22 records occupies 621 bytes in query-ordinal order, starting at
`11228 + 621*ordinal` in the complete body. Its parts are:

| Part | Record bytes | Decoded values |
|---|---|---|
| C1 | 0..402 | 104 M31 limbs, index `26*slot+column` |
| C2 | 403..588 | 48 M31 limbs, index `4*(4*helper+slot)+basis` |
| Shared salt | 589..620 | 32 arbitrary bytes; not interpreted as field values |

Both packed parts use every bit: `104*31=403*8` and `48*31=186*8`.
There is no spare-bit/padding allowance to reject or silently ignore.
C2 helper order is H/G/D, with each value's limbs in
`(c0.a,c0.b,c1.a,c1.b)` order. The four slots feed circle coordinates
`(+x,+y),(+x,-y),(-x,-y),(-x,+y)`; sorting Merkle entries does not sort the
arithmetic record array.

The active `relation_callback.rs::opened_values_prepared` takes those exact
slices and derives gamma-combined values before leaf hashing/authentication.
The `v8_gamma_wrap` path calls `query_arithmetic::gamma`; its input sizes are
104 and 48 limbs. `v6_onefold::gamma_combine_v6_packed_layer0` is the retained
control. All inputs may be malicious; no helper is treated as an honest zero.

## Reuse and limits

The existing V7 packed-limb decoder is a literal contiguous little-endian
31-bit byte model. Its canonical representation and exact slot/helper/tower
maps are reused. The new generic collection lemma derives the raw integer
represented by each successful result, rather than only observing that a
`Fin p` result carries a range bound.

The optimized Rust decoder instead uses four overlapping u64 loads,
shifts/ORs and a 31-bit mask. Its output-to-bit-model equality is **not** a
theorem supplied by the older V7 packed decoder. The new byte/list projection
must not be described as that compiled machine refinement. Likewise, the
field-level 26+3 gamma sum is not a proof of every delayed-reduction/prepared
multiplier kernel. Existing `GammaDotUnroll`, `M31RangeKernels` and the V7
exact tower kernel facts already cover useful arithmetic fragments; they
are preserved, not replayed or described as nonexistent. Their complete
composition with the active buffer/decoder path remains an explicit
implementation interface.

Parsing does not prove any root, salt or Merkle path authenticates. A
query-ordinal array of decoded records is not automatically a global word
fixed before gamma or before the queries. Distinct labels and canonicality
cannot supply that missing commitment/source coupling.

## Current checked result

`PackedLimbCollect.lean` is green: canonical decoding success determines
the raw integer, complete short-circuit collection determines every limb,
and any out-of-range raw limb rejects. Its focused run took 3.87 seconds,
1,259,814,912 bytes peak RSS, zero swaps and exit 0; four audits contain only
standard Lean axioms (the single-limb integer identity uses no axioms).

`PackedQueryRecord.lean` is now green. Its endpoint is the
actual 621-byte split, complete canonical rejection, raw limb/typed-entry
equality, exact 29-lane gamma recombination and complete-body record bounds.
The first two focused checks are preserved as failures, not certificates:
v1 exposed reduction of the four packed C2 decodes and generic do-bind
elaboration; named V7 assembly/tower lemmas and explicit Option.bind removed
those costs. v2 isolated two broad contradiction searches that attempted to
normalize the packed lists. Their replacement eliminates the specific
`none = some decoded` equality directly. No limit or theorem premise changed.
The successful v3 check took 14.55 seconds, with 5,614,305,280 bytes peak RSS,
zero swaps and exit 0. All thirteen audits contain only standard Lean axioms;
recursive imported source/olean provenance was unchanged.

`PackedQueryResidual.lean` is an **uncompiled dependent draft**, not a
completed source/game endpoint. Its intended construction takes parser
success and the already-proved ordered inverse constructor, derives the
four observed quotient slots and both base inverses, and transports those
six scalar values through the actual circle fold. A second constructed
record retains the arbitrary ordinary/image prior, the residual sign
`final - opening`, and powers `rho^(ordinal+1)` in the shifted query batch.
The caller supplies no quotient, fold, or residual correspondence equation.
However, the whole leaf has not passed the kernel; downstream declarations
reported with `sorryAx` in its failed compiler logs are **not certificates**.

The focused failures are retained. v1–v3 reached excessive reduction while
matching expanded concrete folds and Fin256 query-injection expressions.
The v4 constructed `FoldInput`/`CertifiedInjection` split reduced this to
two base-inverse field equalities. v5–v8 tried explicitly normalizing their
Bool branch and using a generic six-field equality theorem; the selected
application still exceeded the same limit. The v7 diagnostic prints the
exact goals and already-derived scalar facts. Finally, v9's direct equality
elimination exposed the hidden reduction graph: at `cases invx`, Lean
unfolded QM31 inversion into nested `QuadraticAlgebra.norm`, `ZMod.gcdA`
and concrete M31 modular arithmetic. This is a symbolic-elaboration blocker,
not a disproved identity or a soundness counterexample. v9 exited 1 after
9.72 seconds, with 5,577,392,128 bytes peak RSS and zero swaps. No limit was
raised and no further proof job was launched after that result.

The next remedy is an explicit-argument abstract bridge or an opacity
boundary **below the exact-field inversion instance**, not more concrete
unfolding. Successful parser/slot subdeclarations appearing in a failed
whole-leaf log are not promoted to a separately completed module.

## Exact completed dependency/status map

| Interface | Evidence and scope |
|---|---|
| Raw integer to canonical limb; complete collection or rejection | Kernel-checked `PackedLimbCollect` |
| 621-byte list to all 104 C1 and 48 C2 canonical limbs, salt and exact source indices | Kernel-checked `PackedQueryRecord.success_exact`, entry and bound lemmas |
| Successful decoded entries to the raw-byte 29-lane mathematical gamma sum | Kernel-checked `combined_eq_raw` and `combined_eq_scalar_power`; arbitrary malicious leaf values allowed |
| Complete-body record lookup, ordinal offset `11228+621*i` | Kernel-checked bounds from the existing `CanonicalRelationInput.parseFixed` success predicate |
| Parsed local records through checked inverse, fold and shifted-rho input | Uncompiled `PackedQueryResidual` draft; final failure explicitly retained |
| Optimized four-u64 loads/shifts/ORs/mask to the literal V7 bit decoder | Still a machine/source refinement obligation |
| Prepared powers, delayed reductions and tower operations to the mathematical gamma sum | Existing useful V7/research arithmetic lemmas, not yet a complete active-path composition |
| Decoded observed records to the fixed authenticated oracle used by a causal game | Separate authentication/source coupling; not implied by parsing |

The V7 reuse is exact at the byte-bit specification, slot/helper indices,
canonical embeddings and four-limb tower assembly. The old V7 query count,
transcript sampler, work stages and non-interactive resource laws are not
used to certify the V8 q22 transcript.

## Reproduction and provenance

The [machine-readable evidence](packed-query-record-evidence.json) records
the target, source/olean hashes, every success/failure log and measurement
scope. Successful logs are
[limb collection](experiments/packed-limb-collect-v1.log) and
[complete record](experiments/packed-query-record-v3.log). The final dependent
failure is [v9](experiments/packed-query-residual-v9.log), with the narrow
[goal diagnostic](experiments/packed-query-residual-diagnostic-v7.log)
preserved separately.

For a justified changed target or missing artifact, from this worktree:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_packed_query_record.sh PackedLimbCollect /tmp/packed-limb-recheck.log
bash docs/research/v8-no-work-100-20260907/experiments/run_packed_query_record.sh PackedQueryRecord /tmp/packed-record-recheck.log
```

Do not replay the unchanged successful leaves merely to reproduce this
report. `PackedQueryResidual` uses the same runner but is currently expected
to fail; fix the isolated symbolic boundary before rerunning it. The runner
refuses an existing output log and runs targets serially, not as a package
replay. Each actual run used an explicitly allocated serial build slot.

Lean is 4.32.0 (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`), arm64 macOS.
The runner obtains the pinned cached Lake environment, then invokes the
selected Lean leaf directly with `-M7000`. An independent process-tree RSS
guard stops at 7 GiB; this macOS guard is not a Linux cgroup or a promise
that swapping is disabled. All recorded runs observed zero swaps. Wall time
and RSS above measure the focused Lean child, not a verifier or prover.

Borrowed formal sources are checked individually against
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`; mathlib is
`81a5d257c8e410db227a6665ed08f64fea08e997`. The mutable main/cache HEAD is
recorded in each log but is not substituted for that source pin. Imported
source/olean hashes are recorded before and, on success, after compilation;
new green dependencies are explicitly pinned in
`experiments/packed-query-new-pins.sha256`. Main and concurrent agents' work
were not modified.

## Unchanged contract

No source operation, wire field, salt, commitment, transcript call or protocol
parameter changes. Maximum proof body remains 40,282 bytes. No new soundness
probability is assigned: raw causal recovery, full-view privacy, actual
resource-bounded Fiat–Shamir extraction and complete-transaction CU remain
separate gates. V7's q16 and work-stage laws are not imported into q22.

The next bounded source experiment should first finish the explicit scalar
inverse abstraction above. After that, prove one 31-byte/eight-limb decoder
block equivalent to the literal bit model, including all eight word-crossing
offsets and the all-ones noncanonical value, before composing all 19 blocks.
Neither step supplies authenticated-global-word identity on its own.
