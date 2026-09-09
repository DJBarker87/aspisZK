# Concrete interleaved chord reconstruction for the repaired rows

Research-only continuation from
`bc945367d6b0d9a5b4cb2dc5a9ecad8ddcfb33ee`. The worktree started clean;
main and concurrent research are preserved. No Rust, transcript, verifier,
protocol parameter, proof-body or production changes.

Status: the generic linear/interleaving core and selected 1024-coordinate
constructor are kernel-checked. The ordinary row game now receives a concrete
total natural-projection map and a derived transpose identity.
The previously committed
[natural projection proofs](natural-chord-projection-review.md) remain green
and were not rerun.

## The interface this closes

The preceding image/projection result returned two 512-coordinate halves.
`ShiftedRowPrefix.Rows` instead needs a **total linear map from 1024 original
quotient coordinates to 1024 original reconstruction coordinates**. Merely
naming an arbitrary map `reconstruction` does not connect those interfaces.

The new construction is explicit:

```
q[2j], q[2j+1]
  -> natural polynomial halves A, B
  -> full chord product Af, Bf
  -> canonical natural coordinates at width 514
  -> retain the first 512 natural coordinates of each half
  -> interleave them at positions 2j, 2j+1.
```

All stages are linear in q. The conversion uses the maintained proved
inverse matrix; it does not posit an evaluation-system rank. The map is
defined even when the image residual is nonzero. It does not perform
monomial truncation, and no overflow coefficient is assumed zero in its
definition or transpose identity.

[InterleavedChordLinear](experiments/InterleavedChordLinear.lean) reuses the
V7-consumed `V5FriInitialCircleEncoderIdentity` binary index equivalence and
literal even/odd coefficient maps. It derives the interleaving projections
and dot-product split, without changing the committed basis.

[InterleavedChordAlgebra](experiments/InterleavedChordAlgebra.lean),
[InterleavedChordPair](experiments/InterleavedChordPair.lean) and
[InterleavedChordFull](experiments/InterleavedChordFull.lean) stage the symbolic
linear algebra before the selected-width specialization. The final full-pair
linear map has the literal chord polynomial as its `toFun`, with linearity
proved from the generic multiplication-map identities; this avoids unfolding
512-term polynomials during definitional comparison.

[InterleavedChordRows](experiments/InterleavedChordRows.lean) constructs the
selected `reconstruction` linear map, its exact even/odd output, and its
evaluation using the maintained `initialP0/initialP1` polynomial convention.
For `q[1023]=0`, `b*q[1022]-c*q[1021]=0`, nondegenerate `(b,c)`, and a circle
point, that evaluation equals `(a+b*x+c*y)*Q(x,y)`.

## The ordinary scalar uses that same map

The transpose coefficients are constructed by applying the primal map to
coordinate vectors and reusing `ShiftedRowPrefix.reify_dot`. A second identity
expresses the original-covector dot product as the full width-514 product
paired with the **zero-padded natural covector**. Both identities hold for
every q, including invalid images.

The `rows` constructor installs this concrete map in `ShiftedRowPrefix.Rows`.
The inherited affine correction and repaired powers `[1,kappa,kappa^2,kappa^3]`
then produce the cubic prior from the four actual original-row errors. There
is no assumed transpose equality and no `inactiveExact` premise.

The checked-slope lemma covers both actual OOD coordinate branches: a
nonzero selected denominator implies `b=y0-y1` or `c=x1-x0` is nonzero. The
field theorem consumes the nonzero denominator enforced by the source's
checked inverse. Translating `try_inv` is not claimed in this leaf.

## What remains separate

The constructed map is the exact coefficient-space operator required by the
source-shaped row game. Equality with the implementation of the sparse carry
loop and optimized structured transpose is still an implementation-refinement
obligation, not inferred from passing honest tests or renamed by the map.

The affine interpolant vector and four original covectors/scalars remain
constructor inputs. Their concrete OOD/challenge/selector construction and
fixing before kappa still have to be connected to the actual transcript.
Only the generic slope guard is specialized here; no OOD-answer correctness
is asserted. Domain-slot instantiation, virtual-quotient support, source
parser/response refinement and whole-game acceptance coupling remain explicit.

No received word is assumed globally polynomial. These deterministic
identities do not construct a covering tuple, acquire authenticated values,
return a checked payment witness, or bound the uncovered accepted mass.
They add no numerical security error and do not alter the existing conditional
row/image ledgers. Raw ideal-game and resource-bounded Fiat–Shamir claims
remain separate, with zero grinding credit.

The proof body remains 40,282 bytes. There are no new verifier operations or
new CU measurements; this turn changes only formal research artifacts.

| Interface | New evidence | Remaining boundary |
|---|---|---|
| Full chord, natural inverse, prefix and low-bit interleaving | Constructed total linear map | Actual Rust carry/conversion loop refinement |
| Image-valid evaluation at a circle point | `message_circle_eval` | Actual stored-domain/slot and source encoder coupling |
| Literal transpose and full zero-padded pairing | `transpose_dot`, `reconstruction_full_dot`, for every input | Optimized structured contraction refines that transpose |
| Affine ordinary scalar with four shifted rows | `concrete_before_prior` | Actual OOD interpolant, original public rows and pre-kappa fixing |
| Nondegenerate chord | `checked_slope_chord` | Source checked inverse produces the stated nonzero denominator |

The next bounded algebra/source experiment is to identify the actual two-entry
OOD interpolant and the actual original public covectors in this constructor,
then connect the structured carry algorithm to the derived transpose. It is
not necessary to assume the received word is a codeword to define that map.

## Reproduction and evidence

Run only changed targets with fresh
log paths, from the repository root:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_interleaved_chord.sh InterleavedChordLinear /absolute/NEW-linear.log
bash docs/research/v8-no-work-100-20260907/experiments/run_interleaved_chord.sh InterleavedChordAlgebra /absolute/NEW-algebra.log
bash docs/research/v8-no-work-100-20260907/experiments/run_interleaved_chord.sh InterleavedChordPair /absolute/NEW-pair.log
bash docs/research/v8-no-work-100-20260907/experiments/run_interleaved_chord.sh InterleavedChordFull /absolute/NEW-full.log
bash docs/research/v8-no-work-100-20260907/experiments/run_interleaved_chord.sh InterleavedChordRows /absolute/NEW-rows.log
```

The runner checks source/olean provenance through the entire retained Aspis
and research import closure, pinned to the research revision and cached
mathlib revision. It records hashes before/after, named axiom audits, exit,
wall time, RSS and swaps; the focused process has `-M7000` and an independent
7-GiB aggregate-RSS stop. No full suite or SBF rebuild is required here.

All five retained leaves have exit 0, unchanged import provenance and zero
swaps. Each listed axiom audit contains only the standard `propext`,
`Classical.choice`, `Quot.sound` subset. The 11 Rows audits include the two
already-checked full-pair identities; their count is not a security metric.

| Leaf / successful log | Wall seconds | Peak RSS bytes | Named audits |
|---|---:|---:|---:|
| [Linear v1](experiments/interleaved-chord-linear-v1.log) | 16.67 | 5,637,111,808 | 8 |
| [Algebra v1](experiments/interleaved-chord-algebra-v1.log) | 18.72 | 5,631,574,016 | 2 |
| [Pair v1](experiments/interleaved-chord-pair-v1.log) | 11.27 | 5,617,041,408 | 2 |
| [Full v3](experiments/interleaved-chord-full-v3.log) | 12.29 | 5,624,020,992 | 2 |
| [Rows v5](experiments/interleaved-chord-rows-v5.log) | 12.13 | 5,635,227,648 | 11 |

Wall time includes page faults; user CPU is about two seconds for each leaf.
These are Lean measurements, not prover, extractor, verifier or CU timings.
The imported source pin is the checkpoint above. The last three selected
runs observed research HEAD `4aaa61e679189b2cf76bfc25c2e3ff8d5c76341e` and
read-only main/cache HEAD `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
The runner validates the exact imported source against the older pin, and
records every research/consumed-Aspis source and olean hash before and after.
Final Rows source SHA-256:
`b79f73c5ee6256caac27e318a127e4c9d0e56473f933266e46c4dae14682c0c1`;
olean SHA-256:
`321111baf1ca250ef72d6ea4c9db5eb8e2a662fa6bcef538943f4fd514f7258b`.

The selected v1 preflight failed at broad definitional conversion under the
200-recursion limit (exit 1, 6.66 seconds, RSS 5,499,289,600 bytes, zero swaps).
Replacing those conversions alone did not suffice: v2 reached the independent
7-GiB guard (exit 137, 23.74 seconds, RSS 7,568,162,816 bytes, zero swaps).
The changed v3 still reached the guard (exit 137, 66.18 seconds,
RSS 7,624,523,776 bytes, zero swaps). No unchanged killed job was retried.
The next diagnostic split used synchronous elaboration, recursion 80 and
2,000 heartbeats: Pair passed, while Full v1/v2 pinpointed the final
composed-map expected-type conversion (exit 1, 24.11/10.67 seconds,
RSS 5,474,631,680/5,473,566,720 bytes). Defining the literal polynomial as
the generic linear map's `toFun` made Full v3 pass at those same low limits.
Rows v4 then exposed only local product-function and transpose conversion
errors (exit 1, 5.68 seconds, RSS 5,490,376,704 bytes). Symbolic generic
application/transpose helpers closed them in Rows v5 at recursion 200 and
5,000 heartbeats. No memory cap was raised. All failed logs are retained
diagnostics, not proof evidence; error-generated `sorryAx` in those failed
audits is absent from every retained successful endpoint.
