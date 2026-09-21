# Baseline reuse audit and compact repair boundary

Base 6a08ffc4 plus this changeset. This audit follows the user's instruction
to reuse the optimized baseline and its formal work, not recreate them.
The historical 1,047,041 CU result is a complete baseline transaction; the
R17 primary checkpoint is a different candidate verifier scope. Neither
the scopes nor the underlying profiles can be silently equated.

## What the source actually shows

The staged R17 SBF manifest retains opt-level=3, fat LTO, one codegen unit,
overflow checks and selected-v7-kernels. Its flags include grouped/sparse,
prepared field arithmetic and query features. However a flag does not imply
that the new caller reaches the corresponding optimized function.

The old performance_verifier routes to structured_weights::prepare/relation.
That path binds a compact, verifier-derived Description, evaluates its
ordinary terminal through block/grouped kernels, and keeps fresh query
covectors separate. Its dense differential path is host-only.

R17 instead routes through r17_host_relation, builds two full weight vectors,
applies basis-dual and chord transforms, hashes both expanded vectors before
tau, and puts both into add_dense. Its diagnostic second full verifier pass
also runs on SBF. That second pass explains a remaining heap failure, but
not the 24.47M primary checkpoint, which precedes it. In R24, preparation
from the first original-start marker through prepare-end costs 19,892,834 CU.
This is an implementation cost, not a lower bound for private verification.
R28 restores primary acceptance after the R27 temporary-buffer heap
regression, at 24,208,293 CU (264,376 below R24), by reusing final Vec buffers
with the retained prepared affine arithmetic. The second reference pass
still exhausts heap. Preparation remains 19,892,834 CU: this confirms that
kernel reuse helps but does not replace the compact-structure work below.

## Reuse map

Paths below are under v8-no-work-100-20260907/experiments unless qualified.
Proofs retain their documented algebra/source-model boundaries, not a newly
claimed Rust/LLVM/SBF or privacy theorem.

| Existing component / proof | R17 status and required work |
| --- | --- |
| Selected field and semantic kernels; prepared multipliers | Present in retained source/features. Audit actual callers separately from enabled flags. |
| circle_norm.rs, joined_inverse.rs, line_norm.rs; ChordNorm, CircleNorm, JoinedInverse, LineNorm, QueriedInverse, SharedInverseReplay, LineNormBuffer | R27 restores the actual selected-point line-inversion caller. Same chord/points/derived lines feed both quotient channels. No new inverse formula. |
| quotient_fold.rs; QuotientFold.fold_identity and prepared_powers | R27 reuses the unchanged Prepared object across both channels. Identity covers arbitrary numerators, including invalid proofs; no honest-proof premise. |
| affine_primal.rs; AffinePrimal raw injection/cast/range results | R27 enables the existing v8_affine_primal route for both final vectors. Source copied unchanged, not reimplemented. |
| R17 InPlaceDenseFold storage lemma | R28 reuses its abstract write-order argument for owned final buffers and retains the existing prepared affine arithmetic. Actual Vec/source correspondence remains separate; 240 finite comparisons and allocation-retention checks pass. |
| WeightAccumulator::weight_prefix and qm31_sum_products4; TerminalQuery prefix_shared, halved_vector_indexed, partial_raw_result, four_product_range | R27 uses the existing four-entry path and dot helper on each mixed dense/query accumulator. The helper's documented fallback remains; this does not yet separate ordinary/query components. |
| structured_weights::block_terminal_impl/grouped_terminal and sparse_grouped.rs; FusedRows.fuse_through_linear_transport, BlockHorner, ArithmeticRewrites | R29–R35 connect the ordinary compact terminal through the repaired basis, including sparse corrections and caller-owned storage. Existing generic algebra is reused; Rust/source correspondence remains separate. Retaining dense preparation makes the combined route slower than R28. |
| R16 TransportDual.inverseTransport_dot and transportDual_forward_dot; R17 SourceOriginalWeights.original_weights_transported_pairing | Reuse as the basis/chord bridge. Do not reprove generic inverse-dual pairing. The new compact evaluator must implement this SAME functional. |
| shared_gamma.rs; SharedGammaDots | Present but R17 prepare still uses separate Horner batches and opened reconstructs query powers. Caller integration remains, not a claimed enabled optimization. |
| semantic_carry.rs / semantic_boundary.rs and their existing proofs | Audit the R17 semantic caller before enabling; the changed initial G claim must remain correct. No wholesale transplant of old profile-specific initial-state behavior. |
| leaf_record.rs, auth_order.rs, byte-equivalent Merkle helpers and retained proofs | R17 opening caller still uses its older direct leaf/authentication sequence. Preserve canonical validation and failure chronology when reconnecting these. |

For joined inversion, reuse JoinedInverse.checked_correct,
joined_eq_separate and shared_product_seeds. LineNormBuffer.inverseLines_eq_checked
already connects the modeled internally constructed point/line/norm buffers
to checked inversion. This is stronger reusable evidence than assuming that
an arbitrary independently supplied line buffer happens to match the points.
The actual caller uses Selected::new, points(), and lines derived from those
same points; they are not prover hints. R27's fallback leaves logical
canonical/domain checks in their old per-record order. Resource/heap failures
remain separately observable and are not covered by that claim.

## Compact representation: exact next boundary

R17 hashes expanded weights before tau. Replacing those bytes with a compact
Description changes the transcript/challenges. It must be a separately
versioned research profile with new fixtures and source/oracle analysis,
not advertised as byte-identical R17 or justified by reusing an old CU number.
First establish that the fixed descriptor determines every coefficient,
interpolant subtraction and image-residual coefficient of BOTH channels.
Then use the existing transported pairing to construct the compact terminal.

R29 now compiles the exact linear decomposition and composes the old fused-row
theorem with the repaired transport; actual source controls pass. See
[R17_COMPACT_TRANSPORT.md](R17_COMPACT_TRANSPORT.md) for exact targets, pins,
retained failures and the remaining sparse-contraction obligation. This is
not yet an integrated compact verifier or a new CU measurement.

R30–R33 subsequently implement weighted sparse corrections and the complete
ordinary-channel compact terminal, then connect it to the primary research
verifier while retaining expanded transcript binding, image/query terms and
the G/reference paths. See [R17_WEIGHTED_COMPACT.md](R17_WEIGHTED_COMPACT.md)
for source controls, the focused grouping proof and storage/build failures.
This does not yet eliminate dense preparation or compact the G channel.

R34/R35's [consumed workspace](R17_COMPACT_WORKSPACE.md) restores SBF
primary acceptance, but at 25127686 CU versus R28's 24208293. This is a
retained regression, not the selected fastest implementation. The priority
is now compact preparation with explicitly versioned descriptor binding.

For the inactive indicator, the dual transport yields only the pivot
coordinate: inactive non-pivots have 1-1=0, active rows have 0, and the
pivot has 1. R29's inactive_to_pivot now proves this specialization of the
retained transport definition under the explicit inactive-pivot premise. It is a
useful simplification, not permission to discard the pivot/image residual.

The source permutation is not identity: the first 89 slots contain legal
pads from rows 13..478; non-pads are packed after them. It becomes identity
at slot 479. This fixed reindexing is precisely why the baseline's tensor
terminal cannot be used unchanged. Reuse its linear/tensor/grouped lemmas
to derive the reindexed contraction, retaining the pivot correction.
The G channel additionally requires its existing 271-coordinate Vandermonde
functional; local invertibility does not justify replacing that map or
reintroducing the disproved first-271 direct placement.

No new hiding assumption, old H1 schedule search, production change, dropped
negative regression or privacy/soundness closure follows from this audit.
