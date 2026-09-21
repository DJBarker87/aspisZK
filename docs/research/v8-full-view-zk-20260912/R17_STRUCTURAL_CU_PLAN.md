# Exact-map structural optimization boundary

Current priority: [baseline reuse audit](R17_BASELINE_REUSE.md). Restore and
compose existing optimized kernels/proofs before inventing replacements.
The historical FFT candidate below is no longer the next primary task:
R25's DIF implementation regressed CU, and R26 remains host-tested only.
R27 restores several existing opening/folding kernels. R28's owned affine
buffers restore primary acceptance at 24,208,293 CU; the unchanged second
reference pass still exhausts heap and supported-budget cases still fail.
The larger target remains compact functional preparation through the repaired
basis, with an explicit transcript-version boundary for descriptor binding.
R29's [compact transport bridge](R17_COMPACT_TRANSPORT.md) now proves the
exact correction formula and reuses the old fused-row theorem; focused
source controls pass. R30–R33 implement that sparse contraction and connect
the ordinary-channel terminal; [exact boundaries](R17_WEIGHTED_COMPACT.md).
G contraction, dense transcript binding and complete source refinement remain.

R36 now restores verifier-derived compact descriptor binding in an explicitly
new research-v2 profile and removes ordinary dense preparation. Its fresh
fixture reaches primary SBF acceptance at 20591164 CU. See
[compact preparation](R17_COMPACT_PREPARE.md). G expansion/dual/chord still
costs 15247174 CU and is now the primary structural target. Full-program
reference heap failure, source refinement and security obligations remain.

Source base: e32bac9b plus R14/R15 staged research changes. This is an
implementation plan and algebraic derivation, not a compiled Lean theorem,
completed CU measurement, or new privacy claim.

## Preserve the map before changing the protocol

The expensive source operation in `tools/r17_mask_workspace.rs` is
`w[j] = sum_i a[i] * (i+1)^j`, for 271 coin weights and 1024 outputs.
Its dense implementation is not a lower bound on verification cost.
The R15 intermediate experiment fixes the public matrix in read-only storage
and batches four canonical M31 products per reduction. It still does a dense
matrix multiply and is not the final structural optimization.

A faster exact route follows directly from the geometric-series identity.
Work modulo X^1024, put n_i=i+1, and define

    D(X) = product_i (1 - n_i X)
    N(X) = sum_i a[i] product_{k != i} (1 - n_k X)
    W(X) = N(X) / D(X) mod X^1024.

Then coefficient j of W is exactly the current w[j]. D(0)=1, so the
inverse exists without any challenge nonzero condition or rejection event.
All D coefficients and the truncated inverse are fixed base-field constants.
No change to the mask distribution, basis transport, transcript or proof
format is required by this identity.

Compute N with a balanced product tree. Each leaf has D_i=1-n_i X and
N_i=a[i]. Merge by D=D_left D_right and
N=N_left D_right + N_right D_left. The denominator tree is precomputable;
only numerator combinations depend on the actual coin weights. Use a fast
convolution kernel for both the tree and final multiplication, not a new
quadratic implementation hidden behind polynomial notation. The four M31
components share all fixed polynomial data. An ordinary radix-two transform
cannot silently assume roots in M31; its multiplicative group has only one
factor of two. Reuse/justify suitable extension-field or circle arithmetic,
or measure a bounded-memory Karatsuba alternative.

Next exact proposition: for every canonical source coin vector, the
implemented product-tree numerator and truncated convolution produce the
same 1024 canonical QM31 encodings as the retained power-sum implementation.
This includes arithmetic overflow bounds, truncation indices, workspace
ownership and the exact basis/order consumed by the transcript. First test
the convolution, then one tree level, then full map and actual proof, before
SBF profiling. Keep the direct implementation as a host reference.

## Aligned bases and sparsity constraints

The retained sparse chord scatter, low-quotient support and active-row
geometry are useful exact facts, not permission to remove the second channel.
See R17_MINOR_BLOCKS.md, R17_ACTIVE_MINOR.md and the source tests in
crates/aspis-prover/src/r17_two_channel.rs. The old single-functional negative
and first-271 direct-placement negative remain required.

The current source absorbs both expanded ordinary weight arrays before tau.
A symbolic accumulator can avoid materialization after absorption, but it
cannot simply omit those bytes. Streaming the exact bytes needs an equivalent
hash adapter; replacing them with a compact descriptor is a new transcript
profile and must be justified separately. A sparse replacement mixing map
likewise needs its joint observation/posterior argument, not merely full rank
on its own. The first-271 placement regression already demonstrates why.

After G, profile the still-expensive ordinary tensors and two chord duals.
Exploit shared tensor factors and sparse correction terms, retaining exact
fixed-basis transport. Do not rerun H1-only schedule searches. Ultimately
remove the runtime dense reference pass only through an explicitly reviewed
equivalence/release decision; the current research probe still executes both
and compares their outcomes.

Resource failures, full-transcript privacy, shared-oracle correspondence,
retry/publication behavior and soundness remain separate outstanding gates.

## Implemented first experiment

R16 (base 0e8af97d plus its changeset) now implements the tree and a 2048-point
CM31 convolution. Fixed tables are generated with optimized Rust. Root order,
inverse denominator, convolution edge, complete weight references and actual
host proof gates pass. See R17_REPAIR_CU.md for exact evidence. The first tree
version still uses schoolbook numerator merges; it is not yet a fully fast
product-tree implementation. Its second original-weight stage costs 24.54M
CU, down from 26.65M, but extra workspace causes earlier SBF heap exhaustion.
This is a measured partial optimization and a retained resource regression,
not a completed repair, full source proof, or evidence of budget feasibility.

R17 additionally reuses the G output for both numerator buffers and the
consumed tensor scratch for G output. Its attempted four-product tree
batching regresses CU and is explicitly rejected in favor of original merge
order (R18), retaining the allocation savings and exhaustive coin-basis gate.
The new R17 markers attribute 13.37M CU to the FFT section including buffer
setup, both components, pointwise products, normalization and output copies;
this is now a concrete optimization target, not an inference from total CU.

One exact arithmetic candidate for the next butterfly implementation: fuse
complex multiplication with addition/subtraction before canonical reduction.
For canonical M31 limbs, P=2^31-1, let A=v.a*w.a, B=v.b*w.b,
C=v.a*w.b and D=v.b*w.a as u64 integers. The four output limbs can be
reduced directly from

    u.a + A + P^2 - B,       u.b + C + D,
    u.a + P^2 - A + B,       u.b + 2*P^2 - C - D.

These are nonnegative, below 2^64, and have exactly the required residues.
This eliminates intermediate complex-result reductions and canonical
add/subtract steps. Check bounds and equality independently against source
CM31 operations (including maximal limbs), then the whole existing basis
gate and actual proof, before measuring. Keep trivial twiddles explicit.
R19 now implements this butterfly, specializes the public index-zero twiddle,
and uses the existing power-of-two inverse normalization. The focused bounds
leaf compiles; all finite arithmetic/basis/actual-host-proof gates pass. The
FFT marker interval falls from 13.37M to 8.53M CU. See R17_REPAIR_CU.md for
exact evidence and proof limitations: the natural-number bounds do not yet
establish source reducer correspondence or whole-transform correctness.
R20 implements scalar multiply-add in the original scatter order, retaining
the failed diagonal-batching evidence. Its tree interval is 5.46M CU versus
7.91M before. Reusing weight serialization storage saves another 16 KiB and
lets the honest SBF execution complete openings and their reference check.
R21 implements in-place dense dual folding and stack injection scales, with
100 differential folding schedules and a compiled generic storage-model
proof. The honest SBF execution now reaches primary terminal acceptance at
about 30.38M diagnostic CU; the unchanged second reference pass subsequently
exhausts heap. Neither the full-program resource failure nor the above-budget
primary cost is a release result. Ordinary tensors and both G transform
sections remain major CU targets. Do not remove the reference silently or
replace this scope with an easier verifier when reporting the result.

R22 shares complementary tensor children using p*(1-z)=p-p*z. The complete
logical-tree identity compiles in Lean; actual source-weight and host-proof
controls pass. The primary SBF terminal checkpoint falls to 27.92M CU, while
the full double-checking program still fails in the reference pass on heap.

Next structural candidate: accelerate only the balanced numerator-tree
merges at widths 64,128,256. Keep small and uneven merges (notably the final
256+15 split) on the existing scalar scatter path. A balanced width-s merge
has numerator degree at most s-1, so an s-point cyclic transform can compute
it without aliasing. Both child denominators are fixed and their spectra
can be precomputed; compute N_left*D_right + N_right*D_left pointwise and
inverse-transform. Reuse the existing CM31 workspace, moving its allocation
before the numerator rather than adding another buffer. Branch selection
must depend only on this fixed public tree shape. Validate smaller transform
roots/normalization and each selected merge against the current scalar merge
before the complete basis and actual-proof gates. This is a planned exact-map
optimization, not an implemented or measured speedup; no new mixing map or
hiding assumption is justified by this plan.

This candidate is now implemented as R23a. Its seven selected merges pass
838 direct controls; the whole-map/proof gates pass. It saves only 0.24M
primary CU because generalizing the transform regresses the final FFT.
R24 then specializes fixed sizes/directions and quarter-turn twiddles,
retaining the generic transform as a host reference. All focused gates pass.
The primary checkpoint is now 24.47M CU (R22: 27.92M). G-tree/FFT intervals
are 3.93M/6.61M. Exact evidence and the retained regression are in
R17_REPAIR_CU.md. No universal transform/source proof follows from these tests.

Next exact-map structural candidate: align forward/inverse spectral storage
so convolutions do not reorder the same coordinates repeatedly. A forward
DIF transform can emit bit-reversed frequencies and an inverse DIT can
consume them directly, provided every fixed denominator/inverse spectrum
uses exactly the same permutation. Preserve the current generic transform
as a reference; compare every supported length/direction, selected node,
whole G basis and actual proof before measuring. This is not implemented.
The present fused DIT butterfly cannot simply be reused as a DIF butterfly:
the twiddle multiplies a different intermediate. Derive its arithmetic and
canonical bounds before implementing a fused DIF path. Small/sparse merges
must remain direct. Avoid changing the fixed mixing map merely for a faster
transform: that would be a new profile requiring renewed joint-observation
analysis, not an equivalence optimization.
