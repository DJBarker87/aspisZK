# Exact-map structural optimization boundary

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
This is an unimplemented candidate, not a measured speedup or compiled lemma.
