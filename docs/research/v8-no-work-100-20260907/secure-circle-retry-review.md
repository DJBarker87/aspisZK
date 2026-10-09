# Secure-circle sampler: bounded decoder and kernel

Source parent: `ce36c58168987142d3f07e5d8cba00fb7b1dd05b`.
This is a sampler continuation, not a completed V8 soundness claim.

## Checked deterministic wrapper

`DistinctCircleDecoder.decodeDistinctPrefix` wraps the existing V7
`decodeSecureCirclePrefix circleMap 3` with the selected outer retry
grammar. Outer fuel is instantiated at three for the V8 second point.
An inner failure immediately returns None; only a successful duplicate
point retries. The returned record preserves the remaining raw block list.

Checked theorems establish that every successful inner result has a mapped
point, every successful outer result maps to a point different from the
first, and appending unread blocks cannot change a successful result.
The extra map match in the model is justified by the first theorem, not
an unverified acceptance premise. An inner failure is explicitly proved
to abort even when outer retry fuel remains.

The equality decision uses Lean's classical proposition decision for
byte-function records. This is a mathematical control-flow model, not an
executable replacement sampler or a compiled Rust-to-Lean translation.
The per-record blocksUsed/wordsUsed fields remain the existing decoder's
fields; they are not mislabeled as total consumption across nested calls.

## Checked history-dependent mass recursion

`BoundedRetryKernel.mass` follows an ordinary draw that returns either
None (immediate abort) or a value and updated history. Accepted values
return immediately; rejected successful values recurse. For a fixed
target it proves:

    mass after n attempts = u * geometric(n,r)
    mass after 3 attempts = u * (1+r+r²).

Here u is the one-step accepted-target mass, and r is the one-step
successful-rejection mass. Both laws must hold at EVERY reachable
history (the theorem asks for every history), not merely at the initial
state. History may depend on all prior random draws and rejections.
This is stronger than freezing a complete transcript, but it does not
derive fresh randomness from distinct labels.

The None case contributes zero and is never retried. Consequently the
formula does not flatten the two retry layers or condition on eventual
success. The caller still must connect this recursive mass to the actual
finite raw-tape decoder and discharge the one-step laws using the exact
ordinary sampler. This interface is explicitly conditional, not a source
probability certificate. There is no new quantitative OOD term yet.

## Source interfaces being joined

`SecureCircleParameterDomain` separately establishes the actual accepted
parameter set and cardinal P⁴−P². `SecureCircleParameterInverse` now proves
parameter recovery and byte-level point injectivity from actual successful
map calls, reusing four V7 codec proofs. Thus the distinct wrapper excludes
one prior parameter, not both signs sharing its x-coordinate. These are
prerequisites to replacing the previous unaveraged OOD
indicator, not permission to erase it already.

The cache preflight found a retained V7 SemanticTranscriptBridge artifact,
but importing its whole closure would introduce 31 modules and 12 native
boundary artifact variants different from the frozen overlay. It was not
imported. The needed four codec-inverse proof bodies are reused narrowly
from the pinned V7 source instead, preserving existing import provenance.

## Focused evidence

Same inherited NUC workspace/runner289d7356 over Tailscale. Lean
`-j1 -M9500`, MemoryHigh8GiB/MemoryMax10GiB/SwapMax0/CPUQuota200%.
Each imported-source/output manifest passed before/after its green run.

- DistinctCircleDecoder v2: exit0, 2.92s, RSS6,674,044KiB, zero swaps,
  four standard-only audits. v1 failed solely because byte-function point
  equality lacked a decision instance (2.71s, RSS6,642,024KiB); adding the
  explicit classical decision did not change the mathematical predicate.
- BoundedRetryKernel v2: exit0, 2.97s, RSS6,701,840KiB, zero swaps,
  four standard-only audits. v1 checked the declarations but failed at a
  missing section terminator (2.92s, RSS6,668,408KiB). Only the terminator
  was added; v1 is not credited as a successful file build.

Commands:

    bash run_higher_y_nuc.sh <scope> DistinctCircleDecoder distinct-circle-decoder-nuc-v2
    bash run_higher_y_nuc.sh <scope> BoundedRetryKernel bounded-retry-kernel-nuc-v2

Decoder source `092d83bd281d5e3c6299b50a744c0875976386abea962bc093e7459a3df886f6`;
olean `a27c4050992389f77063b51c623226d597f6491e8b072093ff1540f9170d7115`.
Kernel source `78d6ac88c22571570e2b7407949011e0b77795377446dce48534ae7a283d0da8`;
olean `629a0562cfcde78de835715bf4abe74d747fb3e331b4310b207a3f49c6c19021`.
All attempt sources/logs/manifests retained. No production, wire, verifier
or deployment changes; proof body maximum40282, grinding credit zero.

Next is the joint adapter: exact ordinary successful/abort law → actual
circle decoder mass → distinct-second wrapper mass, with arbitrary
intervening answer absorption and all stopping prefixes represented.
Only then can its OOD bound be composed with CausalQuadraticReduction.
Higher-degree recovery, checked extraction, full-view privacy and the
resource-bounded FS/source coupling remain open.
