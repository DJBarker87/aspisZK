# Sampler arithmetic, D18 weights, and the two-pad repair

This checkpoint adds checked arithmetic components; it does not close the R1
source, semantic, shared-oracle Fiat--Shamir, or zero-knowledge gates. Runtime
source and binaries are unchanged. The previous query checkpoint is
`a7ff42dc8068119ba1aea4e7bda471a01177b5be`.

## Sampler algorithm at the Nat/list level

The optimized Rust sampler converts a 32-byte block into eight radix-2^32
limbs, repeatedly divides by P = 2^31 - 1, and collects four or eight low
base-P digits. Its nonzero challenge sampler then adds the remaining quotient
plus one, with an additional one if the first addition wraps.

`lean/SamplerNatModel.lean` now composes the following components rather than
assuming their modular output laws:

| Component | Checked statement |
|---|---|
| `SamplerLongDivision`, `SamplerPass` | A high-to-low long-division pass preserves the value invariant and returns the numeral's quotient and remainder. |
| `SamplerDigits`, `SamplerRanking` | Repeated low-digit extraction represents the remainder modulo P^n; the canonical tuple agrees with the finite positional ranking equivalence. |
| `SamplerAddDigits`, `SamplerAddBridge` | The explicit recursive carry pass preserves value and length; adding the extra one after a wrap implements `carryResult`. |
| `SamplerCarry`, `SamplerArithmetic` | The single end-around carry yields `x mod (P^n-1) + 1` under the proved quotient bound. |
| `SamplerMachineBounds` | The chosen 32-bit radix gives dividends below 2^63 and quotient limbs below 2^32; for x < 2^256 the remaining eight-digit quotient is at most 256. |
| `SamplerNatModel` | The four/eight-digit results have positional values `x mod P^4`, `x mod P^8`, and `x mod (P^8-1)+1`, respectively. The gamma digits are canonical and their value is strictly between zero and P^8. |

These are natural-number and list models. The 32-byte packing, UInt shifts,
bitwise OR, casts, mutable array traversal, repeated-pass storage, and concrete
QM31/WideExact tuple decoding still need correspondence proofs. The modulo
probability bounds in the preceding checkpoint are not silently promoted to
Rust sampler laws by these results.

## D18 point weights

`D18PointWeights.lean` proves that the ten Boolean row factors are exactly the
five radix-four tensor factors for tau = [3,4,2,0,1]. It reindexes ten bits as
five pairs and uses the checked D18 digit identities; it does not enumerate all
1,024 coefficient positions.

The root's dependent check `D18RawPoint.lean` composes this identity with the
existing R1 raw-row linear map. Its result is the explicit Boolean row sum,
with coefficient messages transported by the involution. This handles the
coordinate ordering for arbitrary supplied points at the mathematical level.
It does not identify the Rust point constructor, inactive mask, Libra row,
circle weights, or complete semantic context.

A direct import of the historical `R0.OpeningDefinitions` was attempted for a
stronger named-definition bridge. That import loads unrelated broad proof
modules and exceeded the fixed Lean interpreter threshold: exit 134,
6,209,616 KiB peak RSS, no swap. The cap was not raised. The earlier SemView
attempt had a missing cache object. Both failures, an exact uncompiled source
snapshot, a known draft proof-orientation issue, and a small-module extraction
plan are preserved under `evidence/lean-d18-opening-weights-20261013/`.
The failed draft is excluded from the successful manifest. The smaller
`D18RawPoint` result is stated on its own explicit definitions; it is not a
replacement assertion that the historical semantic bridge compiled.

## Algebraic privacy repair

`DualPadQuadratic.lean` upgrades the two scalar correction identities to a
rootless quadratic extension. For g = gamma^27 and d = gamma^28 it proves

    det(g, d) = gamma.im * Norm(g).

When gamma.im is nonzero, gamma and g are nonzero and so is that determinant.
The explicit coefficients u and v lie in the base field and cancel any
coefficient gamma^lane after embedding into the extension:

    gamma^lane + gamma^27 * embed(u) + gamma^28 * embed(v) = 0.

Thus the proposed two-pad repair has a checked algebraic justification for
challenges outside the base field. It does not prove the legal mask-space
image conditions, the efficient simulator, a good-challenge density bound,
the abort/publication behavior, or commitment hiding. The exceptional
base-field challenge event remains in the privacy accounting.

## Evidence and review

The root inspected the worker sources and compiled dependent sampler and D18
compositions on the pinned NUC. Each successful focused target used
MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0 and Lean's 5,000 MB interpreter
threshold. Every principal declaration has a printed axioms audit, containing
only the usual `propext`, `Classical.choice`, and/or `Quot.sound` axioms.
No full security theorem is asserted.

`evidence/lean-sampler-transport-chain-20261013/manifest.json` pins the fourteen
successful targets, including the prior D18 transport dependency, with exact
source hashes, selected attempts, timings, peak RSS, zero-swap receipts,
axiom outputs, and source/object dependency inventory. Its validator also
checks the tracked compiled-object archive so validation works in a fresh
checkout. Failed proof-plumbing attempts are retained beside each target;
they are not included as successful axioms evidence. This is a focused
checkpoint, not a complete frozen formal release or a reconstruction of all
historical cache provenance.
