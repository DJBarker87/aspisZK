# Nested four-alpha / twenty-nine-gamma mass bound

Status: kernel-checked as one focused leaf on the capped Tailscale NUC.
Source: [NestedForkExtraction.lean](experiments/NestedForkExtraction.lean).

## Exact endpoint

For finite nonempty outer and inner challenge sets, let `event outer inner`
denote the continuation event, and call an outer challenge forkable when it
has at least four successful inner challenges. `nested_mass_le` proves that
if at most 28 outer challenges are forkable, then

    E_outer E_inner [event] <= 28 / |Outer| + 3 / |Inner|.

`nested_mass_le_of_not_extracted` exposes the intended deterministic bridge:
if 29 forkable outer challenges imply an extraction proposition `X`, then
failure of `X` implies the same mass bound. The proof uses an exact nested
finite mean and an additive exceptional-set argument. It does not assume
independence beyond those displayed fresh finite challenge means.

This is the combinatorial endpoint needed after the checked four-alpha and
twenty-nine-gamma interpolation lemmas. It is not their missing source/game
composition. In particular, this file does **not** prove that actual verifier
acceptance supplies four qualifying alpha continuations at 29 gamma nodes,
that those continuations have the required middle witnesses or common
authenticated C1 support, that payment extraction succeeds, or that the
interactive statement lifts to Fiat--Shamir. Therefore the displayed bound
is not a V8 security level.

## Focused verification

Attempts v1 through v7 timed out while elaborating the final comparison in
`nested_mass_le`; there was no memory pressure and no concrete-field
enumeration. The retained repair gave the intermediate average inequality
and rational fraction inequality explicit types, then combined them with
`linarith only`. This follows the already-green comparison pattern used by
the V7-derived formal development and avoids polymorphic transitivity
elaboration over the nested average expression.

Attempt `nested-fork-extraction-nuc-v8` exited 0 in 3.00 seconds. Peak RSS was
6,892,160 KiB and measured swap was zero. The scope recorded MemoryHigh 8 GiB,
MemoryMax 10 GiB, MemorySwapMax 0 and CPUQuota 200%; Lean 4.32.0 ran with
`-j1 -M9500`. Both 981-entry provenance checks passed and
`PROVENANCE_UNCHANGED=true`. No dependency, package, manifest or concrete
field replay ran.

All five audited declarations depend only on `propext`, `Classical.choice`
and `Quot.sound`; no `sorryAx` or new axiom appears. The two linter warnings
concern unused inherited `DecidableEq` section variables and do not change
the theorem statements.

Transport used only `dombarker@100.108.41.90` over Tailscale;
`HostKeyAlias=nuc.local` selected the pinned SSH host key. The cached runner
retains research pin `289d7356c78a4cd493fe61a54f9548f2a0c11298` and borrowed
V7 source pin `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`; the per-run
manifest separately pins the exact new source and all imported blobs.

| Artifact | SHA-256 |
| --- | --- |
| Source / exact source snapshot | `4247fdc2d50d4c617dc8c9b88c56cab85dbf381251bbb8e81db00327888aefa8` |
| Green olean | `74c42a5f4035452931897a91bd16c81a06c989f1b2225737db778b24c31e7b38` |
| Per-run manifest | `1429167aee299085121cf8108876fd21ef8b4199419ce00ec546f8a3bbd9fbc6` |
| Log | `ac2912e2ae14449675c7aa7e7d4328dd0aadcf7ce61d4a882f64ac8764173ac6` |

## Next consumer

The next substantive theorem must establish the premise that 29 outer
challenges with four qualifying inner continuations imply the same
authenticated C1/payment extraction event. Distinct interpolated quotients
or component messages alone are insufficient: the existing block-support
counterexamples show that separate high-support batches need not yield a
component tuple with shared own support. That source-shaped implication,
not this finite averaging lemma, remains the soundness bottleneck.
