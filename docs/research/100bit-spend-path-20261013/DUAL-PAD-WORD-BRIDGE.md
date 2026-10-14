# Whole-word two-pad correction

The quadratic correction now lifts from one field element to an entire word.
This is a checked algebraic step in the proposed privacy argument. It is not
a zero-knowledge theorem or a proof of the required mask ranks.

`DualPadWord.correction` takes a base field K, extension E, a common K-linear
subspace B of words, and a linear map `raw` for the observations that each
individual lane must preserve. For each semantic difference `delta c`, it
requires an explicitly supplied noise word `noise c` such that both words
belong to B and `raw (noise c) = raw (delta c)`. It does not produce these
preimages or assume their existence implicitly.

Given coefficients satisfying `a c + g*u c + d*v c = 0` in E, it constructs

```
repairU = -sum_c u c * (delta c - noise c)
repairV = -sum_c v c * (delta c - noise c).
```

Both repairs remain in B and have zero raw observations. The gamma-batched
noise plus the two repairs equals the entire original batched difference,
point by point. Consequently every fixed deterministic observation of that
word is equal as well; this implication is stronger than equality on a
particular finite sample of PCS outputs.

`DualPadLift` applies the previously checked `DualPadQuadratic.pad_correction`
with `g = gamma^27` and `d = gamma^28`. Its premises retain the rootless
quadratic extension and `gamma.im != 0`. The latter means gamma is outside
the base field; it is not guaranteed merely by the sampler excluding zero.

The remaining privacy work is concrete. The legal tape and its embeddings
must be identified with the subspace model. In particular, original C1
lanes are M31-valued while the pads are QM31-valued: a common ambient
QM31-linear pad space does not prove that arbitrary QM31 combinations are
legal C1 masks. Eligible C1 noise must be produced separately with its
original field restriction. The exact raw map must cover every disclosed
individual-lane value. Universal raw preimages, the pure-mask Chain0 image,
and the actual R1 payload identities remain open. An efficient public-input
simulator and the salted-commitment/random-oracle privacy argument are also
still required. See [the privacy construction](PRIVACY-RANK-PATH.md).

The focused NUC runs passed in 1.11 s (`R1DualPadWord-n`) and 1.40 s
(`R1DualPadLift-a`), at 1,809,636 and 2,152,392 KiB peak RSS. Both used
4G/6G/zero-swap scopes. The [combined evidence](evidence/lean-privacy-opening-20261014/README.md)
records exact sources, receipts, objects, and axiom audits.
