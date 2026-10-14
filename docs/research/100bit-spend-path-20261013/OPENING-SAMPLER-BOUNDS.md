# Independent-answer opening bounds

`OpeningSamplerBound.lean` applies the existing modulo-counting theorem to
the concrete R1 opening bad sets. It reuses `ConcreteBinding`'s cardinality
bounds, including the literal joint list and both fold comparisons.

Let `P = 2147483647`. A uniform 256-bit answer reduced modulo a positive
integer n has maximum point mass at most `(floor(2^256/n)+1)/2^256`.
The two relevant moduli have quotient 256, so both caps are `257/2^256`.
They nevertheless describe different samplers and different codomains.

| Challenge | Modulus and output | Bad-set cardinality cap |
|---|---|---:|
| gamma | `P^8-1`, ranked into nonzero E | 336869026622539 |
| kappa | `P^8`, ranked into E | 600 |
| first fold | `P^8`, ranked into E | 9396508281846 |
| second fold | `P^8`, ranked into E | 9396508281846 |

The gamma model matches the intended shape of
`crates/aspis-r1-cost-probe/src/sampler.rs::gamma_sample`: reduce modulo
`P^8-1`, add one, then decode the field rank. It does not replace zero after
an ordinary modulo-`P^8` draw. The ordinary sampler is used for the other
three challenges. Explicit equivalences from answer bytes to `Fin (2^256)`
and from ranks to the relevant field output remain parameters; this file
does not prove their Rust correspondence.

For fixed preceding algebraic data, the four theorems bound the probability
of membership in the corresponding bad set. The two fold statements retain
the degree-at-most-six premise for the received round polynomial. A separate
closed scalar calculation proves that the sum of the four caps is below
`2^-199`. This scalar sum is not a theorem about an adaptive protocol run.
The data must first be shown fixed before the respective answer, then the
round bounds must be composed through the actual transcript and verifier.
The q22 and semantic terms still dominate the proposed full ledger.

Root review corrected an earlier successful draft that used the ordinary
sampler for gamma. Its proof was about that different model and cannot be
used for the intended gamma source. Attempt `d` is retained as superseded;
`f` is the final corrected target. Historical attempt receipts and logs
are retained, but exact source snapshots for attempts `a` through `e` were
not found. The final source snapshot is present and hash-matched.

`R1OpeningSamplerBound-opening-sampler-bound-f` passed on the NUC in 1.66 s
at 3,161,512 KiB peak RSS with zero swap, under the existing 4G/6G/0 scope.
The [combined evidence](evidence/lean-privacy-opening-20261014/README.md)
includes its six axiom reports and the fourteen-report import checkpoint.
