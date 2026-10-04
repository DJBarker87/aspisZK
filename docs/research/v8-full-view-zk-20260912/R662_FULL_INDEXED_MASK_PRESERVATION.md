# R662 full indexed mask preservation

Status: both focused targets compiled successfully in the pinned Lean 4.32 cached workspace. Exact verified sources and complete evidence are promoted together.

R662 connects R660's full `Index 256` incoming G representation to the
TwoSwap mask model. `flattenFull` converts the entire 1024-coordinate indexed
channel, and the theorem shows that adding R660's low residual extension adds
exactly the existing R645 actual mask. No low-support condition is imposed on
the incoming G channel.

Together with R661, this proves that the correction preserves all 271 actual
sparse coordinates, inactive balance, and each point functional for which the
correction is explicitly zero. R661 also lifts the coordinate result to every
sparse weighted pairing. These are exact TwoSwap field-model statements.

This does not prove native implementation execution, raw/authentication
preservation, a complete published-view simulation, a shared-oracle law, or
privacy or security. The full 214-active-row H1 kernel remains unproved; the
included R661 H1 note is read-only support and not a theorem dependency.

R662 final run `1791114103493495000` compiled
`AspisV8R19/R662FullIndexedMaskPreservation.lean` from revision
`521944c51acb36a94ed5bd676b5af2fd8611c4bc`, SHA-256
`52c7edf157b10719e89085833d942ec10ad2a5bc98c6f889e1dc8c5699e35963`, exit 0,
wall 1.33 seconds, GNU-time peak RSS 3,299,148 KiB, swap 0. Its five complete
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`
(the first has only `propext` and `Quot.sound`).

R661 final run `1791113992344619000` and its failed precursor
`1791113946437043000` are retained under `attempts/r661`. R661's final source
SHA-256 is `e9d795f352e6c2342fa1d6921d7797f5a0690466992b1313d6549ef38ef5e148`;
the failed source SHA is
`1e6812026f9382197768bbb5773893ce09a8979b692d56b93a065e5b03d6e054`.
Direct R661 source pins are R660
`a69264542fcf89116d0bd9792132e2ee611842e0650f54d8082432585203024c` and R574
`ccd4bab7796221eada233ba04de5c83a09e8565f69009d24115d7a822abc4b16`.

First remaining proposition: construct actual C1/H1/core G channels for every legal same-public witness difference with the retained full-support fold, relation and active-coordinate conditions, then prove the actual shared-oracle root/determinant laws and entire published-view simulator. These mask identities do not discharge that proposition.

Verifier source, all security parameters, authentication, canonical checks, negative examples and CU 999,790 / 999,532 are unchanged. No unchanged proof/regression or CU benchmark was repeated.
