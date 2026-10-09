# R661 TwoSwap mask addition

Status: focused green evidence only. Promotion is held for the dependent R662
full-index composition. Nothing has been staged, committed, or pushed.

`R661TwoSwapMaskAddition.lean` proves exact field-model linearity of the
actual TwoSwap `fullMask` for arbitrary `Nat → F` input. Adding the flattened
R660 residual combination preserves all 271 selected sparse coordinates and,
therefore, every sparse terminal pairing with arbitrary weights. It also
preserves the inactive balance and any point functional whose correction is
explicitly zero.

The result does not prove native Rust execution, a shared-oracle law, raw or
authentication preservation, complete published-view preservation, or a
privacy/security conclusion. Its supporting H1 inventory is read-only and
non-proof: the full 214-active-row H1 kernel remains unproved.

Final target: `AspisV8R19/R661TwoSwapMaskAddition.lean`. The final run
`1791113992344619000` used source revision
`521944c51acb36a94ed5bd676b5af2fd8611c4bc`, source SHA-256
`e9d795f352e6c2342fa1d6921d7797f5a0690466992b1313d6549ef38ef5e148`, and
exited 0 in 1.42 seconds, with GNU-time peak RSS 3,303,384 KiB and swap 0.
All six complete `#print axioms` reports contain only `propext`,
`Classical.choice`, and `Quot.sound`.

The earlier focused attempt `1791113946437043000` is retained verbatim. It
exited 1 after 1.45 seconds at 3,291,084 KiB RSS, swap 0; its source has SHA-256
`1e6812026f9382197768bbb5773893ce09a8979b692d56b93a065e5b03d6e054` and its
axiom output contains `sorryAx`. It is not proof evidence.

Direct formal pins are R660
`a69264542fcf89116d0bd9792132e2ee611842e0650f54d8082432585203024c` and R574
`ccd4bab7796221eada233ba04de5c83a09e8565f69009d24115d7a822abc4b16`.
